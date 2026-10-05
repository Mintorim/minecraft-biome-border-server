// biome_finder_server.c
//
// File last edited for 26.3
//
// Samples Minecraft biome statistics across consecutive world seeds and
// serves live results over a local HTTP page.
//
//   Border mode: tallies the biomes neighbouring a chosen target biome.
//   Origin mode: tallies the biome at block (0,0) for each seed.
//
// Requires Linux/macOS and Cubiomes (headers plus a built libcubiomes.a).
//
// Released under CC0 1.0 Universal (public domain).
// Portions of this code were created with AI assistance.
//
// Local use only: the HTTP interface binds to 127.0.0.1 and has no authentication.
//
// Build:
//   clang -O3 -mcpu=native -flto -o biome_origin biome_finder_server.c libcubiomes.a -lm -lpthread   (Apple Silicon)
//   clang -O3 -march=native -flto -o biome_origin biome_finder_server.c libcubiomes.a -lm -lpthread  (Intel / Linux)
// Run:  ./border_server then open http://localhost:8787

#include "generator.h"
#include "util.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <math.h>
#include <inttypes.h>
#include <pthread.h>
#include <signal.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

// ======================= CONFIGURATION =====================================
#define MC_VERSION       MC_NEWEST
#define AREA_SIZE        512     // cells per side of the sampled grid (one cell = 4 blocks)
#define HTTP_PORT        8787
#define MAX_ID           512     // upper bound on biome ids
#define MAX_THREADS_CAP  64      // hard ceiling on worker threads

// Climate sampling needs the target biome to appear somewhere in the
// AREA_SIZE grid. If it doesn't, one cheaper scan over a wider, coarser grid
// is tried (the same technique cubiomes uses for scale > 4 queries). The cost
// is CLIMATE_FALLBACK_CELLS^2 samples per seed, independent of AREA_SIZE.
#define CLIMATE_FALLBACK_CELLS  128   // side length (cells) of the fallback grid
#define CLIMATE_FALLBACK_SCALE  64    // blocks per fallback cell; must be a multiple of 4
// =============================================================================

// Sample heights are in ordinary block Y-coordinates (as shown on the F3
// screen); blockYToQuart-style conversion is done with floorDiv4() because
// cubiomes takes quart-scale (4-block) coordinates.
#define MIN_Y_BLOCK     -64
#define MAX_Y_BLOCK      319
#define DEFAULT_Y_BLOCK  252   // above all terrain and caves

// Floor division by 4. C's "/" truncates toward zero, which is wrong for
// negative Y (e.g. -63/4 gives -15, but blocks -64..-61 belong to quart -16).
static int floorDiv4(int a) {
    int q = a / 4;
    int r = a % 4;
    if (r < 0) q--;
    return q;
}

// MODE_BORDER: counts the biomes bordering a target biome. With the
//              "generic surface" keyword the target is, per seed, whatever
//              biome sits at (0,0), and all seeds are blended into one total.
// MODE_ORIGIN: counts the biome at (0,0) once per seed (much cheaper).
typedef enum { MODE_BORDER = 0, MODE_ORIGIN = 1 } SampleMode;
#define GENERIC_SURFACE_KEYWORD "generic surface"

// Accepts "generic surface" or "generic_surface" (case-insensitive), since
// every real biome name uses underscores.
static int isGenericSurfaceKeyword(const char *name) {
    if (!name) return 0;
    char buf[64];
    size_t i = 0;
    for (; name[i] && i < sizeof(buf) - 1; i++)
        buf[i] = (name[i] == '_') ? ' ' : name[i];
    buf[i] = 0;
    return strcasecmp(buf, GENERIC_SURFACE_KEYWORD) == 0;
}

// How the sample height is chosen:
//   YMODE_ADAPTIVE - per column, sample at the estimated terrain surface
//                    (cubiomes' mapApproxHeight()). Cannot find cave biomes.
//   YMODE_FIXED    - one Y for the whole run. Useful for probing a specific
//                    height, e.g. Y=0 for cave biomes.
typedef enum { YMODE_ADAPTIVE = 0, YMODE_FIXED = 1 } YMode;

// Maximum distinct neighbouring biomes stored per history snapshot.
#define HISTORY_MAX_NONZERO 96
// Snapshots kept in memory before older ones are thinned out.
#define HISTORY_CAP 4000
// Stability check: look back at least this many seeds (or 5% of the run).
#define STABLE_LOOKBACK_MIN 200
#define STABLE_THRESHOLD_PCT 0.05

// ---------------------------------------------------------------- biome table
typedef struct { int id; const char *name; } BiomeEntry;
static BiomeEntry g_biomeTable[MAX_ID];
static int g_biomeCount = 0;

const char *overworld_biomes[] = {
    "badlands", "bamboo_jungle", "beach", "birch_forest", "cherry_grove",
    "cold_ocean", "dappled_forest", "dark_forest", "deep_cold_ocean",
    "deep_dark", "deep_frozen_ocean", "deep_lukewarm_ocean", "deep_ocean",
    "desert", "dripstone_caves", "eroded_badlands", "flower_forest",
    "forest", "frozen_ocean", "frozen_peaks", "frozen_river", "grove",
    "ice_spikes", "jagged_peaks", "jungle", "lukewarm_ocean", "lush_caves",
    "mangrove_swamp", "meadow", "mushroom_fields", "ocean",
    "old_growth_birch_forest", "old_growth_pine_taiga",
    "old_growth_spruce_taiga", "pale_garden", "plains", "river", "savanna",
    "savanna_plateau", "snowy_beach", "snowy_plains", "snowy_slopes",
    "snowy_taiga", "sparse_jungle", "stony_peaks", "stony_shore",
    "sulfur_caves", "sunflower_plains", "swamp", "taiga", "warm_ocean",
    "windswept_forest", "windswept_gravelly_hills", "windswept_hills",
    "windswept_savanna", "wooded_badlands"
};
const int NUM_BIOMES = sizeof(overworld_biomes) / sizeof(overworld_biomes[0]);

static int is_overworld_biome(const char *name) {
    if (!name) return 0;
    for (int i = 0; i < NUM_BIOMES; i++) {
        if (strcasecmp(name, overworld_biomes[i]) == 0) return 1;
    }
    return 0;
}

// Fills the table with the cubiomes biome ids whose names are in the overworld list.
static void buildBiomeTable(void) {
    g_biomeCount = 0;
    for (int id = 0; id < MAX_ID; id++) {
        const char *name = biome2str(MC_VERSION, id);
        if (name && is_overworld_biome(name)) {
            g_biomeTable[g_biomeCount].id = id;
            g_biomeTable[g_biomeCount].name = name;
            g_biomeCount++;
        }
    }
}

static int resolveBiomeName(const char *name) {
    for (int i = 0; i < g_biomeCount; i++)
        if (strcasecmp(name, g_biomeTable[i].name) == 0)
            return g_biomeTable[i].id;
    return -1;
}

// ---------------------------------------------------------------- history (for the graph)
typedef struct {
    long seedsDone;
    long totalBorder;
    int  n;                          // number of populated slots below
    int  ids[HISTORY_MAX_NONZERO];
    long counts[HISTORY_MAX_NONZERO];
} HistoryPoint;

static HistoryPoint g_history[HISTORY_CAP];
static int  g_historyCount = 0;
static long g_snapshotInterval = 1;  // seeds between snapshots; doubles when the history fills up
static int  g_historyEpoch = 0;      // bumped on each Start so the browser knows to clear its graph

// caller must hold g_lock
static void pushHistoryLocked(long seedsDone, long totalBorder, long *counts) {
    if (g_historyCount == HISTORY_CAP) {
        // Keep every other point and double the interval, bounding memory
        // and JSON size at the cost of coarser early history.
        int w = 0;
        for (int i = 0; i < g_historyCount; i += 2) g_history[w++] = g_history[i];
        g_historyCount = w;
        g_snapshotInterval *= 2;
    }
    HistoryPoint *hp = &g_history[g_historyCount++];
    hp->seedsDone = seedsDone;
    hp->totalBorder = totalBorder;
    hp->n = 0;
    for (int i = 0; i < MAX_ID && hp->n < HISTORY_MAX_NONZERO; i++) {
        if (counts[i] > 0) {
            hp->ids[hp->n] = i;
            hp->counts[hp->n] = counts[i];
            hp->n++;
        }
    }
}

static long historyCountForId(const HistoryPoint *hp, int id) {
    for (int i = 0; i < hp->n; i++)
        if (hp->ids[i] == id) return hp->counts[i];
    return 0;
}

// ---------------------------------------------------------------- climate classification
// Bucket boundaries for each climate parameter. Values outside the nominal
// range are clamped into the first/last bucket.
#define N_TLEVELS   5
#define N_HLEVELS   5
#define N_CLEVELS   7
#define N_ELEVELS   7
#define N_PVLEVELS  5

static const double T_BOUNDS[N_TLEVELS + 1]  = {-1.0, -0.45, -0.15, 0.2, 0.55, 1.0};
static const double H_BOUNDS[N_HLEVELS + 1]  = {-1.0, -0.35, -0.1, 0.1, 0.3, 1.0};
static const double C_BOUNDS[N_CLEVELS + 1]  = {-1.2, -1.05, -0.455, -0.19, -0.11, 0.03, 0.3, 1.0};
static const double E_BOUNDS[N_ELEVELS + 1]  = {-1.0, -0.78, -0.375, -0.2225, 0.05, 0.45, 0.55, 1.0};
static const double PV_BOUNDS[N_PVLEVELS + 1] = {-1.0, -0.85, -0.2, 0.2, 0.7, 1.0};

static const char *C_NAMES[N_CLEVELS] = {
    "Mushroom fields", "Deep ocean", "Ocean", "Coast",
    "Near-inland", "Mid-inland", "Far-inland"
};
static const char *PV_NAMES[N_PVLEVELS] = {
    "Valleys", "Low", "Mid", "High", "Peaks"
};

// Returns the bucket index in [0, n-1] that value falls into.
static int classifyLevel(double value, const double *bounds, int n) {
    if (value < bounds[0]) return 0;
    for (int i = 0; i < n; i++)
        if (value < bounds[i + 1]) return i;
    return n - 1;
}

// ---------------------------------------------------------------- shared state
// All of the following is protected by g_lock.
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static volatile int g_running = 0;           // at least one worker is sampling
static volatile int g_workerShouldStop = 0;
static pthread_t g_workerThreads[MAX_THREADS_CAP];
static int g_numWorkers = 0;
static int g_workersAlive = 0;

static SampleMode g_mode = MODE_BORDER;
static int  g_generic = 0;           // MODE_BORDER only: 1 = "generic surface"
static YMode g_yMode = YMODE_FIXED;
static int  g_yBlock = DEFAULT_Y_BLOCK;  // used only when g_yMode == YMODE_FIXED
static int  g_yQuart = DEFAULT_Y_BLOCK / 4;

static int  g_targetId = -1;
static char g_targetName[64] = "";
static char g_checkpointPath[300] = "";
static long g_nextSeed = 0;          // next seed a worker will claim
static long g_seedsDone = 0;         // seeds sampled so far for this identity
static long g_totalBorder = 0;       // border-edge (or origin) samples so far
static long g_counts[MAX_ID];

// Climate statistics: at most one sample per seed, taken inside the target
// biome. g_climateSamples is the denominator for the percentages and is
// <= g_seedsDone, since a seed only contributes if the target was found.
static long g_climateSamples = 0;
static long g_tCounts[N_TLEVELS];
static long g_hCounts[N_HLEVELS];
static long g_cCounts[N_CLEVELS];
static long g_eCounts[N_ELEVELS];
static long g_pvCounts[N_PVLEVELS];
static long g_wNegCount = 0;   // weirdness < 0 (W-)
static long g_wPosCount = 0;   // weirdness >= 0 (W+)

// caller must hold g_lock
static void resetClimateStatsLocked(void) {
    g_climateSamples = 0;
    memset(g_tCounts, 0, sizeof(g_tCounts));
    memset(g_hCounts, 0, sizeof(g_hCounts));
    memset(g_cCounts, 0, sizeof(g_cCounts));
    memset(g_eCounts, 0, sizeof(g_eCounts));
    memset(g_pvCounts, 0, sizeof(g_pvCounts));
    g_wNegCount = 0;
    g_wPosCount = 0;
}

// ---------------------------------------------------------------- checkpoints
// Builds the checkpoint filename for a run identity. Statistics gathered at
// different heights or in different modes are different measurements, so
// each gets its own file.
static void checkpointPath(SampleMode mode, int generic, const char *biomeName,
                            YMode yMode, int yBlock, char *out, size_t outlen) {
    char ySuffix[24] = "";
    if (yMode == YMODE_ADAPTIVE) snprintf(ySuffix, sizeof(ySuffix), "_adaptivesurface");
    else if (yBlock != DEFAULT_Y_BLOCK) snprintf(ySuffix, sizeof(ySuffix), "_y%d", yBlock);

    if (mode == MODE_ORIGIN)
        snprintf(out, outlen, "border_state_origin%s.txt", ySuffix);
    else if (generic)
        snprintf(out, outlen, "border_state_generic_surface%s.txt", ySuffix);
    else
        snprintf(out, outlen, "border_state_%s%s.txt", biomeName, ySuffix);
}

// caller must hold g_lock
static void saveCheckpointLocked(void) {
    if (g_mode == MODE_BORDER && !g_generic && g_targetId < 0) return;
    if (!g_checkpointPath[0]) return;
    char tmpPath[sizeof(g_checkpointPath) + 8];
    snprintf(tmpPath, sizeof(tmpPath), "%s.tmp", g_checkpointPath);
    FILE *f = fopen(tmpPath, "w");
    if (!f) return;
    fprintf(f, "targetid %d\n", g_targetId);
    fprintf(f, "targetname %s\n", g_targetName);
    fprintf(f, "nextseed %ld\n", g_nextSeed);
    fprintf(f, "seedsdone %ld\n", g_seedsDone);
    fprintf(f, "totalborder %ld\n", g_totalBorder);
    for (int i = 0; i < MAX_ID; i++)
        if (g_counts[i] > 0)
            fprintf(f, "count %d %ld\n", i, g_counts[i]);
    fprintf(f, "climatesamples %ld\n", g_climateSamples);
    for (int i = 0; i < N_TLEVELS; i++)  fprintf(f, "tcount %d %ld\n", i, g_tCounts[i]);
    for (int i = 0; i < N_HLEVELS; i++)  fprintf(f, "hcount %d %ld\n", i, g_hCounts[i]);
    for (int i = 0; i < N_CLEVELS; i++)  fprintf(f, "ccount %d %ld\n", i, g_cCounts[i]);
    for (int i = 0; i < N_ELEVELS; i++)  fprintf(f, "ecount %d %ld\n", i, g_eCounts[i]);
    for (int i = 0; i < N_PVLEVELS; i++) fprintf(f, "pvcount %d %ld\n", i, g_pvCounts[i]);
    fprintf(f, "wneg %ld\n", g_wNegCount);
    fprintf(f, "wpos %ld\n", g_wPosCount);
    if (fflush(f) != 0 || fclose(f) != 0) {
        remove(tmpPath);
        return;
    }
    if (rename(tmpPath, g_checkpointPath) != 0)
        remove(tmpPath);
}

// Loads a checkpoint into the globals. Returns 1 if the file existed.
// caller must hold g_lock
static int loadCheckpointLocked(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) return 0;
    memset(g_counts, 0, sizeof(g_counts));
    resetClimateStatsLocked();
    g_nextSeed = 0; g_seedsDone = 0; g_totalBorder = 0;
    char line[256];
    while (fgets(line, sizeof(line), f)) {
        long val; int id;
        if (sscanf(line, "nextseed %ld", &val) == 1) g_nextSeed = val;
        else if (sscanf(line, "seedsdone %ld", &val) == 1 && val >= 0) g_seedsDone = val;
        else if (sscanf(line, "totalborder %ld", &val) == 1 && val >= 0) g_totalBorder = val;
        else if (sscanf(line, "count %d %ld", &id, &val) == 2 && id >= 0 && id < MAX_ID && val >= 0)
            g_counts[id] = val;
        else if (sscanf(line, "climatesamples %ld", &val) == 1 && val >= 0) g_climateSamples = val;
        else if (sscanf(line, "tcount %d %ld", &id, &val) == 2 && id >= 0 && id < N_TLEVELS)
            g_tCounts[id] = val;
        else if (sscanf(line, "hcount %d %ld", &id, &val) == 2 && id >= 0 && id < N_HLEVELS)
            g_hCounts[id] = val;
        else if (sscanf(line, "ccount %d %ld", &id, &val) == 2 && id >= 0 && id < N_CLEVELS)
            g_cCounts[id] = val;
        else if (sscanf(line, "ecount %d %ld", &id, &val) == 2 && id >= 0 && id < N_ELEVELS)
            g_eCounts[id] = val;
        else if (sscanf(line, "pvcount %d %ld", &id, &val) == 2 && id >= 0 && id < N_PVLEVELS)
            g_pvCounts[id] = val;
        else if (sscanf(line, "wneg %ld", &val) == 1 && val >= 0) g_wNegCount = val;
        else if (sscanf(line, "wpos %ld", &val) == 1 && val >= 0) g_wPosCount = val;
    }
    fclose(f);
    return 1;
}

// ---------------------------------------------------------------- worker
// Reads the climate noise at one point (qx, qz in quart coordinates) and
// returns its T/H/C/E/PV/W level buckets.
static void classifyClimateSample(Generator *gen, int qx, int yQuart, int qz,
                                   int *lvlT, int *lvlH, int *lvlC, int *lvlE, int *lvlPV, int *wNeg) {
    int64_t np[NP_MAX];
    sampleBiomeNoise(&gen->bn, np, qx, yQuart, qz, NULL, 0);
    double t = np[NP_TEMPERATURE] / 10000.0;
    double h = np[NP_HUMIDITY] / 10000.0;
    double c = np[NP_CONTINENTALNESS] / 10000.0;
    double e = np[NP_EROSION] / 10000.0;
    double w = np[NP_WEIRDNESS] / 10000.0;
    double pv = 1.0 - fabs(3.0 * fabs(w) - 2.0);
    *lvlT = classifyLevel(t, T_BOUNDS, N_TLEVELS);
    *lvlH = classifyLevel(h, H_BOUNDS, N_HLEVELS);
    *lvlC = classifyLevel(c, C_BOUNDS, N_CLEVELS);
    *lvlE = classifyLevel(e, E_BOUNDS, N_ELEVELS);
    *lvlPV = classifyLevel(pv, PV_BOUNDS, N_PVLEVELS);
    *wNeg = (w < 0.0);
}

// Generates a biome grid sampled at each column's estimated terrain surface
// (mapApproxHeight()), so one search covers oceans, plains and mountains
// without a single fixed Y missing some of them.
//
// yQuartOut, if non-null, receives each column's sample height (quart
// coordinates) for reuse by climate sampling. heightScratch must hold
// r.sx * r.sz floats.
static int genBiomesAdaptiveSurface(Generator *gen, int *ids, int *yQuartOut,
                                     float *heightScratch, Range r) {
    int sx = r.sx, sz = r.sz;
    if (mapApproxHeight(heightScratch, NULL, gen, NULL, r.x, r.z, sx, sz) != 0)
        return -1;
    for (int z = 0; z < sz; z++) {
        for (int x = 0; x < sx; x++) {
            int idx = z * sx + x;
            int yQuart = floorDiv4((int) lroundf(heightScratch[idx]));
            if (yQuartOut) yQuartOut[idx] = yQuart;
            int64_t np[NP_MAX];
            ids[idx] = sampleBiomeNoise(&gen->bn, np, r.x + x, yQuart, r.z + z, NULL, 0);
        }
    }
    return 0;
}

// Each worker owns its Generator and buffers; threads share only the
// globals above, and only while holding g_lock.
static void *workerFn(void *arg) {
    (void) arg;

    Generator gen;
    setupGenerator(&gen, MC_VERSION, 0);

    // Mode, generic flag and Y are fixed for the whole run, so read them once.
    pthread_mutex_lock(&g_lock);
    SampleMode mode = g_mode;
    int generic = g_generic;
    int adaptive = (g_yMode == YMODE_ADAPTIVE);
    int yQuart = g_yQuart;  // only meaningful when !adaptive
    pthread_mutex_unlock(&g_lock);

    Range r = {4, -AREA_SIZE / 2, -AREA_SIZE / 2, AREA_SIZE, AREA_SIZE, yQuart, 1};
    int *ids = (mode == MODE_BORDER) ? allocCache(&gen, r) : NULL;
    long localCounts[MAX_ID];
    int centerIdx = (AREA_SIZE / 2) * r.sx + (AREA_SIZE / 2);  // index of (0,0) in ids[]

    // Per-column sample heights for the main grid (adaptive mode only).
    int   *yQuartGrid = (mode == MODE_BORDER && adaptive) ? malloc(sizeof(int) * r.sx * r.sz) : NULL;
    float *heightBuf  = (mode == MODE_BORDER && adaptive) ? malloc(sizeof(float) * r.sx * r.sz) : NULL;

    // Wide, coarse fallback grid for climate sampling (border mode only).
    Range rf = {CLIMATE_FALLBACK_SCALE,
                -CLIMATE_FALLBACK_CELLS / 2, -CLIMATE_FALLBACK_CELLS / 2,
                CLIMATE_FALLBACK_CELLS, CLIMATE_FALLBACK_CELLS, yQuart, 1};
    int *fids = (mode == MODE_BORDER) ? allocCache(&gen, rf) : NULL;
    int   *fYQuartGrid = (mode == MODE_BORDER && adaptive) ? malloc(sizeof(int) * rf.sx * rf.sz) : NULL;
    float *fHeightBuf  = (mode == MODE_BORDER && adaptive) ? malloc(sizeof(float) * rf.sx * rf.sz) : NULL;

    for (;;) {
        pthread_mutex_lock(&g_lock);
        if (g_workerShouldStop) { pthread_mutex_unlock(&g_lock); break; }
        long seed = g_nextSeed++;
        int fixedTarget = g_targetId;
        pthread_mutex_unlock(&g_lock);

        applySeed(&gen, DIM_OVERWORLD, (uint64_t) seed);

        if (mode == MODE_ORIGIN) {
            int originYQuart = yQuart;
            if (adaptive) {
                float h;
                if (mapApproxHeight(&h, NULL, &gen, NULL, 0, 0, 1, 1) == 0)
                    originYQuart = floorDiv4((int) lroundf(h));
            }
            int originBiome = getBiomeAt(&gen, 4, 0, originYQuart, 0);
            if (originBiome >= 0 && originBiome < MAX_ID) {
                int lvlT = 0, lvlH = 0, lvlC = 0, lvlE = 0, lvlPV = 0, wNeg = 0;
                classifyClimateSample(&gen, 0, originYQuart, 0,
                                       &lvlT, &lvlH, &lvlC, &lvlE, &lvlPV, &wNeg);

                pthread_mutex_lock(&g_lock);
                g_counts[originBiome]++;
                g_totalBorder++;   // equals g_seedsDone in origin mode
                g_seedsDone++;

                g_climateSamples++;
                g_tCounts[lvlT]++;
                g_hCounts[lvlH]++;
                g_cCounts[lvlC]++;
                g_eCounts[lvlE]++;
                g_pvCounts[lvlPV]++;
                if (wNeg) g_wNegCount++; else g_wPosCount++;

                if (g_seedsDone % g_snapshotInterval == 0)
                    pushHistoryLocked(g_seedsDone, g_totalBorder, g_counts);
                if (g_seedsDone % 100 == 0)
                    saveCheckpointLocked();
                pthread_mutex_unlock(&g_lock);
            }
            continue;
        }

        int genOk = 0;
        if (ids) {
            genOk = adaptive
                ? (genBiomesAdaptiveSurface(&gen, ids, yQuartGrid, heightBuf, r) == 0)
                : (genBiomes(&gen, ids, r) == 0);
        }

        if (genOk) {
            // In generic-surface mode the target is the biome at the origin,
            // i.e. the centre cell of the grid just generated.
            int target = generic ? ids[centerIdx] : fixedTarget;

            memset(localCounts, 0, sizeof(localCounts));
            long localTotal = 0;
            int sx = r.sx, sz = r.sz;

            // Count each horizontally or vertically adjacent pair where
            // exactly one cell is the target, tallying the other biome.
            for (int z = 0; z < sz; z++)
                for (int x = 0; x < sx - 1; x++) {
                    int a = ids[z * sx + x], b = ids[z * sx + x + 1];
                    if (a == target && b != target && b >= 0 && b < MAX_ID) { localCounts[b]++; localTotal++; }
                    else if (b == target && a != target && a >= 0 && a < MAX_ID) { localCounts[a]++; localTotal++; }
                }
            for (int z = 0; z < sz - 1; z++)
                for (int x = 0; x < sx; x++) {
                    int a = ids[z * sx + x], b = ids[(z + 1) * sx + x];
                    if (a == target && b != target && b >= 0 && b < MAX_ID) { localCounts[b]++; localTotal++; }
                    else if (b == target && a != target && a >= 0 && a < MAX_ID) { localCounts[a]++; localTotal++; }
                }

            // Climate sampling: one noise sample per seed, taken at the first
            // cell found that is the target biome (not a border cell).
            int gotClimate = 0;
            int lvlT = 0, lvlH = 0, lvlC = 0, lvlE = 0, lvlPV = 0, wNeg = 0;
            for (int z = 0; z < sz && !gotClimate; z++) {
                for (int x = 0; x < sx; x++) {
                    if (ids[z * sx + x] != target) continue;
                    int thisYQuart = adaptive ? yQuartGrid[z * sx + x] : yQuart;
                    classifyClimateSample(&gen, r.x + x, thisYQuart, r.z + z,
                                           &lvlT, &lvlH, &lvlC, &lvlE, &lvlPV, &wNeg);
                    gotClimate = 1;
                    break;
                }
            }

            // Nothing in the dense grid: try the wide, coarse grid. Coarse
            // queries are approximate, so each hit is re-checked at scale 4
            // and skipped if it doesn't hold up.
            if (!gotClimate && fids) {
                int fOk = adaptive
                    ? (genBiomesAdaptiveSurface(&gen, fids, fYQuartGrid, fHeightBuf, rf) == 0)
                    : (genBiomes(&gen, fids, rf) == 0);
                if (fOk) {
                    for (int fz = 0; fz < rf.sz && !gotClimate; fz++) {
                        for (int fx = 0; fx < rf.sx; fx++) {
                            if (fids[fz * rf.sx + fx] != target) continue;
                            int qx = (rf.x + fx) * (CLIMATE_FALLBACK_SCALE / 4);
                            int qz = (rf.z + fz) * (CLIMATE_FALLBACK_SCALE / 4);
                            int fYQuart = adaptive ? fYQuartGrid[fz * rf.sx + fx] : yQuart;
                            if (getBiomeAt(&gen, 4, qx, fYQuart, qz) != target) continue;
                            classifyClimateSample(&gen, qx, fYQuart, qz,
                                                   &lvlT, &lvlH, &lvlC, &lvlE, &lvlPV, &wNeg);
                            gotClimate = 1;
                            break;
                        }
                    }
                }
            }

            pthread_mutex_lock(&g_lock);
            for (int i = 0; i < MAX_ID; i++) g_counts[i] += localCounts[i];
            g_totalBorder += localTotal;
            g_seedsDone++;
            if (gotClimate) {
                g_climateSamples++;
                g_tCounts[lvlT]++;
                g_hCounts[lvlH]++;
                g_cCounts[lvlC]++;
                g_eCounts[lvlE]++;
                g_pvCounts[lvlPV]++;
                if (wNeg) g_wNegCount++; else g_wPosCount++;
            }
            if (g_seedsDone % g_snapshotInterval == 0)
                pushHistoryLocked(g_seedsDone, g_totalBorder, g_counts);
            if (g_seedsDone % 100 == 0)
                saveCheckpointLocked();
            pthread_mutex_unlock(&g_lock);
        }
    }

    free(ids);
    free(fids);
    free(yQuartGrid);
    free(heightBuf);
    free(fYQuartGrid);
    free(fHeightBuf);

    pthread_mutex_lock(&g_lock);
    g_workersAlive--;
    if (g_workersAlive == 0) {
        // Last worker out: final snapshot and checkpoint.
        pushHistoryLocked(g_seedsDone, g_totalBorder, g_counts);
        saveCheckpointLocked();
        g_running = 0;
    }
    pthread_mutex_unlock(&g_lock);
    return NULL;
}

static long detectCoreCount(void) {
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    if (n < 1) n = 1;
    if (n > MAX_THREADS_CAP) n = MAX_THREADS_CAP;
    return n;
}

// Starts sampling. seedOverride < 0 means continue from the checkpoint.
// biomeName is ignored in MODE_ORIGIN. Returns NULL on success, otherwise a
// static error string.
static const char *startSampling(SampleMode mode, const char *biomeName, long seedOverride,
                                  int numThreads, long snapshotEvery, YMode yMode, int yBlock) {
    if (numThreads < 1) numThreads = 1;
    if (numThreads > MAX_THREADS_CAP) numThreads = MAX_THREADS_CAP;
    if (snapshotEvery < 1) snapshotEvery = 1;
    if (yBlock < MIN_Y_BLOCK) yBlock = MIN_Y_BLOCK;
    if (yBlock > MAX_Y_BLOCK) yBlock = MAX_Y_BLOCK;

    pthread_mutex_lock(&g_lock);
    if (g_running) {
        pthread_mutex_unlock(&g_lock);
        return "Already running - stop it first.";
    }

    int generic = 0;
    int id = -1;
    char resolvedName[64] = "";

    if (mode == MODE_BORDER) {
        if (!biomeName || !biomeName[0]) {
            pthread_mutex_unlock(&g_lock);
            return "Type a biome name (or \"generic surface\") first.";
        }
        if (isGenericSurfaceKeyword(biomeName)) {
            generic = 1;
            strncpy(resolvedName, GENERIC_SURFACE_KEYWORD, sizeof(resolvedName) - 1);
        } else {
            id = resolveBiomeName(biomeName);
            if (id < 0) {
                pthread_mutex_unlock(&g_lock);
                return "Unknown biome name.";
            }
            // Use the canonical spelling so differently-cased input maps to
            // the same name and checkpoint.
            const char *canonical = biome2str(MC_VERSION, id);
            strncpy(resolvedName, canonical ? canonical : biomeName, sizeof(resolvedName) - 1);
        }
    } else {
        strncpy(resolvedName, "(biome at origin)", sizeof(resolvedName) - 1);
    }

    // If this run measures something different from what is loaded, switch
    // identity and load its checkpoint (or start fresh).
    int identityChanged = (mode != g_mode) || (generic != g_generic) ||
                           (id != g_targetId) || (yMode != g_yMode) ||
                           (yMode == YMODE_FIXED && yBlock != g_yBlock);
    if (identityChanged) {
        g_mode = mode;
        g_generic = generic;
        g_targetId = id;
        g_yMode = yMode;
        g_yBlock = yBlock;
        g_yQuart = floorDiv4(yBlock);
        strncpy(g_targetName, resolvedName, sizeof(g_targetName) - 1);
        g_targetName[sizeof(g_targetName) - 1] = 0;

        checkpointPath(mode, generic, resolvedName, yMode, yBlock,
                        g_checkpointPath, sizeof(g_checkpointPath));
        if (!loadCheckpointLocked(g_checkpointPath)) {
            memset(g_counts, 0, sizeof(g_counts));
            resetClimateStatsLocked();
            g_nextSeed = 0; g_seedsDone = 0; g_totalBorder = 0;
        }
    }
    if (seedOverride >= 0) g_nextSeed = seedOverride;

    // Fresh graph for this run; running totals are kept.
    g_historyCount = 0;
    g_snapshotInterval = snapshotEvery;
    g_historyEpoch++;
    pushHistoryLocked(g_seedsDone, g_totalBorder, g_counts);

    g_workerShouldStop = 0;
    g_numWorkers = 0;
    g_workersAlive = 0;
    g_running = 1;

    // Hold the mutex while creating workers so none can touch
    // g_workersAlive before the final thread count is known.
    int created = 0;
    for (; created < numThreads; created++) {
        if (pthread_create(&g_workerThreads[created], NULL, workerFn, NULL) != 0)
            break;
    }

    g_numWorkers = created;
    g_workersAlive = created;
    if (created != numThreads) {
        g_workerShouldStop = 1;
        if (created == 0) g_running = 0;
        pthread_mutex_unlock(&g_lock);
        for (int i = 0; i < created; i++)
            pthread_join(g_workerThreads[i], NULL);
        return "Could not create all worker threads.";
    }

    pthread_mutex_unlock(&g_lock);
    return NULL;
}

// Stops sampling; blocks until every worker has finished its current seed
// and the final checkpoint is saved.
static void stopSampling(void) {
    pthread_mutex_lock(&g_lock);
    if (!g_running) { pthread_mutex_unlock(&g_lock); return; }
    g_workerShouldStop = 1;
    int n = g_numWorkers;
    pthread_mutex_unlock(&g_lock);

    for (int i = 0; i < n; i++)
        pthread_join(g_workerThreads[i], NULL);
}

// ---------------------------------------------------------------- tiny HTTP server
static int writeAll(int fd, const void *data, size_t len) {
    const char *p = (const char *) data;
    while (len > 0) {
        ssize_t n = write(fd, p, len);
        if (n < 0) return 0;
        if (n == 0) return 0;
        p += n;
        len -= (size_t) n;
    }
    return 1;
}

static void sendResponse(int fd, const char *status, const char *ctype, const char *body, size_t bodyLen) {
    char header[256];
    int n = snprintf(header, sizeof(header),
        "HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n",
        status, ctype, bodyLen);
    if (n > 0 && (size_t) n < sizeof(header))
        writeAll(fd, header, (size_t) n);
    writeAll(fd, body, bodyLen);
}

static void sendText(int fd, const char *status, const char *ctype, const char *body) {
    sendResponse(fd, status, ctype, body, strlen(body));
}

// Sends a heap-allocated body, then frees it.
static void sendTextOwned(int fd, const char *status, const char *ctype, char *body) {
    sendResponse(fd, status, ctype, body, strlen(body));
    free(body);
}

static int hexNibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

// Copies the value of `key` from a query string into out, decoding %XX
// escapes and treating '+' as a space. Returns 1 if the key was found.
static int getParam(const char *query, const char *key, char *out, size_t outlen) {
    if (!query) return 0;
    size_t keylen = strlen(key);
    const char *p = query;
    while (p && *p) {
        if (strncmp(p, key, keylen) == 0 && p[keylen] == '=') {
            p += keylen + 1;
            size_t i = 0;
            while (*p && *p != '&' && i + 1 < outlen) {
                if (*p == '%' && p[1] && p[2]) {
                    int hi = hexNibble(p[1]), lo = hexNibble(p[2]);
                    if (hi >= 0 && lo >= 0) {
                        out[i++] = (char) ((hi << 4) | lo);
                        p += 3;
                        continue;
                    }
                }
                out[i++] = (*p == '+') ? ' ' : *p;
                p++;
            }
            out[i] = 0;
            return 1;
        }
        p = strchr(p, '&');
        if (p) p++;
    }
    return 0;
}

// Used by /api/start and /api/reset. Currently always returns YMODE_FIXED,
// so adaptive mode cannot be selected through the API.
static YMode parseYModeParam(const char *query) {
    char yModeBuf[16] = "";
    if (getParam(query, "ymode", yModeBuf, sizeof(yModeBuf)) && strcasecmp(yModeBuf, "fixed") == 0)
        return YMODE_FIXED;
    return YMODE_FIXED;
}

typedef struct { int id; long count; } SortEntry;
static int cmpDesc(const void *a, const void *b) {
    long ca = ((const SortEntry *) a)->count, cb = ((const SortEntry *) b)->count;
    return (cb > ca) - (cb < ca);
}

// ---------------------------------------------------------------- statistics
// z for a 95% two-sided confidence interval.
#define Z_95 1.959963985

// Wilson score interval for a binomial proportion. Unlike the normal
// approximation, it stays within [0,1] for the small proportions common here.
// p and the returned bounds are fractions (0..1), not percentages.
static void wilsonInterval(double p, double n, double *lo, double *hi) {
    if (n <= 0) { *lo = 0.0; *hi = 1.0; return; }
    double z2 = Z_95 * Z_95;
    double denom = 1.0 + z2 / n;
    double center = (p + z2 / (2.0 * n)) / denom;
    double half = (Z_95 / denom) * sqrt(p * (1.0 - p) / n + z2 / (4.0 * n * n));
    *lo = center - half; if (*lo < 0.0) *lo = 0.0;
    *hi = center + half; if (*hi > 1.0) *hi = 1.0;
}

static double wilsonHalfWidth(double p, double n) {
    if (n <= 0.0) return 0.5;
    double lo, hi;
    wilsonInterval(p, n, &lo, &hi);
    return 0.5 * (hi - lo);
}

// Estimates the sample size at which the Wilson interval half-width reaches
// targetHalfWidth, holding the current proportion p fixed. This is a
// planning estimate, not a guarantee.
static double requiredSampleSize(double p, double targetHalfWidth) {
    if (targetHalfWidth <= 0.0) return 1e15;
    double n = 1.0;
    while (n < 1e12 && wilsonHalfWidth(p, n) > targetHalfWidth) n *= 2.0;
    if (n >= 1e12) return 1e12;
    double lo = n * 0.5, hi = n;
    for (int i = 0; i < 80; i++) {
        double mid = 0.5 * (lo + hi);
        if (wilsonHalfWidth(p, mid) > targetHalfWidth) lo = mid;
        else hi = mid;
    }
    return hi;
}

static void buildBiomesJson(char *buf, size_t buflen) {
    size_t off = 0;
    off += snprintf(buf + off, buflen - off,
        "{\"suggestedThreads\":%ld,\"defaultYBlock\":%d,\"minYBlock\":%d,\"maxYBlock\":%d,\"biomes\":[",
        detectCoreCount(), DEFAULT_Y_BLOCK, MIN_Y_BLOCK, MAX_Y_BLOCK);
    for (int i = 0; i < g_biomeCount && off < buflen - 64; i++)
        off += snprintf(buf + off, buflen - off, "%s{\"id\":%d,\"name\":\"%s\"}",
                         i ? "," : "", g_biomeTable[i].id, g_biomeTable[i].name);
    off += snprintf(buf + off, buflen - off, "]}");
}

// Builds /api/status (polled once per second). Returns a heap-allocated string.
static char *buildStatusJson(void) {
    pthread_mutex_lock(&g_lock);
    int running = g_running;
    int numWorkers = g_numWorkers;
    int epoch = g_historyEpoch;
    SampleMode mode = g_mode;
    int generic = g_generic;
    YMode yMode = g_yMode;
    int yBlock = g_yBlock;
    char targetName[64]; strncpy(targetName, g_targetName, sizeof(targetName));
    long nextSeed = g_nextSeed, seedsDone = g_seedsDone, totalBorder = g_totalBorder;

    SortEntry entries[MAX_ID];
    int n = 0;
    for (int i = 0; i < MAX_ID; i++)
        if (g_counts[i] > 0) { entries[n].id = i; entries[n].count = g_counts[i]; n++; }
    qsort(entries, n, sizeof(SortEntry), cmpDesc);

    // Find the history snapshot at or before the look-back point, used to
    // compute each biome's change over the recent window.
    long lookback = seedsDone / 20; // 5%
    if (lookback < STABLE_LOOKBACK_MIN) lookback = STABLE_LOOKBACK_MIN;
    long targetSeed = seedsDone - lookback;
    const HistoryPoint *refPoint = NULL;
    if (targetSeed > 0) {
        for (int i = g_historyCount - 1; i >= 0; i--) {
            if (g_history[i].seedsDone <= targetSeed) { refPoint = &g_history[i]; break; }
        }
    }

    // Progress estimate: for each row, how many more samples (at the current
    // samples-per-seed rate) are needed for its 95% margin of error to reach
    // +/-0.05 percentage points. The worst row drives the progress bar.
    // "ready" separately requires both the observed stability flags and the
    // precision target to be met.
    double rate = seedsDone > 0 ? (double) totalBorder / (double) seedsDone : 0.0;
    double worstAdditionalSeeds = 0.0;
    int haveProgressData = (n > 0 && seedsDone >= 20 && totalBorder > 0);
    int allStable = (n > 0);
    int allPrecise = (n > 0);

    long climateSamples = g_climateSamples;
    long tCounts[N_TLEVELS];  memcpy(tCounts, g_tCounts, sizeof(tCounts));
    long hCounts[N_HLEVELS];  memcpy(hCounts, g_hCounts, sizeof(hCounts));
    long cCounts[N_CLEVELS];  memcpy(cCounts, g_cCounts, sizeof(cCounts));
    long eCounts[N_ELEVELS];  memcpy(eCounts, g_eCounts, sizeof(eCounts));
    long pvCounts[N_PVLEVELS]; memcpy(pvCounts, g_pvCounts, sizeof(pvCounts));
    long wNeg = g_wNegCount, wPos = g_wPosCount;

    size_t buflen = 8192 + (size_t) n * 280;
    char *buf = malloc(buflen);
    size_t off = 0;
    off += snprintf(buf + off, buflen - off,
        "{\"running\":%s,\"numWorkers\":%d,\"epoch\":%d,\"target\":\"%s\","
        "\"nextSeed\":%ld,\"seedsDone\":%ld,\"totalBorder\":%ld,\"results\":[",
        running ? "true" : "false", numWorkers, epoch,
        targetName[0] ? targetName : "", nextSeed, seedsDone, totalBorder);

    for (int i = 0; i < n && off < buflen - 280; i++) {
        double p = totalBorder > 0 ? (double) entries[i].count / totalBorder : 0.0;
        double pct = 100.0 * p;
        double ciLo, ciHi;
        wilsonInterval(p, (double) totalBorder, &ciLo, &ciHi);
        if ((ciHi - ciLo) * 0.5 > 0.0005) allPrecise = 0;
        const char *name = biome2str(MC_VERSION, entries[i].id);

        if (haveProgressData) {
            double neededN = requiredSampleSize(p, 0.0005); // 0.05 percentage points, as a fraction
            double additionalN = neededN - (double) totalBorder;
            if (additionalN < 0.0) additionalN = 0.0;
            double additionalSeeds = rate > 0.0 ? additionalN / rate : (additionalN > 0.0 ? 1e15 : 0.0);
            if (additionalSeeds > worstAdditionalSeeds) worstAdditionalSeeds = additionalSeeds;
        }

        if (refPoint) {
            long refCount = historyCountForId(refPoint, entries[i].id);
            double refPct = refPoint->totalBorder > 0 ? 100.0 * refCount / refPoint->totalBorder : 0.0;
            double delta = pct - refPct;
            int stable = fabs(delta) <= STABLE_THRESHOLD_PCT;
            if (!stable) allStable = 0;
            off += snprintf(buf + off, buflen - off,
                "%s{\"id\":%d,\"name\":\"%s\",\"count\":%ld,\"pct\":%.4f,\"ciLo\":%.4f,\"ciHi\":%.4f,"
                "\"delta\":%.4f,\"stable\":%s}",
                i ? "," : "", entries[i].id, name ? name : "?", entries[i].count, pct,
                ciLo * 100.0, ciHi * 100.0, delta, stable ? "true" : "false");
        } else {
            allStable = 0;
            off += snprintf(buf + off, buflen - off,
                "%s{\"id\":%d,\"name\":\"%s\",\"count\":%ld,\"pct\":%.4f,\"ciLo\":%.4f,\"ciHi\":%.4f,"
                "\"delta\":null,\"stable\":false}",
                i ? "," : "", entries[i].id, name ? name : "?", entries[i].count, pct,
                ciLo * 100.0, ciHi * 100.0);
        }
    }

    // A biome present at the look-back point but absent now also counts as a change.
    if (refPoint) {
        for (int r = 0; r < refPoint->n; r++) {
            int id = refPoint->ids[r];
            if (g_counts[id] == 0) {
                double refPct = refPoint->totalBorder > 0
                    ? 100.0 * refPoint->counts[r] / refPoint->totalBorder : 0.0;
                if (fabs(refPct) > STABLE_THRESHOLD_PCT) allStable = 0;
            }
        }
    }

    off += snprintf(buf + off, buflen - off, "],");

    if (haveProgressData) {
        double remainingSeeds = worstAdditionalSeeds;
        double totalEstimate = seedsDone + remainingSeeds;
        double fraction = totalEstimate > 0 ? seedsDone / totalEstimate : 0.0;
        if (fraction > 1.0) fraction = 1.0;
        off += snprintf(buf + off, buflen - off,
            "\"progress\":{\"fraction\":%.4f,\"remainingSeeds\":%.0f,\"ready\":%s},",
            fraction, remainingSeeds, (allStable && allPrecise) ? "true" : "false");
    } else {
        off += snprintf(buf + off, buflen - off, "\"progress\":{\"fraction\":null,\"remainingSeeds\":null,\"ready\":false},");
    }

    off += snprintf(buf + off, buflen - off,
        "\"mode\":\"%s\",\"generic\":%s,\"yMode\":\"%s\",\"yBlock\":%d,",
        mode == MODE_ORIGIN ? "origin" : "border", generic ? "true" : "false",
        yMode == YMODE_ADAPTIVE ? "adaptive" : "fixed", yBlock);

    off += snprintf(buf + off, buflen - off, "\"climateSamples\":%ld,", climateSamples);

    off += snprintf(buf + off, buflen - off, "\"temperature\":[");
    for (int i = 0; i < N_TLEVELS; i++) {
        double pct = climateSamples > 0 ? 100.0 * tCounts[i] / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off, "%s{\"level\":%d,\"count\":%ld,\"pct\":%.4f}",
                         i ? "," : "", i, tCounts[i], pct);
    }
    off += snprintf(buf + off, buflen - off, "],\"humidity\":[");
    for (int i = 0; i < N_HLEVELS; i++) {
        double pct = climateSamples > 0 ? 100.0 * hCounts[i] / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off, "%s{\"level\":%d,\"count\":%ld,\"pct\":%.4f}",
                         i ? "," : "", i, hCounts[i], pct);
    }
    off += snprintf(buf + off, buflen - off, "],\"continentalness\":[");
    for (int i = 0; i < N_CLEVELS; i++) {
        double pct = climateSamples > 0 ? 100.0 * cCounts[i] / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off, "%s{\"level\":%d,\"name\":\"%s\",\"count\":%ld,\"pct\":%.4f}",
                         i ? "," : "", i, C_NAMES[i], cCounts[i], pct);
    }
    off += snprintf(buf + off, buflen - off, "],\"erosion\":[");
    for (int i = 0; i < N_ELEVELS; i++) {
        double pct = climateSamples > 0 ? 100.0 * eCounts[i] / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off, "%s{\"level\":%d,\"count\":%ld,\"pct\":%.4f}",
                         i ? "," : "", i, eCounts[i], pct);
    }
    off += snprintf(buf + off, buflen - off, "],\"pv\":[");
    for (int i = 0; i < N_PVLEVELS; i++) {
        double pct = climateSamples > 0 ? 100.0 * pvCounts[i] / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off, "%s{\"level\":%d,\"name\":\"%s\",\"count\":%ld,\"pct\":%.4f}",
                         i ? "," : "", i, PV_NAMES[i], pvCounts[i], pct);
    }
    {
        double negPct = climateSamples > 0 ? 100.0 * wNeg / climateSamples : 0.0;
        double posPct = climateSamples > 0 ? 100.0 * wPos / climateSamples : 0.0;
        off += snprintf(buf + off, buflen - off,
            "],\"weirdness\":{\"neg\":{\"count\":%ld,\"pct\":%.4f},\"pos\":{\"count\":%ld,\"pct\":%.4f}}}",
            wNeg, negPct, wPos, posPct);
    }

    pthread_mutex_unlock(&g_lock);
    return buf;
}

// Builds /api/history?since=EPOCH:COUNT, returning only the snapshots the
// browser doesn't already have.
static char *buildHistoryJson(const char *sinceParam) {
    int sinceEpoch = -1, sinceCount = 0;
    if (sinceParam) sscanf(sinceParam, "%d:%d", &sinceEpoch, &sinceCount);

    pthread_mutex_lock(&g_lock);
    int epoch = g_historyEpoch;
    int startIdx = (sinceEpoch == epoch) ? sinceCount : 0;
    // If the history was thinned since the client's cursor, the cursor is
    // stale; resend from the beginning.
    if (startIdx > g_historyCount) startIdx = 0;
    if (startIdx < 0) startIdx = 0;
    int sendCount = g_historyCount - startIdx;

    size_t buflen = 256 + (size_t) sendCount * (HISTORY_MAX_NONZERO * 24 + 64);
    if (buflen < 1024) buflen = 1024;
    char *buf = malloc(buflen);
    size_t off = 0;
    off += snprintf(buf + off, buflen - off,
        "{\"epoch\":%d,\"count\":%d,\"interval\":%ld,\"points\":[",
        epoch, g_historyCount, g_snapshotInterval);
    for (int i = startIdx; i < g_historyCount && off < buflen - 256; i++) {
        const HistoryPoint *hp = &g_history[i];
        off += snprintf(buf + off, buflen - off, "%s{\"s\":%ld,\"t\":%ld,\"c\":{",
                         i > startIdx ? "," : "", hp->seedsDone, hp->totalBorder);
        for (int j = 0; j < hp->n; j++)
            off += snprintf(buf + off, buflen - off, "%s\"%d\":%ld", j ? "," : "", hp->ids[j], hp->counts[j]);
        off += snprintf(buf + off, buflen - off, "}}");
    }
    off += snprintf(buf + off, buflen - off, "]}");
    pthread_mutex_unlock(&g_lock);
    return buf;
}

static const char *PAGE_HTML =
"<!DOCTYPE html><html><head><meta charset='utf-8'>"
"<title>Biome Border Finder</title>"
"<style>"
":root{color-scheme:dark;"
"--bg:#1b1c1e;--panel:#242527;--panel2:#2c2d30;--border:#3a3b3e;"
"--text:#e8e8ea;--muted:#a3a4a8;--accent:#5fb3ff;--good:#4caf7d;--bad:#e0665f;}"
"*{box-sizing:border-box}"
"body{font-family:-apple-system,Helvetica,Arial,sans-serif;max-width:920px;margin:32px auto;"
"padding:0 16px;color:var(--text);background:var(--bg)}"
"h1{font-size:20px;font-weight:600}"
".row{margin:10px 0;display:flex;align-items:center;flex-wrap:wrap;gap:8px}"
"label{display:inline-block;min-width:110px;color:var(--muted)}"
"input,select{padding:7px 8px;font-size:14px;background:var(--panel2);color:var(--text);"
"border:1px solid var(--border);border-radius:6px}"
"button{padding:8px 16px;font-size:14px;margin-right:8px;cursor:pointer;"
"background:var(--panel2);color:var(--text);border:1px solid var(--border);border-radius:6px}"
"button:hover{background:#37383b}"
"button.primary{background:var(--accent);color:#0b1622;border-color:var(--accent);font-weight:600}"
"button.primary:hover{filter:brightness(1.08)}"
"#status{background:var(--panel);padding:12px;border-radius:8px;margin:16px 0;"
"white-space:pre-wrap;font-family:ui-monospace,Menlo,monospace;font-size:13px;border:1px solid var(--border)}"
"canvas{width:100%;background:var(--panel);border:1px solid var(--border);border-radius:8px;display:block}"
"#legend{display:flex;flex-wrap:wrap;gap:10px 16px;margin:10px 0;font-size:12px;color:var(--muted)}"
".swatch{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:5px;vertical-align:middle}"
"table{border-collapse:collapse;width:100%;margin-top:14px}"
"td,th{padding:6px 8px;border-bottom:1px solid var(--border);text-align:left;font-size:13px}"
"th{color:var(--muted);font-weight:600}"
"tr.stable td{color:var(--good)}"
"#err{color:var(--bad);margin:8px 0;min-height:1em;font-size:13px}"
".hint{color:var(--muted);font-size:12px;margin:2px 0 14px}"
".score-good{color:var(--good);font-weight:600}"
"#scoreDisplay{font-size:24px;font-weight:700;margin:18px 0 6px}"
"#climateTable{border-collapse:collapse;width:100%;margin-top:6px;font-size:12.5px}"
"#climateTable th{color:var(--muted);font-weight:600;text-align:left;"
"padding:5px 14px 5px 0;white-space:nowrap;vertical-align:top}"
"#climateTable td{padding:5px 10px 5px 0;font-family:ui-monospace,Menlo,monospace;white-space:nowrap}"
".climate-label{color:var(--muted);display:inline-block;min-width:34px}"
".climate-pct{display:inline-block;min-width:52px;text-align:right}"
"#progressWrap{background:var(--panel2);border:1px solid var(--border);border-radius:8px;"
"height:20px;overflow:hidden;margin:8px 0 4px}"
"#progressBar{height:100%;width:0%;background:var(--accent);transition:width 0.4s ease}"
"#progressBar.ready{background:var(--good)}"
"#progressText{font-size:12px;color:var(--muted);margin:0 0 16px}"
"#cycleProgressWrap{background:var(--panel2);border:1px solid var(--border);border-radius:8px;"
"height:20px;overflow:hidden;margin:8px 0 4px;display:none}"
"#cycleProgressBar{height:100%;width:0%;background:var(--good);transition:width 0.15s linear}"
"#cycleProgressText{font-size:12px;color:var(--muted);margin:0 0 16px;display:none}"
"</style></head><body>"

"<h1>Biome Border Finder</h1>"

"<div class='row'><label>Statistic</label>"
"<select id='modeSelect' onchange='onModeChange()'>"
"<option value='border'>Biome border percentages</option>"
"<option value='origin'>Biome percentages at (0,0)</option>"
"</select></div>"

"<div class='row' id='biomeRow'><label>Biome</label>"
"<input type='text' list='biomelist' id='biomeInput' autocomplete='off' placeholder=\"start typing a biome name, or 'generic surface'\" size='30'>"
"<datalist id='biomelist'></datalist></div>"
"<div class='hint' id='modeHint' style='margin:-6px 0 10px'>"
"\"generic surface\" picks whatever biome sits at (0,0) for each seed (river one seed, plains the next, "
"and so on) and blends all of their border edges into one running total."
"</div>"

"<div class='row' id='cycleRow'><label>Auto-cycle</label>"
"<input type='checkbox' id='cycleInput'>"
"<span class='hint' style='margin:0'>Automatically cycle to the next surface biome alphabetically every 1000 seeds</span></div>"

"<div class='row'><label>Sample height</label>"
"<select id='yModeSelect' onchange='onYModeChange()'>"
"<option value='adaptive'>Surface</option>"
"<option value='fixed' selected>Fixed Y</option>"
"</select></div>"
"<div class='hint' id='yModeHint' style='margin:-6px 0 10px'>"
"Fixed Y=252 is default"
"</div>"

"<div class='row' id='yRow'><label>Sample Y</label>"
"<input type='number' id='yInput' style='width:100px'>"
"<span class='hint' style='margin:0'>block Y-coordinate, -64 to 319; default is 252</span></div>"

"<div class='row'><label>Start seed</label>"
"<input type='number' id='seedInput' placeholder='leave blank to auto-continue'></div>"

"<div class='row'><label>Threads</label>"
"<input type='number' id='threadsInput' min='1' style='width:80px'>"
"<span class='hint' style='margin:0'>defaults to the detected CPU core count</span></div>"

"<div class='row' id='graphUpdateRow'><label>Graph updates</label>"
"<select id='snapshotSelect'>"
"<option value='1'>every seed</option>"
"<option value='10' selected>every 10 seeds</option>"
"<option value='100'>every 100 seeds</option>"
"</select></div>"

"<div class='row'><label>Max Y (%)</label>"
"<input type='number' id='maxYInput' min='0.001' step='0.001' value='0.10' style='width:100px'>"
"<span class='hint' style='margin:0'>vertical scale</span></div>"

"<div class='row'>"
"<button class='primary' id='toggleBtn' onclick='toggleRun()'>Start</button>"
"<button onclick='doReset()'>Reset this biome's data</button>"
"</div>"

"<div id='err'></div>"
"<div id='status'>loading...</div>"

"<div id='progressWrap'><div id='progressBar'></div></div>"
"<div id='progressText'>Progress toward stable results: gathering data...</div>"
"<div id='cycleProgressWrap'><div id='cycleProgressBar'></div></div>"
"<div id='cycleProgressText'>Auto-cycle progress: 0.0% (0/1000 seeds)</div>"

"<div id='graphSection'>"
"<div id='scoreDisplay'>Average absolute &Delta;: gathering data...</div>"
"<canvas id='chart' height='360'></canvas>"

"<div class='hint'>"
"The graph shows one score: the average absolute change (Δ) over the recent look-back period "
"for the five most common neighbouring biomes. Smaller is better; zero means the recent "
"percentages have stopped changing. The green zone is ±0.01%. "
"</div>"

"<div id='legend'></div>"
"</div>"

"<table id='resultsTable'><thead><tr>"
"<th id='biomeColHeader'>Neighboring biome</th><th>Samples</th><th>%</th>"
"<th>95% CI</th><th>&Delta; vs earlier</th>"
"</tr></thead><tbody></tbody></table>"

"<div id='climateSection'>"
"<h1 style='margin-top:28px'>Climate zones inside this biome</h1>"
"<div class='hint'>"
"One sample point per seed, taken somewhere inside the target biome (not on its border). "
"Shows how often each climate level shows up wherever this biome actually generates. "
"Not collected in \"biome at origin\" mode, since that mode has no single target biome."
"</div>"
"<div class='hint' id='climateSampleCount' style='margin:0 0 6px'>Climate samples so far: 0</div>"
"<div style='overflow-x:auto'>"
"<table id='climateTable'><tbody></tbody></table>"
"</div>"
"</div>"

"<script>"

"let idToName = {};"
"let colorOf = {};"
"const palette = ['#5fb3ff','#ff8a5f','#7ee08a','#e07ee0','#ffd166','#6fe3d6','#c792ea','#f07178',"
"'#8bd450','#ff6f91','#4fc3f7','#ffb74d'];"
"let nextColor = 0;"

"let scoreHistory = new Map();"
"let snapshotHistory = new Map();"
"let since = null;"
"let knownEpoch = null;"
"let allBiomesList = [];"

"let lastSeedsDone = 0;"
"let lastStatusTime = null;"
"let currentSpeed = 0;"
"let speedSamples = [];"
"let seedsAtCycleStart = null;"
"let cycleStartBiome = null;"
"let cycleTransitionInProgress = false;"

"function colorFor(id){"
"  if(!(id in colorOf)){"
"    colorOf[id]=palette[nextColor%palette.length];"
"    nextColor++;"
"  }"
"  return colorOf[id];"
"}"

"let defaultYBlock = 252;"
"let formSynced = false;"

"async function loadBiomes(){"
"  try {"
"    const r = await fetch('/api/biomes');"
"    const j = await r.json();"
"    if(!j || !Array.isArray(j.biomes)) throw new Error('Invalid biome list');"
"    allBiomesList = ['generic surface'].concat(j.biomes.map(b => b.name));"
"    allBiomesList.sort();"
"    const dl = document.getElementById('biomelist');"
"    dl.innerHTML = allBiomesList.map(name => `<option value='${name}'>`).join('');"
"    idToName = {};"
"    j.biomes.forEach(b => idToName[b.id] = b.name);"
"    const ti = document.getElementById('threadsInput');"
"    if(!ti.value && j.suggestedThreads) ti.value = j.suggestedThreads;"
"    defaultYBlock = j.defaultYBlock;"
"    const yi = document.getElementById('yInput');"
"    if(!yi.value && j.defaultYBlock !== undefined) yi.value = j.defaultYBlock;"
"    if(j.minYBlock !== undefined) yi.min = j.minYBlock;"
"    if(j.maxYBlock !== undefined) yi.max = j.maxYBlock;"
"  } catch(e) {"
"    /* Autocomplete is optional; the biome field still works as plain text. */"
"    allBiomesList = ['generic surface'];"
"  }"
"}"

"function onModeChange(){\n"
"  const mode = document.getElementById('modeSelect').value;\n"
"  const isOrigin = (mode === 'origin');\n"
"  document.getElementById('biomeRow').style.display = isOrigin ? 'none' : 'flex';\n"
"  document.getElementById('cycleRow').style.display = isOrigin ? 'none' : 'flex';\n"
"  document.getElementById('modeHint').style.display = isOrigin ? 'none' : 'block';\n"
"  document.getElementById('climateSection').style.display = 'block';\n"
"  const graphSection = document.getElementById('graphSection');\n"
"  const graphUpdateRow = document.getElementById('graphUpdateRow');\n"
"  graphSection.style.display = isOrigin ? 'none' : 'block';\n"
"  graphUpdateRow.style.display = isOrigin ? 'none' : 'flex';\n"
"}\n"

"function onYModeChange(){"
"  const isFixed = document.getElementById('yModeSelect').value === 'fixed';"
"  document.getElementById('yRow').style.display = isFixed ? 'flex' : 'none';"
"}"

"function setErr(msg){"
"  document.getElementById('err').textContent = msg || '';"
"}"

"function resetGraph(){"
"  scoreHistory = new Map();"
"  snapshotHistory = new Map();"
"  since = null;"
"  lastStatusTime = null;"
"  currentSpeed = 0;"
"  speedSamples = [];"
"}"

"function getMaxY(){"
"  let v = parseFloat(document.getElementById('maxYInput').value);"
"  if(!isFinite(v) || v <= 0) v = 0.10;"
"  return v;"
"}"

"async function doStart(){"
"  setErr('');"
"  seedsAtCycleStart = null;"
"  const mode = document.getElementById('modeSelect').value;"
"  const biome = document.getElementById('biomeInput').value.trim();"
"  const seed = document.getElementById('seedInput').value.trim();"
"  const threads = document.getElementById('threadsInput').value.trim();"
"  const snap = document.getElementById('snapshotSelect').value;"
"  const yMode = document.getElementById('yModeSelect').value;"
"  const y = document.getElementById('yInput').value.trim();"
"  if(mode === 'border' && !biome){"
"    setErr(\"Type a biome name (or 'generic surface') first.\");"
"    return;"
"  }"
"  let url = '/api/start?mode=' + mode + '&snapshot=' + snap + '&ymode=' + yMode;"
"  if(mode === 'border') url += '&biome=' + encodeURIComponent(biome);"
"  if(seed !== '') url += '&seed=' + encodeURIComponent(seed);"
"  if(threads !== '') url += '&threads=' + encodeURIComponent(threads);"
"  if(yMode === 'fixed' && y !== '') url += '&y=' + encodeURIComponent(y);"
"  const r = await fetch(url);"
"  const j = await r.json();"
"  if(j.error) setErr(j.error);"
"  else resetGraph();"
"  refresh();"
"}"

"async function doStop(){"
"  setErr('');"
"  await fetch('/api/stop');"
"  refresh();"
"}"

"function toggleRun(){"
"  const btn = document.getElementById('toggleBtn');"
"  if(btn.dataset.running === 'true'){"
"    doStop();"
"  } else {"
"    doStart();"
"  }"
"}"

"async function doReset(){"
"  const mode = document.getElementById('modeSelect').value;"
"  const biome = document.getElementById('biomeInput').value.trim();"
"  const yMode = document.getElementById('yModeSelect').value;"
"  const y = document.getElementById('yInput').value.trim();"
"  if(mode === 'border' && !biome){"
"    setErr(\"Type the biome name (or 'generic surface') to reset.\");"
"    return;"
"  }"
"  const label = mode === 'origin' ? 'biome-at-origin' : biome;"
"  if(!confirm('Erase all saved progress for \"' + label + '\"? This cannot be undone.')) return;"
"  let url = '/api/reset?mode=' + mode + '&ymode=' + yMode;"
"  if(mode === 'border') url += '&biome=' + encodeURIComponent(biome);"
"  if(yMode === 'fixed' && y !== '') url += '&y=' + encodeURIComponent(y);"
"  const r = await fetch(url);"
"  const j = await r.json();"
"  if(j.error) setErr(j.error);"
"  else resetGraph();"
"  refresh();"
"}"

"function fmtPct(v){"
"  return (v>=0?'+':'') + v.toFixed(3) + '%';"
"}"

"function syncFormFromStatus(j){"
"  if(formSynced) return;"
"  if(!j.target) return;"
"  formSynced = true;"
"  document.getElementById('modeSelect').value = j.mode;"
"  document.getElementById('yModeSelect').value = j.yMode;"
"  document.getElementById('yInput').value = j.yBlock;"
"  if(j.mode === 'border'){"
"    document.getElementById('biomeInput').value = j.generic ? 'generic surface' : j.target;"
"  }"
"  onModeChange();"
"  onYModeChange();"
"}"

"function renderProgress(j){"
"  const bar = document.getElementById('progressBar');"
"  const text = document.getElementById('progressText');"
"  const p = j.progress || {};"
"  if(p.fraction === null || p.fraction === undefined){"
"    bar.style.width = '0%';"
"    bar.classList.remove('ready');"
"    text.textContent = 'Progress toward stable results: gathering data...';"
"    return;"
"  }"
"  bar.style.width = (p.fraction * 100).toFixed(1) + '%';"
"  bar.classList.toggle('ready', !!p.ready);"
"  if(p.ready){"
"    text.textContent = 'Observed stability and 95% CI precision have both reached the ±0.05% target.';"
"  } else {"
"    text.textContent = 'Progress toward stable results: ' + (p.fraction*100).toFixed(1) + '%'"
"      + ' (≈' + Math.round(p.remainingSeeds).toLocaleString() + ' seeds remain)';"
"  }"
"}"

"function renderCycleProgress(j){"
"  const wrap = document.getElementById('cycleProgressWrap');"
"  const bar = document.getElementById('cycleProgressBar');"
"  const text = document.getElementById('cycleProgressText');"
"  const enabled = document.getElementById('cycleInput').checked;"
"  const active = enabled && j.mode === 'border' && (j.running || seedsAtCycleStart !== null);"
"  if(!active){"
"    wrap.style.display = 'none';"
"    text.style.display = 'none';"
"    return;"
"  }"
"  wrap.style.display = 'block';"
"  text.style.display = 'block';"
"  if(seedsAtCycleStart === null) seedsAtCycleStart = j.seedsDone;"
"  const cycleSeeds = Math.max(0, j.seedsDone - seedsAtCycleStart);"
"  const pct = Math.min(100, Math.floor(cycleSeeds) / 10);"
"  bar.style.width = pct.toFixed(1) + '%';"
"  text.textContent = cycleTransitionInProgress"
"    ? 'Auto-cycle progress: 100.0% - switching to the next biome...'"
"    : 'Auto-cycle progress: ' + pct.toFixed(1) + '% (' + Math.min(1000, cycleSeeds).toLocaleString() + '/1000 seeds)';"
"}"

"async function refreshStatus(){"
"  const r = await fetch('/api/status');"
"  const j = await r.json();"

"  const toggleBtn = document.getElementById('toggleBtn');"
"  if(j.running){"
"    toggleBtn.textContent = 'Stop';"
"    toggleBtn.className = '';"
"    toggleBtn.dataset.running = 'true';"
"  } else {"
"    toggleBtn.textContent = 'Start';"
"    toggleBtn.className = 'primary';"
"    toggleBtn.dataset.running = 'false';"
"  }"

"  const cycleEnabled = document.getElementById('cycleInput').checked;"
"  if(cycleEnabled && j.mode === 'border' && j.running){"
"    const current = j.generic ? 'generic surface' : j.target;"
"    if(seedsAtCycleStart === null || cycleStartBiome !== current){"
"      seedsAtCycleStart = j.seedsDone;"
"      cycleStartBiome = current;"
"    } else if(j.seedsDone - seedsAtCycleStart >= 1000){"
"      const sBiomes = allBiomesList.filter(b => b !== 'generic surface');"
"      const idx = sBiomes.indexOf(current);"
"      if(idx < 0 || sBiomes.length === 0){"
"        setErr('Auto-cycle could not find the current biome in the biome list.');"
"      } else {"
"        const nextBiome = sBiomes[(idx + 1) % sBiomes.length];"
"        if(cycleTransitionInProgress) return;"
"        cycleTransitionInProgress = true;"
"        document.getElementById('biomeInput').value = nextBiome;"
"        try {"
"          await fetch('/api/stop');"
"          const stopped = await (await fetch('/api/status')).json();"
"          const snap = document.getElementById('snapshotSelect').value;"
"          const yMode = document.getElementById('yModeSelect').value;"
"          const y = document.getElementById('yInput').value.trim();"
"          const threads = document.getElementById('threadsInput').value.trim();"
"          let url = '/api/start?mode=border&snapshot=' + snap + '&ymode=' + yMode"
"            + '&biome=' + encodeURIComponent(nextBiome)"
"            + '&seed=' + encodeURIComponent(stopped.nextSeed);"
"          if(threads !== '') url += '&threads=' + encodeURIComponent(threads);"
"          if(yMode === 'fixed' && y !== '') url += '&y=' + encodeURIComponent(y);"
"          const res = await (await fetch(url)).json();"
"          if(res.error){"
"            setErr(res.error);"
"            seedsAtCycleStart = null;"
"            cycleStartBiome = null;"
"          } else {"
"            resetGraph();"
"            const started = await (await fetch('/api/status')).json();"
"            seedsAtCycleStart = started.seedsDone;"
"            cycleStartBiome = started.generic ? 'generic surface' : started.target;"
"          }"
"        } finally {"
"          cycleTransitionInProgress = false;"
"        }"
"        return;"
"      }"
"    }"
"  } else {"
"    seedsAtCycleStart = null;"
"    cycleStartBiome = null;"
"  }"
"  renderCycleProgress(j);"
"  const now = Date.now();"
"  if(j.running){"
"    speedSamples.push({time: now, seedsDone: j.seedsDone});"
"    const cutoff = now - 10000;"
"    while(speedSamples.length > 1 && speedSamples[1].time <= cutoff) speedSamples.shift();"
"    if(speedSamples.length >= 2 && speedSamples[0].time <= cutoff){"
"      const base = speedSamples[0];"
"      const seedsInTenSeconds = Math.max(0, j.seedsDone - base.seedsDone);"
"      currentSpeed = seedsInTenSeconds / 10;"
"    } else {"
"      currentSpeed = 0;"
"    }"
"  } else {"
"    currentSpeed = 0;"
"    speedSamples = [];"
"  }"
"  lastSeedsDone = j.seedsDone;"
"  lastStatusTime = now;"

"  syncFormFromStatus(j);"

"  const sampleLabel = j.mode === 'origin' ? 'Total samples at origin: ' : 'Total border samples: ';"
"  const targetLabel = j.mode === 'origin' ? '(biome frequency at the origin)' : (j.target || '(none selected yet)');"
"  const yLabel = j.yMode === 'adaptive' ? 'adaptive (each column at its own terrain surface)' : ('fixed Y=' + j.yBlock);"
"  const speedText = j.running ? currentSpeed.toFixed(1) + ' seeds/sec' : '0.0 seeds/sec';"

"  document.getElementById('status').textContent = "
"    'State: ' + (j.running ? ('RUNNING (' + j.numWorkers + ' threads)') : 'stopped') + '\\n' +"
"    'Speed: ' + speedText + '\\n' +"
"    'Statistic: ' + targetLabel + '\\n' +"
"    'Sample height: ' + yLabel + '\\n' +"
"    'Seeds sampled: ' + j.seedsDone.toLocaleString() + '\\n' +"
"    'Next seed to sample: ' + j.nextSeed + '\\n' +"
"    sampleLabel + j.totalBorder.toLocaleString();"

"  document.getElementById('biomeColHeader').textContent ="
"    j.mode === 'origin' ? 'Biome at origin' : 'Neighboring biome';"

"  const tbody = document.querySelector('#resultsTable tbody');"

"  tbody.innerHTML = j.results.map(r => {"
"    const d = r.delta === null ? 'gathering data...' : fmtPct(r.delta);"
"    const ci = r.ciLo.toFixed(3) + '\u2013' + r.ciHi.toFixed(3) + '%';"
"    return `<tr class=\"${r.stable?'stable':''}\">"
"      <td><span class=\"swatch\" style=\"background:${colorFor(r.id)}\"></span>${r.name}</td>`"
"      + `<td>${r.count}</td><td>${r.pct.toFixed(3)}%</td><td>${ci}</td><td>${d}</td></tr>`;"
"  }).join('');"

"  if(knownEpoch !== null && j.epoch !== knownEpoch){"
"    resetGraph();"
"  }"

"  knownEpoch = j.epoch;"

"  renderProgress(j);"
"  renderClimateStats(j);"
"}"

"function climateRow(label, entries, totalSamples){"
"  if(totalSamples === 0){"
"    return `<tr><th>${label}</th><td class=\"hint\">no data yet</td></tr>`;"
"  }"
"  const cells = entries.map(e =>"
"    `<td><span class=\"climate-label\">${e.label}</span>`+"
"    `<span class=\"climate-pct\">${e.pct.toFixed(1)}%</span></td>`"
"  ).join('');"
"  return `<tr><th>${label}</th>${cells}</tr>`;"
"}"

"function renderClimateStats(j){"
"  const n = j.climateSamples || 0;"
"  document.getElementById('climateSampleCount').textContent ="
"    'Climate samples so far: ' + n;"

"  const tEntries = (j.temperature||[]).map(x => ({label:'T'+x.level, pct:x.pct}));"
"  const hEntries = (j.humidity||[]).map(x => ({label:'H'+x.level, pct:x.pct}));"
"  const cEntries = (j.continentalness||[]).map(x => ({label:'C'+x.level, pct:x.pct}));"
"  const eEntries = (j.erosion||[]).map(x => ({label:'E'+x.level, pct:x.pct}));"
"  const pvEntries = (j.pv||[]).map(x => ({label:'PV'+x.level, pct:x.pct}));"
"  const wEntries = j.weirdness ? ["
"    {label:'W-', pct:j.weirdness.neg.pct},"
"    {label:'W+', pct:j.weirdness.pos.pct}"
"  ] : [];"

"  const rows = ["
"    ['Temperature', tEntries],"
"    ['Humidity', hEntries],"
"    ['Continentalness', cEntries],"
"    ['Erosion', eEntries],"
"    ['Peaks/Valleys', pvEntries],"
"    ['Weirdness sign', wEntries]"
"  ];"

"  document.querySelector('#climateTable tbody').innerHTML ="
"    rows.map(([label, entries]) => climateRow(label, entries, n)).join('');"
"}"

"function calculateScore(current, reference){"
"  if(!current || !reference) return null;"
"  if(!current.t || !reference.t) return null;"

"  const currentIds = Object.keys(current.c).map(Number);"
"  const referenceIds = Object.keys(reference.c).map(Number);"
"  const candidateIds = Array.from(new Set(currentIds.concat(referenceIds)));"
"  candidateIds.sort((a,b) => {"
"    const aShare = Math.max((current.c[a] || 0) / current.t, (reference.c[a] || 0) / reference.t);"
"    const bShare = Math.max((current.c[b] || 0) / current.t, (reference.c[b] || 0) / reference.t);"
"    return bShare - aShare;"
"  });"

"  const top = candidateIds.slice(0,5);"

"  if(top.length === 0) return null;"

"  let sum = 0;"
"  let used = 0;"

"  for(const id of top){"
"    const key = String(id);"
"    const currentCount = current.c[key] || 0;"
"    const referenceCount = reference.c[key] || 0;"

"    const currentPct = 100 * currentCount / current.t;"
"    const referencePct = 100 * referenceCount / reference.t;"

"    sum += Math.abs(currentPct - referencePct);"
"    used++;"
"  }"

"  return used > 0 ? sum / used : null;"
"}"

"async function refreshHistory(){"
"  let url = '/api/history';"
"  if(since) url += '?since=' + encodeURIComponent(since);"

"  const r = await fetch(url);"
"  const j = await r.json();"

"  if(knownEpoch !== null && j.epoch !== knownEpoch){"
"    resetGraph();"
"    knownEpoch = j.epoch;"
"  }"

"  for(const point of j.points){"
"    snapshotHistory.set(point.s, point);"
"  }"

"  const allSnapshots = Array.from(snapshotHistory.values())"
"    .sort((a,b) => a.s - b.s);"

"  const points = [];"

"  for(let i = 0; i < allSnapshots.length; i++){"
"    const current = allSnapshots[i];"

"    let lookback = Math.floor(current.s / 20);"
"    if(lookback < 200) lookback = 200;"

"    const targetSeed = current.s - lookback;"

"    if(targetSeed <= 0) continue;"

"    let reference = null;"

"    for(let k = i - 1; k >= 0; k--){"
"      if(allSnapshots[k].s <= targetSeed){"
"        reference = allSnapshots[k];"
"        break;"
"      }"
"    }"

"    if(!reference) continue;"

"    const score = calculateScore(current, reference);"

"    if(score !== null && isFinite(score)){"
"      points.push({x: current.s, y: score});"
"    }"
"  }"

"  for(const p of points){"
"    scoreHistory.set(p.x, p.y);"
"  }"

"  since = j.epoch + ':' + j.count;"

"  drawChart();"
"}"

"function formatGraphPct(value){"
"  const a = Math.abs(value);"
"  if(a >= 1) return value.toFixed(1) + '%';"
"  if(a >= 0.1) return value.toFixed(2) + '%';"
"  return value.toFixed(3) + '%';"
"}"

"function drawChart(){"
"  const canvas = document.getElementById('chart');"
"  const cssW = canvas.clientWidth || 860;"
"  const H = 360;"
"  const dpr = window.devicePixelRatio || 1;"

"  canvas.width = Math.round(cssW * dpr);"
"  canvas.height = Math.round(H * dpr);"

"  const ctx = canvas.getContext('2d');"
"  ctx.setTransform(dpr,0,0,dpr,0,0);"

"  const W = cssW;"
"  const padL = 70;"
"  const padR = 18;"
"  const padT = 18;"
"  const padB = 38;"

"  ctx.clearRect(0,0,W,H);"

"  const points = Array.from(scoreHistory.entries())"
"    .map(([x,y]) => ({x:Number(x), y:Number(y)}))"
"    .filter(p => isFinite(p.x) && isFinite(p.y))"
"    .sort((a,b) => a.x - b.x);"

"  updateScoreDisplay(points);"

"  const maxY = getMaxY();"

"  let maxX = 1;"
"  if(points.length > 0){"
"    maxX = points[points.length - 1].x;"
"    if(maxX < 1) maxX = 1;"
"  }"

"  const xOf = x => padL + (W-padL-padR) * (x/maxX);"

"  const yOf = y => {"
"    const v = Math.max(0, Math.min(maxY, y));"
"    return H-padB - (H-padT-padB) * (v/maxY);"
"  };"

"  ctx.font = '11px -apple-system,BlinkMacSystemFont,sans-serif';"
"  ctx.lineWidth = 1;"

"  ctx.strokeStyle = '#3a3b3e';"
"  ctx.fillStyle = '#a3a4a8';"

"  for(let i=0; i<=5; i++){"
"    const fraction = i / 5;"
"    const y = padT + (H-padT-padB) * fraction;"
"    const value = maxY * (1 - fraction);"

"    ctx.beginPath();"
"    ctx.moveTo(padL,y);"
"    ctx.lineTo(W-padR,y);"
"    ctx.stroke();"

"    ctx.fillText(formatGraphPct(value), 8, y + 4);"
"  }"

"  const greenLimit = Math.min(0.01, maxY);"
"  const greenY = yOf(greenLimit);"
"  const zeroY = yOf(0);"

"  ctx.fillStyle = 'rgba(76,175,125,0.10)';"
"  ctx.fillRect(padL, greenY, W-padL-padR, zeroY-greenY);"

"  ctx.strokeStyle = '#4caf7d';"
"  ctx.lineWidth = 1.5;"
"  ctx.beginPath();"
"  ctx.moveTo(padL,zeroY);"
"  ctx.lineTo(W-padR,zeroY);"
"  ctx.stroke();"

"  ctx.fillStyle = '#a3a4a8';"
"  ctx.fillText('average absolute Δ (%)', 8, 12);"
"  ctx.fillText('seeds sampled →', W-120, H-8);"

"  ctx.fillText('0', padL-4, H-padB+16);"

"  if(points.length > 0){"
"    const firstX = points[0].x;"
"    const lastX = points[points.length-1].x;"
"    ctx.fillText(String(firstX), padL-4, H-padB+16);"
"    ctx.fillText(String(lastX), W-padR-35, H-padB+16);"
"  }"

"  if(points.length >= 2){"
"    ctx.strokeStyle = '#5fb3ff';"
"    ctx.lineWidth = 2;"
"    ctx.lineJoin = 'round';"
"    ctx.lineCap = 'round';"

"    for(let i=1; i<points.length; i++){"
"      const a = points[i-1];"
"      const b = points[i];"

"      if(b.x <= a.x) continue;"

"      ctx.beginPath();"
"      ctx.moveTo(xOf(a.x), yOf(a.y));"
"      ctx.lineTo(xOf(b.x), yOf(b.y));"
"      ctx.stroke();"
"    }"
"  }"

"  if(points.length > 0){"
"    ctx.fillStyle = '#5fb3ff';"

"    for(const p of points){"
"      const x = xOf(p.x);"
"      const y = yOf(p.y);"

"      ctx.beginPath();"
"      ctx.arc(x,y,1.8,0,Math.PI*2);"
"      ctx.fill();"
"    }"
"  }"

"  if(points.length === 0){"
"    ctx.fillStyle = '#a3a4a8';"
"    ctx.fillText("
"      'The score graph will appear once enough history exists for a look-back comparison.',"
"      padL,"
"      H/2"
"    );"
"  }"
"}"

"function updateScoreDisplay(points){"
"  const el = document.getElementById('scoreDisplay');"
"  if(points.length === 0){"
"    el.textContent = 'Average absolute \u0394: gathering data...';"
"    el.classList.remove('score-good');"
"    return;"
"  }"
"  const latest = points[points.length - 1].y;"
"  el.textContent = 'Average absolute \u0394: ' + latest.toFixed(4) + '%';"
"  el.classList.toggle('score-good', latest < 0.01);"
"}"

"document.getElementById('maxYInput').addEventListener('input', drawChart);"

"async function refresh(){"
"  await refreshStatus();"
"  if(document.getElementById('modeSelect').value !== 'origin') await refreshHistory();"
"}"

"document.getElementById('biomeInput').addEventListener('input', function(e) {"
"  const val = this.value.toLowerCase();"
"  const dl = document.getElementById('biomelist');"
"  if(!val){"
"    dl.innerHTML = allBiomesList.map(name => `<option value='${name}'>`).join('');"
"    return;"
"  }"
"  const starts = [], contains = [];"
"  allBiomesList.forEach(name => {"
"    const lower = name.toLowerCase();"
"    if(lower.startsWith(val)) starts.push(name);"
"    else if(lower.includes(val)) contains.push(name);"
"  });"
"  dl.innerHTML = starts.concat(contains).map(name => `<option value='${name}'>`).join('');"
"});"

"loadBiomes();"
"refresh();"
"setInterval(refresh, 1000);"
"window.addEventListener('resize', drawChart);"

"</script></body></html>";


static void handleConnection(int fd) {
    char buf[4096];
    ssize_t n = read(fd, buf, sizeof(buf) - 1);
    if (n <= 0) { close(fd); return; }
    buf[n] = 0;

    char method[8] = "", path[512] = "";
    sscanf(buf, "%7s %511s", method, path);

    char *query = strchr(path, '?');
    if (query) { *query = 0; query++; }

    char respBuf[8192];

    if (strcmp(path, "/") == 0) {
        sendText(fd, "200 OK", "text/html; charset=utf-8", PAGE_HTML);
    } else if (strcmp(path, "/api/biomes") == 0) {
        buildBiomesJson(respBuf, sizeof(respBuf));
        sendText(fd, "200 OK", "application/json", respBuf);
    } else if (strcmp(path, "/api/status") == 0) {
        sendTextOwned(fd, "200 OK", "application/json", buildStatusJson());
    } else if (strcmp(path, "/api/history") == 0) {
        char sinceBuf[32] = "";
        getParam(query, "since", sinceBuf, sizeof(sinceBuf));
        sendTextOwned(fd, "200 OK", "application/json", buildHistoryJson(sinceBuf[0] ? sinceBuf : NULL));
    } else if (strcmp(path, "/api/start") == 0) {
        char biomeBuf[64] = "", seedBuf[32] = "", threadsBuf[16] = "", snapBuf[16] = "",
             modeBuf[16] = "", yBuf[16] = "";
        getParam(query, "biome", biomeBuf, sizeof(biomeBuf));
        long seedOverride = -1;
        if (getParam(query, "seed", seedBuf, sizeof(seedBuf)) && seedBuf[0])
            seedOverride = atol(seedBuf);
        int threads = (int) detectCoreCount();
        if (getParam(query, "threads", threadsBuf, sizeof(threadsBuf)) && threadsBuf[0])
            threads = atoi(threadsBuf);
        long snapshotEvery = 1;
        if (getParam(query, "snapshot", snapBuf, sizeof(snapBuf)) && snapBuf[0])
            snapshotEvery = atol(snapBuf);
        SampleMode mode = MODE_BORDER;
        if (getParam(query, "mode", modeBuf, sizeof(modeBuf)) && strcasecmp(modeBuf, "origin") == 0)
            mode = MODE_ORIGIN;
        int yBlock = DEFAULT_Y_BLOCK;
        if (getParam(query, "y", yBuf, sizeof(yBuf)) && yBuf[0])
            yBlock = atoi(yBuf);
        YMode yMode = parseYModeParam(query);
        const char *err = startSampling(mode, biomeBuf, seedOverride, threads, snapshotEvery, yMode, yBlock);
        if (err) snprintf(respBuf, sizeof(respBuf), "{\"error\":\"%s\"}", err);
        else snprintf(respBuf, sizeof(respBuf), "{\"ok\":true}");
        sendText(fd, "200 OK", "application/json", respBuf);
    } else if (strcmp(path, "/api/stop") == 0) {
        stopSampling();
        sendText(fd, "200 OK", "application/json", "{\"ok\":true}");
    } else if (strcmp(path, "/api/reset") == 0) {
        char biomeBuf[64] = "", modeBuf[16] = "", yBuf[16] = "";
        getParam(query, "biome", biomeBuf, sizeof(biomeBuf));
        SampleMode mode = MODE_BORDER;
        if (getParam(query, "mode", modeBuf, sizeof(modeBuf)) && strcasecmp(modeBuf, "origin") == 0)
            mode = MODE_ORIGIN;
        int yBlock = DEFAULT_Y_BLOCK;
        if (getParam(query, "y", yBuf, sizeof(yBuf)) && yBuf[0])
            yBlock = atoi(yBuf);
        if (yBlock < MIN_Y_BLOCK) yBlock = MIN_Y_BLOCK;
        if (yBlock > MAX_Y_BLOCK) yBlock = MAX_Y_BLOCK;
        YMode yMode = parseYModeParam(query);
        int generic = (mode == MODE_BORDER && isGenericSurfaceKeyword(biomeBuf));
        // Compare by canonical name, as startSampling() does, so differently-
        // cased input matches the running identity.
        int resolvedBiomeId = (mode == MODE_BORDER && !generic) ? resolveBiomeName(biomeBuf) : -1;
        const char *canonicalName = (resolvedBiomeId >= 0) ? biome2str(MC_VERSION, resolvedBiomeId) : biomeBuf;

        pthread_mutex_lock(&g_lock);
        int isCurrentIdentity = (mode == g_mode) && (generic == g_generic) && (yMode == g_yMode) &&
                                 (yMode == YMODE_ADAPTIVE || yBlock == g_yBlock) &&
                                 (mode == MODE_ORIGIN || generic || strcasecmp(canonicalName, g_targetName) == 0);
        if (g_running && isCurrentIdentity) {
            pthread_mutex_unlock(&g_lock);
            sendText(fd, "200 OK", "application/json", "{\"error\":\"Stop it before resetting.\"}");
        } else {
            char path2[300];
            checkpointPath(mode, generic, canonicalName, yMode, yBlock, path2, sizeof(path2));
            remove(path2);
            if (isCurrentIdentity) {
                memset(g_counts, 0, sizeof(g_counts));
                resetClimateStatsLocked();
                g_nextSeed = 0; g_seedsDone = 0; g_totalBorder = 0;
                g_historyCount = 0;
                g_historyEpoch++;
            }
            pthread_mutex_unlock(&g_lock);
            sendText(fd, "200 OK", "application/json", "{\"ok\":true}");
        }
    } else {
        sendText(fd, "404 Not Found", "text/plain", "not found");
    }
    close(fd);
}

static void *connectionThread(void *arg) {
    int fd = (int) (intptr_t) arg;
    handleConnection(fd);
    return NULL;
}

int main(void) {
    signal(SIGPIPE, SIG_IGN);

    buildBiomeTable();

    int serverFd = socket(AF_INET, SOCK_STREAM, 0);
    int opt = 1;
    setsockopt(serverFd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = inet_addr("127.0.0.1"); // localhost only
    addr.sin_port = htons(HTTP_PORT);

    if (bind(serverFd, (struct sockaddr *) &addr, sizeof(addr)) != 0) {
        perror("bind failed (is the port already in use?)");
        return 1;
    }
    listen(serverFd, 16);

    printf("Biome Border Finder is running.\n");
    printf("Open this in your browser:  http://localhost:%d\n", HTTP_PORT);
    printf("Detected %ld CPU cores (used as the default thread count).\n", detectCoreCount());
    printf("(Press Ctrl+C here to shut it down.)\n");

    for (;;) {
        struct sockaddr_in clientAddr;
        socklen_t clientLen = sizeof(clientAddr);
        int clientFd = accept(serverFd, (struct sockaddr *) &clientAddr, &clientLen);
        if (clientFd < 0) continue;

        pthread_t t;
        pthread_create(&t, NULL, connectionThread, (void *) (intptr_t) clientFd);
        pthread_detach(t);
    }

    return 0;
}