/*
 * csakura - a sakura tree with falling petals for your terminal
 *
 * Grows a lush, illustration-style cherry-blossom tree: a metaball
 * canopy of blossom clouds with depth shading, a thick tapering trunk,
 * and petals drifting off on the wind. Regenerates on resize.
 *
 * Deps: ncurses (wide-char), libcurl. Build: make. License: MIT.
 * Works on Linux and macOS.
 */

#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#else
#define _XOPEN_SOURCE 700
#endif

#include <curl/curl.h>
#include <getopt.h>
#include <locale.h>
#include <math.h>
#include <ncurses.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define VERSION "2.0.0"
#define WEATHER_REFRESH_SECS 600 /* 10 minutes */

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define MAX_PETALS  768
#define MAX_SOURCES 4096
#define MAX_BLOBS   28
#define MAX_STARS   300
#define MAX_RAIN    500
#define MAX_FOG     200
#define MAX_SNOW    400

typedef struct {
    const char *glyph; /* UTF-8 glyph, NULL = empty cell */
    short pair;
    bool bold;
} Cell;

typedef struct {
    double x, y;
    double vy;                /* fall speed, cells per frame  */
    double phase, freq, amp;  /* horizontal sway              */
    const char *glyph;
    short pair;
    double rest;              /* seconds left on the ground, <0 = falling */
    bool active;
} Petal;

typedef struct { short x, y; } Coord;
typedef struct { double x, y, rx, ry; } Blob;

typedef struct {
    double x, y;
    double vy;    /* fall speed, cells per frame — no sway, straight down */
} Raindrop;

typedef struct {
    double x, y;
    double vy;                /* fall speed, cells per frame — much slower
                                * than rain, gentle like a petal          */
    double phase, freq, amp;  /* horizontal sway, same idea as Petal      */
    double rest;              /* seconds settled on the ground, <0 = falling */
} Snowflake;

typedef struct {
    double x, y;
    double vx;    /* slow horizontal drift, sign varies per wisp */
    int width;    /* cells wide, fixed for the wisp's lifetime   */
} FogWisp;

/* ---- state ------------------------------------------------------------- */

static Cell *grid = NULL;
static int gw = 0, gh = 0;

static Coord sources[MAX_SOURCES]; /* canopy cells petals can spawn from */
static int nsources = 0;

static Blob blobs[MAX_BLOBS];
static int nblobs = 0;

static Petal petals[MAX_PETALS];
static int npetals = 0;

static double wind = 0.0, wind_target = 0.0;

/* night mode / rain: set once from the fetch (or --force), before curses
 * starts. Everything below just reads these; nothing re-fetches mid-run. */
static bool   g_night = false;
static bool   g_raining = false;
static double g_rain_intensity = 0.0; /* 0..1, drives raindrop count/speed */
static bool   g_fog = false;
static bool   g_snowing = false;
static double g_snow_intensity = 0.0; /* 0..1, drives snowflake count/speed */
static double g_wind_factor = 1.0; /* multiplies opt_wind; 1.0 = unaffected
                                     * (used before/if the fetch fails) */

static Coord stars[MAX_STARS];
static int nstars = 0;

static Raindrop raindrops[MAX_RAIN];
static int nrain = 0;

static FogWisp fog[MAX_FOG];
static int nfog = 0;

static Snowflake snowflakes[MAX_SNOW];
static int nsnow = 0;

static volatile sig_atomic_t running = 1;

/* ---- options ------------------------------------------------------------ */

static int    opt_fps     = 20;    /* -f  frames per second (5-60)   */
static int    opt_density = 5;     /* -p  petal density     (1-10)   */
static double opt_wind    = 1.0;   /* -w  wind strength     (0-10)   */
static bool   opt_ascii   = false; /* -a  ASCII glyphs only          */
static bool   opt_debug   = false; /* -d, --debug show detailed weather diagnostics */
static int    opt_palette = 0;     /* -c  blossom palette index      */
static int    opt_force      = 0;  /* --force=day|night      0=auto, 1=day,  2=night  (debug) */
static int    opt_force_rain = 0;  /* --force=rain|norain    0=auto, 1=rain, 2=norain (debug) */
static int    opt_force_fog  = 0;  /* --force=fog|nofog      0=auto, 1=fog,  2=nofog  (debug) */
static int    opt_force_wind = 0;  /* --force=calm|light|moderate|strong  0=auto, 1-4 (debug) */
static int    opt_force_snow = 0;  /* --force=snow|nosnow    0=auto, 1=snow, 2=nosnow (debug) */

/* ---- helpers ------------------------------------------------------------ */

static double frand(void) { return rand() / ((double)RAND_MAX + 1.0); }
static double frange(double a, double b) { return a + frand() * (b - a); }
static double clampd(double v, double a, double b)
{
    return v < a ? a : (v > b ? b : v);
}

static void on_signal(int sig) { (void)sig; running = 0; }

/* ---- weather -------------------------------------------------------------
 *
 * One-shot fetch at startup (not per-frame): geolocate by public IP via
 * ip-api.com, then ask Open-Meteo (no API key needed) for the current
 * conditions at that lat/lon. Both are plain JSON over HTTP, parsed with
 * a tiny hand-rolled scanner instead of pulling in a JSON library, since
 * the shape of the responses we care about is small and fixed.
 *
 * Debug step: the result is just rendered as one line at the foot of the
 * tree (see draw()). If anything fails (no network, DNS, etc.) we fall
 * back to a placeholder string instead of blocking startup.
 * ------------------------------------------------------------------------ */

static char weather_line[256] = "";

struct HttpBuf { char *data; size_t size; };

static size_t http_write_cb(void *ptr, size_t size, size_t nmemb, void *userdata)
{
    struct HttpBuf *buf = (struct HttpBuf *)userdata;
    size_t total = size * nmemb;
    char *nd = realloc(buf->data, buf->size + total + 1);
    if (!nd)
        return 0;
    buf->data = nd;
    memcpy(buf->data + buf->size, ptr, total);
    buf->size += total;
    buf->data[buf->size] = '\0';
    return total;
}

/* GET url, return a malloc'd, NUL-terminated body (caller frees), or NULL
 * on any failure (timeout, no network, non-2xx, ...). */
static char *http_get(const char *url)
{
    CURL *curl = curl_easy_init();
    if (!curl)
        return NULL;

    struct HttpBuf buf = { malloc(1), 0 };
    if (!buf.data) {
        curl_easy_cleanup(curl);
        return NULL;
    }
    buf.data[0] = '\0';

    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, http_write_cb);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, &buf);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, 5L);
    curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
    curl_easy_setopt(curl, CURLOPT_USERAGENT, "csakura/" VERSION);

    long http_code = 0;
    CURLcode rc = curl_easy_perform(curl);
    if (rc == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
    curl_easy_cleanup(curl);

    if (rc != CURLE_OK || http_code < 200 || http_code >= 300) {
        free(buf.data);
        return NULL;
    }
    return buf.data;
}

/* Look for "key": <number> anywhere in json and parse it. Skips string
 * values (e.g. units blocks) so it won't misfire on a same-named field
 * that holds text instead of a number. */
static bool json_num(const char *json, const char *key, double *out)
{
    char pat[64];
    snprintf(pat, sizeof(pat), "\"%s\":", key);
    const char *p = strstr(json, pat);
    if (!p)
        return false;
    p += strlen(pat);
    while (*p == ' ')
        p++;
    if (*p == '"')
        return false;
    *out = strtod(p, NULL);
    return true;
}

/* Look for "key": "string value" and copy it out. */
static bool json_str(const char *json, const char *key, char *out, size_t outlen)
{
    char pat[64];
    snprintf(pat, sizeof(pat), "\"%s\":", key);
    const char *p = strstr(json, pat);
    if (!p)
        return false;
    p += strlen(pat);
    while (*p == ' ')
        p++;
    if (*p != '"')
        return false;
    p++;
    const char *end = strchr(p, '"');
    if (!end)
        return false;
    size_t len = (size_t)(end - p);
    if (len >= outlen)
        len = outlen - 1;
    memcpy(out, p, len);
    out[len] = '\0';
    return true;
}

/* Maps a WMO weather_code (the vocabulary Open-Meteo uses) to a rain
 * intensity label. Falls back to a plain rain-amount check for codes
 * outside the rain/drizzle/storm family (e.g. clear sky, snow codes),
 * so a nonzero "rain" reading is never silently dropped. */
static const char *rain_category(int code, double rain_mm)
{
    switch (code) {
    case 51: case 53: case 55: case 56: case 57:
        return "llovizna";
    case 61: case 80:
        return "leve";
    case 63: case 81:
        return "moderada";
    case 65: case 82:
        return "fuerte";
    case 95:
        return "tormenta";
    case 96: case 99:
        return "tormenta con granizo";
    default:
        return rain_mm > 0.0 ? "si" : "no";
    }
}

/* Rough 0..1 severity used to drive raindrop count/speed — not meant to
 * be precise, just "drizzle should look thinner than a storm". */
static double rain_intensity_value(const char *cat)
{
    if (strcmp(cat, "llovizna") == 0)             return 0.30;
    if (strcmp(cat, "leve") == 0)                 return 0.45;
    if (strcmp(cat, "moderada") == 0)             return 0.65;
    if (strcmp(cat, "fuerte") == 0)                return 0.85;
    if (strcmp(cat, "tormenta") == 0)             return 1.00;
    if (strcmp(cat, "tormenta con granizo") == 0) return 1.00;
    if (strcmp(cat, "si") == 0)                   return 0.50; /* unknown code, rain>0 */
    return 0.0; /* "no" */
}

/* Same idea as rain_category(), for the snow-family WMO codes. */
static const char *snow_category(int code, double snow_mm)
{
    switch (code) {
    case 71: case 85:
        return "liviana";
    case 73:
        return "moderada";
    case 75: case 86:
        return "fuerte";
    case 77:
        return "granos";
    default:
        return snow_mm > 0.0 ? "si" : "no";
    }
}

static double snow_intensity_value(const char *cat)
{
    if (strcmp(cat, "liviana") == 0)  return 0.30;
    if (strcmp(cat, "moderada") == 0) return 0.55;
    if (strcmp(cat, "fuerte") == 0)   return 0.85;
    if (strcmp(cat, "granos") == 0)   return 0.35;
    if (strcmp(cat, "si") == 0)       return 0.45; /* unknown code, snow>0 */
    return 0.0; /* "no" */
}

static const char *weather_description(int code)
{
    switch (code) {
    case 0:  return "despejado";
    case 1:  return "mayormente despejado";
    case 2:  return "parcialmente nublado";
    case 3:  return "cubierto";
    case 45:
    case 48: return "niebla";
    case 51:
    case 53:
    case 55: return "llovizna";
    case 56:
    case 57: return "llovizna helada";
    case 61:
    case 63:
    case 65: return "lluvia";
    case 66:
    case 67: return "lluvia helada";
    case 71:
    case 73:
    case 75: return "nieve";
    case 77: return "granos de nieve";
    case 80:
    case 81:
    case 82: return "chubascos de lluvia";
    case 85:
    case 86: return "chubascos de nieve";
    case 95: return "tormenta";
    case 96:
    case 99: return "tormenta con granizo";
    default: return "clima desconocido";
    }
}

/* wind_speed_10m thresholds, in km/h */
static const char *WIND_LABELS[]  = { "sin viento", "ligero", "moderado", "fuerte" };
static const double WIND_FACTORS[] = { 0.15, 0.6, 1.3, 2.4 };

static int wind_bucket(double kmh)
{
    if (kmh < 2.0)  return 0;
    if (kmh < 20.0) return 1;
    if (kmh < 50.0) return 2;
    return 3;
}

/* Everything compute_weather() produces, kept out of the g_* globals so
 * it can be safely built on a background thread (pure function: only
 * touches its own locals/out, plus read-only opt_force* config). The
 * main thread applies it via apply_weather() once it's done. */
typedef struct {
    bool ok; /* false = network/parse failure; don't apply this result */
    bool night;
    bool raining;
    double rain_intensity;
    bool fog;
    bool snowing;
    double snow_intensity;
    double wind_factor;
    char line[256];
} WeatherResult;

static void compute_weather(WeatherResult *out)
{
    memset(out, 0, sizeof(*out));
    out->wind_factor = 1.0;

    /* debug override: skip the network entirely and just force the
     * day/night and/or rain visuals, so this can be iterated on without
     * waiting on ip-api.com / open-meteo each run */
    if (opt_force) {
        out->ok = true;
        out->night = (opt_force == 2);
        out->raining = (opt_force_rain == 1);
        out->rain_intensity = out->raining ? 0.75 : 0.0;
        out->fog = (opt_force_fog == 1);
        out->snowing = (opt_force_snow == 1);
        out->snow_intensity = out->snowing ? 0.7 : 0.0;
        if (opt_force_wind)
            out->wind_factor = WIND_FACTORS[opt_force_wind - 1];

        char windnote[32] = "";
        if (opt_force_wind)
            snprintf(windnote, sizeof(windnote), ", viento: %s",
                WIND_LABELS[opt_force_wind - 1]);

        snprintf(out->line, sizeof(out->line),
            " modo forzado: %s%s%s%s%s ",
            out->night ? "noche" : "dia",
            opt_force_rain ? (out->raining ? ", lluvia: si" : ", lluvia: no") : "",
            opt_force_fog  ? (out->fog     ? ", niebla: si" : ", niebla: no") : "",
            opt_force_snow ? (out->snowing ? ", nieve: si"  : ", nieve: no")  : "",
            windnote);
        return;
    }

    snprintf(out->line, sizeof(out->line), " clima: sin datos (sin conexion) ");

    char *geo = http_get("http://ip-api.com/json/?fields=status,city,lat,lon");
    if (!geo)
        return;

    char status[16] = "", city[64] = "?";
    double lat = 0.0, lon = 0.0;
    json_str(geo, "status", status, sizeof(status));
    json_str(geo, "city", city, sizeof(city));
    json_num(geo, "lat", &lat);
    json_num(geo, "lon", &lon);
    free(geo);

    if (strcmp(status, "success") != 0)
        return;

    char url[256];
    snprintf(url, sizeof(url),
        "https://api.open-meteo.com/v1/forecast?latitude=%.4f&longitude=%.4f"
        "&current=temperature_2m,precipitation,rain,snowfall,weather_code,wind_speed_10m,is_day",
        lat, lon);

    char *wx = http_get(url);
    if (!wx)
        return;

    /* jump past "current_units" so its string values don't get confused
     * with the numeric fields of the same name inside "current" */
    const char *cur = strstr(wx, "\"current\":");
    if (!cur) {
        free(wx);
        return;
    }

    double temp = 0.0, rain = 0.0, snow = 0.0, wind = 0.0, is_day = 1.0, code = 0.0;
    json_num(cur, "temperature_2m", &temp);
    json_num(cur, "rain", &rain);
    json_num(cur, "snowfall", &snow);
    json_num(cur, "weather_code", &code);
    json_num(cur, "wind_speed_10m", &wind);
    json_num(cur, "is_day", &is_day);
    free(wx);

    out->night = (is_day <= 0.5);

    const char *rcat = rain_category((int)code, rain);
    out->raining = (strcmp(rcat, "no") != 0);
    out->rain_intensity = rain_intensity_value(rcat);

    /* --force=rain|norain overrides just the animation, independent of
     * whatever day/night ended up being (real, since opt_force isn't
     * set on this path) — the debug line below still shows the real
     * reading, so you can see what got overridden. */
    if (opt_force_rain) {
        out->raining = (opt_force_rain == 1);
        out->rain_intensity = out->raining ? fmax(out->rain_intensity, 0.6) : 0.0;
    }

    out->fog = ((int)code == 45 || (int)code == 48);
    if (opt_force_fog)
        out->fog = (opt_force_fog == 1);

    const char *scat = snow_category((int)code, snow);
    out->snowing = (strcmp(scat, "no") != 0);
    out->snow_intensity = snow_intensity_value(scat);
    if (opt_force_snow) {
        out->snowing = (opt_force_snow == 1);
        out->snow_intensity = out->snowing ? fmax(out->snow_intensity, 0.5) : 0.0;
    }

    int wbucket = wind_bucket(wind);
    out->wind_factor = WIND_FACTORS[wbucket];
    if (opt_force_wind)
        out->wind_factor = WIND_FACTORS[opt_force_wind - 1];

    if (opt_debug) {
        snprintf(out->line, sizeof(out->line),
            " %s | %.1f°C | lluvia: %s | niebla: %s | nieve: %s | viento: %.1f km/h (%s) | sol: %s ",
            city, temp,
            rcat,
            out->fog ? "si" : "no",
            scat,
            wind, WIND_LABELS[wbucket],
            is_day > 0.5 ? "si" : "no");
    } else {
        snprintf(out->line, sizeof(out->line),
            " %s | %.1f°C | %s ",
            city, temp,
            weather_description((int)code));
    }

    out->ok = true;
}

/* Copies a successful result into the live globals everything else reads.
 * Only call this from the main thread — the background refresh thread
 * only ever touches its own WeatherResult, never these directly. */
static void apply_weather(const WeatherResult *wr)
{
    if (!wr->ok)
        return;

    g_night          = wr->night;
    g_raining        = wr->raining;
    g_rain_intensity = wr->rain_intensity;
    g_fog            = wr->fog;
    g_snowing        = wr->snowing;
    g_snow_intensity = wr->snow_intensity;
    g_wind_factor    = wr->wind_factor;
    snprintf(weather_line, sizeof(weather_line), "%s", wr->line);
}

/* ---- background weather refresh ------------------------------------------
 *
 * A detached thread re-runs compute_weather() every WEATHER_REFRESH_SECS
 * (location included — it's the same ip-api.com + open-meteo round trip
 * as the startup fetch) and hands the result to the main thread through
 * a small mutex-protected mailbox. The main loop drains it once per frame
 * via check_weather_update() and only then touches ncurses/g_* state, so
 * there's never more than one thread touching animation state. */
static pthread_mutex_t weather_mutex = PTHREAD_MUTEX_INITIALIZER;
static WeatherResult   weather_pending;
static bool            weather_pending_ready = false;

static void *weather_thread_main(void *arg)
{
    (void)arg;
    for (;;) {
        sleep(WEATHER_REFRESH_SECS);

        WeatherResult wr;
        compute_weather(&wr);
        if (!wr.ok) /* transient failure: keep whatever's showing, retry later */
            continue;

        pthread_mutex_lock(&weather_mutex);
        weather_pending = wr;
        weather_pending_ready = true;
        pthread_mutex_unlock(&weather_mutex);
    }
    return NULL;
}

/* defined later, alongside their gen_tree()-time counterparts — forward
 * declared here so check_weather_update() can resize the effect pools */
static void reset_rain(bool scatter);
static void reset_fog(void);
static void reset_snow(bool scatter);

/* Call once per frame from the main thread. Cheap no-op unless the
 * background thread just dropped off a fresh reading. */
static void check_weather_update(void)
{
    WeatherResult wr;
    bool has_update = false;

    pthread_mutex_lock(&weather_mutex);
    if (weather_pending_ready) {
        wr = weather_pending;
        weather_pending_ready = false;
        has_update = true;
    }
    pthread_mutex_unlock(&weather_mutex);

    if (!has_update)
        return;

    apply_weather(&wr);

    /* re-size the effect pools to match whatever changed — scatter=false
     * so new rain/snow eases in from the top instead of popping in fully
     * formed across the whole screen */
    reset_rain(false);
    reset_fog();
    reset_snow(false);
}

/* ---- colors ------------------------------------------------------------- */

enum {
    C_P0 = 1,                       /* blossom ramp: lightest ...       */
    C_P1, C_P2, C_P3, C_P4, C_P5, C_P6,
    C_P7,                           /* ... deepest                      */
    C_TRUNK_D, C_TRUNK_M, C_TRUNK_L,
    C_GRASS, C_FADED,
    C_STAR,                         /* night sky (stars only)            */
    C_RAIN,
    C_FOG,
    C_SNOW,
};

typedef struct {
    const char *name;
    short ramp[8];                  /* xterm-256 indices, light → deep  */
} Palette;

/* same set as the web version; indices approximate the hex ramps */
static const Palette PALETTES[] = {
    { "sakura",   { 225, 224, 218, 212, 211, 175, 168, 132 } },
    { "rose",     { 224, 218, 211, 204, 203, 161, 125,  88 } },
    { "blush",    { 225, 218, 217, 211, 210, 168, 131,  95 } },
    { "magenta",  { 219, 213, 207, 200, 163, 127,  90,  53 } },
    { "peach",    { 223, 216, 215, 209, 173, 130,  94,  58 } },
    { "coral",    { 217, 210, 209, 203, 167, 131,  88,  52 } },
    { "sunset",   { 223, 216, 209, 203, 167, 131,  88,  52 } },
    { "gold",     { 229, 222, 221, 179, 136,  94,  58,  52 } },
    { "lavender", { 189, 183, 147, 141, 140,  98,  61,  54 } },
    { "violet",   { 183, 177, 141, 135,  98,  91,  54,  53 } },
    { "sky",      { 153, 117, 111,  75,  68,  31,  25,  24 } },
    { "mint",     { 158, 122, 115,  79,  72,  35,  29,  22 } },
    { "matcha",   { 193, 150, 149, 107,  70,  64,  28,  22 } },
    { "white",    { 255, 225, 224, 218, 211, 175, 168, 132 } },
    { "ink",      { 255, 252, 251, 248, 245, 242, 239, 236 } },
};
#define NPALETTES ((int)(sizeof(PALETTES) / sizeof(PALETTES[0])))

static int find_palette(const char *name)
{
    for (int i = 0; i < NPALETTES; i++)
        if (strcmp(PALETTES[i].name, name) == 0)
            return i;
    return -1;
}

static void apply_palette(void)
{
    if (!has_colors())
        return;

    const Palette *p = &PALETTES[opt_palette];

    /* background always tracks the terminal's own theme (day/night is the
     * user's terminal's problem, not ours) — only foreground tones shift
     * for night, via the shade offset in gen_canopy() and A_DIM in draw() */
    if (COLORS >= 256) {
        for (int i = 0; i < 8; i++)
            init_pair((short)(C_P0 + i), p->ramp[i], -1);
        init_pair(C_TRUNK_D, 52,  -1);
        init_pair(C_TRUNK_M, 94,  -1);
        init_pair(C_TRUNK_L, 137, -1);
        init_pair(C_GRASS, 108, -1);
        init_pair(C_FADED, p->ramp[5], -1);
        init_pair(C_STAR, 253, -1);
        init_pair(C_RAIN, 74, -1);
        init_pair(C_FOG, 251, -1);
        init_pair(C_SNOW, 255, -1);
    } else {
        /* rough 8-color fallback — still cycleable, just less precise */
        short base = COLOR_MAGENTA;
        if (opt_palette == 7)  base = COLOR_YELLOW; /* gold */
        if (opt_palette == 10) base = COLOR_CYAN;   /* sky */
        if (opt_palette == 11 || opt_palette == 12) base = COLOR_GREEN;
        if (opt_palette == 14) base = COLOR_WHITE;  /* ink */

        init_pair(C_P0, COLOR_WHITE, -1);
        init_pair(C_P1, COLOR_WHITE, -1);
        for (int i = 2; i < 6; i++)
            init_pair((short)(C_P0 + i), base, -1);
        init_pair(C_P6, COLOR_RED, -1);
        init_pair(C_P7, COLOR_RED, -1);
        init_pair(C_TRUNK_D, COLOR_YELLOW, -1);
        init_pair(C_TRUNK_M, COLOR_YELLOW, -1);
        init_pair(C_TRUNK_L, COLOR_YELLOW, -1);
        init_pair(C_GRASS, COLOR_GREEN, -1);
        init_pair(C_FADED, base, -1);
        init_pair(C_STAR, COLOR_WHITE, -1);
        init_pair(C_RAIN, COLOR_CYAN, -1);
        init_pair(C_FOG, COLOR_WHITE, -1);
        init_pair(C_SNOW, COLOR_WHITE, -1);
    }
}

static void init_colors(void)
{
    start_color();
    use_default_colors(); /* keep the terminal's own background */
    apply_palette();
}

/* ---- glyph sets ----------------------------------------------------------- */

static const char *G_FULL   = "\u2588"; /* █ */
static const char *G_DARK   = "\u2593"; /* ▓ */
static const char *G_MED    = "\u2592"; /* ▒ */
static const char *G_DOT    = "\u00B7"; /* · */

static const char *bloom_uni[] = { "\u2740", "\u273F", "\u2741", "\u273D" };
static const char *bloom_asc[] = { "&", "%", "@", "*" };

static const char *petal_uni[] = { "\u2740", "\u273F", "*", "\u00B7", "\u2218" };
static const char *petal_asc[] = { "*", "*", "o", ".", "'" };

static const char *g_full(void) { return opt_ascii ? "@" : G_FULL; }
static const char *g_dark(void) { return opt_ascii ? "%" : G_DARK; }
static const char *g_med(void)  { return opt_ascii ? ":" : G_MED;  }

/* ---- grid ----------------------------------------------------------------- */

static void put(int x, int y, const char *glyph, short pair, bool bold)
{
    if (x < 0 || y < 0 || x >= gw || y >= gh)
        return;
    Cell *c = &grid[(size_t)y * gw + x];
    c->glyph = glyph;
    c->pair  = pair;
    c->bold  = bold;
}

/* ---- canopy field --------------------------------------------------------- */

static double field(double x, double y)
{
    double s = 0.0;
    for (int i = 0; i < nblobs; i++) {
        double dx = (x - blobs[i].x) / blobs[i].rx;
        double dy = (y - blobs[i].y) / blobs[i].ry;
        s += exp(-(dx * dx + dy * dy) * 2.2);
    }
    return s;
}

static void add_source(int x, int y)
{
    if (nsources < MAX_SOURCES) {
        sources[nsources].x = (short)x;
        sources[nsources].y = (short)y;
        nsources++;
    }
}

static void gen_canopy(double cx, double cy, double rx, double ry)
{
    const char **blooms = opt_ascii ? bloom_asc : bloom_uni;

    /* bounds of the actual blossom clouds, not the nominal crown */
    double bx0 = 1e9, bx1 = -1e9, by0 = 1e9, by1 = -1e9;
    for (int i = 0; i < nblobs; i++) {
        if (blobs[i].x - blobs[i].rx < bx0) bx0 = blobs[i].x - blobs[i].rx;
        if (blobs[i].x + blobs[i].rx > bx1) bx1 = blobs[i].x + blobs[i].rx;
        if (blobs[i].y - blobs[i].ry < by0) by0 = blobs[i].y - blobs[i].ry;
        if (blobs[i].y + blobs[i].ry > by1) by1 = blobs[i].y + blobs[i].ry;
    }
    int x0 = (int)(bx0 - 3), x1 = (int)(bx1 + 3);
    int y0 = (int)(by0 - 2), y1 = (int)(by1 + 3);

    /* shade against the real vertical extent of the clouds */
    cy = (by0 + by1) / 2.0;
    ry = fmax((by1 - by0) / 2.0, 2.0);
    (void)cx; (void)rx;

    for (int y = y0; y <= y1; y++) {
        if (y < 0 || y >= gh) continue;
        for (int x = x0; x <= x1; x++) {
            if (x < 0 || x >= gw) continue;

            double f = field(x, y);
            if (f < 0.30)
                continue;

            /* scalloped, airy outline */
            if (f < 0.42 && frand() < 0.35)
                continue;

            /* vertical position inside the crown drives the base tone */
            double h = clampd((y - (cy - ry)) / (2.0 * ry), 0.0, 1.0);

            /* slightly open underside so the branches peek through */
            if (h > 0.62 && f < 0.85) {
                double openness = (h - 0.62) * 1.3;
                if (frand() < openness)
                    continue;
            }

            double shade = h * 6.0 + frange(-0.9, 0.9);

            /* per-lump shading: bright tops, shadowed undersides */
            double fu = field(x, y - 1.6);
            if (fu > f * 1.12) shade += 1.7;
            else if (fu < f * 0.88) shade -= 1.5;

            const char *g;
            bool bold = false;
            if (f > 0.92)
                g = frand() < 0.80 ? g_full() : g_dark();
            else if (f > 0.55)
                g = frand() < 0.60 ? g_dark() : g_med();
            else {
                double r = frand();
                if (r < 0.45)      g = g_med();
                else if (r < 0.85) g = blooms[rand() % 4];
                else               g = opt_ascii ? "." : G_DOT;
                bold = !g_night && frand() < 0.3;
            }

            /* blossom sparkle on the surface (dimmer and rarer at night,
             * so it doesn't compete with the stars) */
            if (f > 0.55 && frand() < (g_night ? 0.02 : 0.07)) {
                g = blooms[rand() % 4];
                bold = !g_night;
                shade -= 2.0;
            }

            /* muted, deeper tones under a night sky */
            if (g_night)
                shade += 2.2;

            int idx = (int)clampd(shade, 0.0, 7.0);
            put(x, y, g, (short)(C_P0 + idx), bold);

            /* petals detach from edges and lump undersides */
            if ((f < 0.60 || fu > f * 1.12) && frand() < 0.5)
                add_source(x, y);
        }
    }
}

/* ---- trunk & limbs --------------------------------------------------------- */

static void gen_trunk(double bx, double tx, double ty)
{
    double base_y = gh - 2.0;
    double h = base_y - ty;
    if (h < 2.0) h = 2.0;

    double maxw = clampd(gw * 0.028, 2.0, 5.0);
    double bend = frange(-1.0, 1.0) * clampd(gw * 0.02, 1.0, 4.0);

    int steps = (int)(h * 2.0) + 2;
    for (int i = 0; i <= steps; i++) {
        double t = (double)i / steps;
        double y = base_y - t * h;
        double x = bx + (tx - bx) * t + sin(t * M_PI) * bend;

        /* taper upward, flare at the roots */
        double w = maxw * pow(1.0 - t, 1.10) * (1.0 + 1.1 * exp(-t * 10.0)) + 0.6;

        for (int dx = (int)-w; dx <= (int)w; dx++) {
            short pair;
            if (dx < -w * 0.35)     pair = C_TRUNK_D;
            else if (dx > w * 0.45) pair = C_TRUNK_L;
            else                    pair = C_TRUNK_M;
            put((int)(x + dx), (int)y, g_full(), pair, false);
        }
    }
}

/* recursive branch skeleton; tips are collected so blossom clouds can
 * grow exactly where the branches end. Branches are kept inside the
 * crown box so nothing climbs off-screen or into the margins. */
static Coord tips[64];
static int ntips = 0;
static double br_xmin, br_xmax, br_ymin;

static void gen_branch(double x, double y, double angle, double len, int depth)
{
    double t = 0.0;

    while (t < len) {
        double dx = cos(angle), dy = sin(angle);
        x += dx * 1.7;
        y -= dy * 0.85;
        t += 1.0;
        angle += frange(-0.10, 0.10);
        angle = clampd(angle, 0.15, M_PI - 0.15);

        /* bounce off the crown box instead of leaving it */
        if (x < br_xmin) { x = br_xmin; angle = M_PI - angle; }
        if (x > br_xmax) { x = br_xmax; angle = M_PI - angle; }
        if (y < br_ymin) { /* go flat near the crown top */
            y = br_ymin;
            angle = angle > M_PI / 2.0 ? M_PI - 0.20 : 0.20;
        }

        put((int)x, (int)y, g_full(), depth == 0 ? C_TRUNK_M : C_TRUNK_L, false);
        if (depth == 0) { /* main limbs are two cells thick */
            put((int)x + 1, (int)y, g_full(), C_TRUNK_D, false);
        } else if (frand() < 0.35) {
            put((int)x + (frand() < 0.5 ? -1 : 1), (int)y, g_full(), C_TRUNK_M, false);
        }
    }

    if (depth >= 2 || len < 3.0) {
        if (ntips < 64) {
            tips[ntips].x = (short)x;
            tips[ntips].y = (short)y;
            ntips++;
        }
        return;
    }

    int kids = 2 + (frand() < 0.5 ? 1 : 0);
    for (int i = 0; i < kids; i++) {
        double spread = frange(0.40, 0.80);
        double na = i == 0 ? angle + spread
                  : i == 1 ? angle - spread
                  : angle + frange(-0.25, 0.25);
        gen_branch(x, y, na, len * frange(0.55, 0.75), depth + 1);
    }
}

/* ---- ground ----------------------------------------------------------------- */

static void gen_ground(double cx, double rx)
{
    const char **blooms = opt_ascii ? bloom_asc : bloom_uni;
    int y = gh - 1;

    for (int x = 0; x < gw; x++) {
        double dx = (x - cx) / (rx * 1.25);
        double p = exp(-dx * dx * 2.2); /* petal carpet under the crown */
        double r = frand();

        if (r < p * 0.50) {
            double rr = frand();
            const char *g = rr < 0.25 ? blooms[rand() % 4]
                          : rr < 0.60 ? (opt_ascii ? "." : G_DOT)
                          : ",";
            put(x, y, g, (short)(C_P3 + rand() % 4), false);
        } else if (r < p * 0.50 + 0.10) {
            put(x, y, "\"", C_GRASS, false);
        } else if (r < p * 0.50 + 0.16) {
            put(x, y, ",", C_GRASS, false);
        } else {
            put(x, y, "_", C_GRASS, false);
        }

        /* a few strays on the row above */
        if (gh > 3 && frand() < p * 0.12)
            put(x, y - 1, opt_ascii ? "." : G_DOT, C_FADED, false);
    }
}

/* ---- night sky (stars) ---------------------------------------------------------- */

/* Scattered once per regrow, only when g_night is set. Drawn underneath
 * the tree grid, so canopy/trunk/ground glyphs simply paint over them. */
static void gen_stars(void)
{
    nstars = 0;
    if (!g_night)
        return;

    int want = (gw * gh) / 90;
    if (want > MAX_STARS)
        want = MAX_STARS;

    for (int i = 0; i < want; i++) {
        stars[nstars].x = (short)(frand() * gw);
        stars[nstars].y = (short)(frand() * fmax(1.0, gh - 2.0));
        nstars++;
    }
}

/* ---- tree ---------------------------------------------------------------------- */

static void gen_tree(void)
{
    memset(grid, 0, sizeof(Cell) * (size_t)gw * gh);
    nsources = 0;
    nblobs = 0;
    ntips = 0;
    gen_stars();

    /* crown geometry: centred, with clear margins on every side */
    double rx = clampd(gw * 0.26, 6.0, 36.0);
    double ry = clampd(gh * 0.26, 3.0, rx * 0.55);
    double cx = gw * 0.5 + frange(-1.5, 1.5);
    double cy = ry + 2.5; /* crown top sits just below the screen edge */

    /* trunk forks below the crown so the branch fan stays visible */
    double bx = cx + frange(-2.0, 2.0);
    double tx = cx + frange(-2.0, 2.0);
    double ty = cy + ry * 1.15;
    if (ty > gh - 4.0) ty = gh - 4.0;

    /* branches must stay inside this box (tip clouds add ~ry*0.4 on top) */
    br_xmin = cx - rx * 0.80;
    br_xmax = cx + rx * 0.80;
    br_ymin = fmax(1.0, cy - ry * 0.55);

    gen_ground(cx, rx); /* first, so the tree overdraws it */
    gen_trunk(bx, tx, ty);

    /* branch skeleton fans out of the trunk top; remember the tips */
    int limbs = 3 + rand() % 2;
    double reach = (ty - br_ymin) * 0.60 + 2.0;
    for (int i = 0; i < limbs; i++) {
        double na = M_PI / 2.0
                  + (i - (limbs - 1) / 2.0) * frange(0.55, 0.75)
                  + frange(-0.15, 0.15);
        gen_branch(tx + frange(-1.0, 1.0), ty + frange(0.0, 1.5),
                   na, reach * frange(0.75, 1.0), 0);
    }

    /* blossom clouds grow on the branch tips, plus a soft core */
    blobs[nblobs++] = (Blob){ cx, cy - ry * 0.10, rx * 0.50, ry * 0.50 };
    for (int i = 0; i < ntips && nblobs < MAX_BLOBS - 4; i++) {
        blobs[nblobs++] = (Blob){
            tips[i].x + frange(-1.5, 1.5),
            tips[i].y - frange(0.0, 1.5),
            rx * frange(0.18, 0.30),
            ry * frange(0.24, 0.38),
        };
    }

    /* clusters hanging into the lower crown, branches peek between */
    for (int i = 0; i < 5 && nblobs < MAX_BLOBS; i++) {
        blobs[nblobs++] = (Blob){
            cx + frange(-0.70, 0.70) * rx,
            cy + frange(0.25, 0.60) * ry,
            rx * frange(0.18, 0.28),
            ry * frange(0.24, 0.34),
        };
    }

    gen_canopy(cx, cy, rx, ry); /* canopy overdraws branch tops */
}

/* ---- petals ---------------------------------------------------------------------- */

static void spawn_petal(Petal *p, bool scatter)
{
    const char **glyphs = opt_ascii ? petal_asc : petal_uni;

    p->active = true;
    p->rest   = -1.0;

    if (nsources > 0 && frand() < 0.85) {
        Coord c = sources[rand() % nsources];
        p->x = c.x + frange(-1.0, 1.0);
        p->y = c.y + frange(0.0, 1.0);
    } else {
        p->x = frand() * gw;
        p->y = -frange(0.0, 3.0);
    }
    if (scatter) /* initial fill so the screen isn't empty at startup */
        p->y = frange(0.0, gh - 2.0);

    p->vy    = frange(0.10, 0.28);
    p->amp   = frange(0.10, 0.45);
    p->freq  = frange(0.05, 0.18);
    p->phase = frand() * 2.0 * M_PI;
    p->glyph = glyphs[rand() % 5];
    p->pair  = (short)(C_P1 + rand() % 5);
}

static void reset_petals(bool scatter)
{
    npetals = gw * opt_density / 4;
    if (npetals < 16)          npetals = 16;
    if (npetals > MAX_PETALS)  npetals = MAX_PETALS;

    for (int i = 0; i < MAX_PETALS; i++)
        petals[i].active = false;
    for (int i = 0; i < npetals; i++)
        if (frand() < 0.6)
            spawn_petal(&petals[i], scatter);
}

static void update_petals(double dt)
{
    /* wind wanders slowly, biased to the right, with occasional gusts;
     * g_wind_factor scales it by the real (or forced) wind category */
    if (frand() < 0.008)
        wind_target = frange(-0.12, 0.45) * opt_wind * g_wind_factor;
    wind += (wind_target - wind) * 0.02;

    for (int i = 0; i < npetals; i++) {
        Petal *p = &petals[i];

        if (!p->active) { /* trickle respawns so it never pulses */
            if (frand() < 0.03)
                spawn_petal(p, false);
            continue;
        }

        if (p->rest >= 0.0) { /* lying on the ground */
            p->rest -= dt;
            if (p->rest < 0.0)
                p->active = false;
            continue;
        }

        p->phase += p->freq;
        p->x += wind + p->amp * sin(p->phase);
        p->y += p->vy;

        if (p->x < -2.0)          p->x = gw + 1.0;
        else if (p->x > gw + 2.0) p->x = -1.0;

        if (p->y >= gh - 1.0) { /* touched down */
            p->y    = gh - 1.0;
            p->rest = frange(2.0, 7.0);
            p->pair = C_FADED;
            p->glyph = opt_ascii ? "." : G_DOT;
        }
    }
}

/* ---- rain ---------------------------------------------------------------------- */

static void spawn_raindrop(Raindrop *d, bool scatter)
{
    d->x  = frand() * gw;
    d->y  = scatter ? frange(0.0, gh - 1.0) : -frange(0.0, 2.0);
    /* heavier rain falls faster, not just denser */
    d->vy = frange(1.1, 1.6) * (0.6 + 0.6 * g_rain_intensity);
}

/* Sizes and (re)fills the raindrop pool. Only needs re-running when the
 * terminal resizes (gw changed) — intensity/g_raining don't change
 * mid-run, so 'r'/'c'/'C' don't need to touch this. */
static void reset_rain(bool scatter)
{
    nrain = 0;
    if (!g_raining)
        return;

    int want = (int)(gw * (0.5 + 1.5 * g_rain_intensity));
    if (want < 8)        want = 8;
    if (want > MAX_RAIN) want = MAX_RAIN;

    nrain = want;
    for (int i = 0; i < nrain; i++)
        spawn_raindrop(&raindrops[i], scatter);
}

static void update_rain(void)
{
    if (!g_raining)
        return;

    for (int i = 0; i < nrain; i++) {
        Raindrop *d = &raindrops[i];

        /* same wind petals use, but raindrops fall much faster (higher
         * vy) so they need a stronger horizontal push to show the same
         * visual lean angle — this is what makes strong wind look like
         * it's actually blowing the rain sideways, not just petals */
        d->x += wind * 1.4;
        d->y += d->vy;

        if (d->x < -1.0)          d->x = gw + 1.0;
        else if (d->x > gw + 1.0) d->x = -1.0;

        if (d->y >= gh) { /* recycle from the top */
            d->y = -frange(0.0, 2.0);
            d->x = frand() * gw;
        }
    }
}

/* ---- fog ---------------------------------------------------------------------- */

/* Ground-hugging haze: sparse, wide, slow-drifting patches, biased toward
 * the lower part of the screen. Same resize-only regen policy as rain. */
static void reset_fog(void)
{
    nfog = 0;
    if (!g_fog)
        return;

    int want = (gw * gh) / 140;
    if (want < 10)       want = 10;
    if (want > MAX_FOG)  want = MAX_FOG;

    nfog = want;
    for (int i = 0; i < nfog; i++) {
        fog[i].x     = frand() * gw;
        fog[i].y     = gh * frange(0.35, 1.0);
        fog[i].width = 2 + rand() % 4;

        /* wind nudges the drift a bit, but fog should stay slow even in
         * a strong blow — clamp how much g_wind_factor can push it */
        double wgust = clampd(g_wind_factor, 0.5, 1.6);
        fog[i].vx = frange(-0.05, 0.05) * wgust;
        if (fabs(fog[i].vx) < 0.015) /* keep it drifting, never fully still */
            fog[i].vx = (fog[i].vx < 0.0) ? -0.015 : 0.015;
    }
}

static void update_fog(void)
{
    if (!g_fog)
        return;

    for (int i = 0; i < nfog; i++) {
        fog[i].x += fog[i].vx;
        if (fog[i].x < -(double)fog[i].width)      fog[i].x = gw + 1.0;
        else if (fog[i].x > gw + 1.0)               fog[i].x = -(double)fog[i].width;
    }
}

/* ---- snow ---------------------------------------------------------------------- */

static void spawn_snowflake(Snowflake *s, bool scatter)
{
    s->x    = frand() * gw;
    s->y    = scatter ? frange(0.0, gh - 2.0) : -frange(0.0, 2.0);
    s->vy   = frange(0.05, 0.14) * (0.6 + 0.6 * g_snow_intensity); /* slower than petals */
    s->amp  = frange(0.15, 0.5);
    s->freq = frange(0.03, 0.10);
    s->phase = frand() * 2.0 * M_PI;
    s->rest = -1.0;
}

/* Same resize-only regen policy as rain/fog — intensity doesn't change
 * mid-run, so 'r'/'c'/'C' don't need to touch this either. */
static void reset_snow(bool scatter)
{
    nsnow = 0;
    if (!g_snowing)
        return;

    int want = (int)(gw * (0.4 + 1.2 * g_snow_intensity));
    if (want < 8)        want = 8;
    if (want > MAX_SNOW) want = MAX_SNOW;

    nsnow = want;
    for (int i = 0; i < nsnow; i++)
        spawn_snowflake(&snowflakes[i], scatter);
}

static void update_snow(double dt)
{
    if (!g_snowing)
        return;

    for (int i = 0; i < nsnow; i++) {
        Snowflake *s = &snowflakes[i];

        if (s->rest >= 0.0) { /* settled on the ground for a while */
            s->rest -= dt;
            if (s->rest < 0.0)
                spawn_snowflake(s, false); /* recycle from the top */
            continue;
        }

        s->phase += s->freq;
        s->x += wind * 0.4 + s->amp * sin(s->phase); /* drifts less than rain */
        s->y += s->vy;

        if (s->x < -2.0)          s->x = gw + 1.0;
        else if (s->x > gw + 2.0) s->x = -1.0;

        if (s->y >= gh - 1.0) {
            s->y    = gh - 1.0;
            s->rest = frange(3.0, 8.0);
        }
    }
}

/* ---- drawing ---------------------------------------------------------------------- */

static void draw(void)
{
    erase();

    if (g_night) {
        attr_t sa = COLOR_PAIR(C_STAR);
        attron(sa);
        for (int i = 0; i < nstars; i++)
            mvaddstr(stars[i].y, stars[i].x, opt_ascii ? "." : G_DOT);
        attroff(sa);
    }

    for (int y = 0; y < gh; y++) {
        for (int x = 0; x < gw; x++) {
            const Cell *c = &grid[(size_t)y * gw + x];
            if (!c->glyph)
                continue;
            /* bold cells (highlights, sparkles) stay at full brightness;
             * everything else dims a touch under a night sky */
            attr_t night = (g_night && !c->bold) ? A_DIM : 0;
            attr_t a = COLOR_PAIR(c->pair) | (c->bold ? A_BOLD : 0) | night;
            attron(a);
            mvaddstr(y, x, c->glyph);
            attroff(a);
        }
    }

    for (int i = 0; i < npetals; i++) {
        const Petal *p = &petals[i];
        if (!p->active)
            continue;
        int px = (int)p->x, py = (int)p->y;
        if (px < 0 || px >= gw || py < 0 || py >= gh)
            continue;
        attr_t a = COLOR_PAIR(p->pair) | (g_night ? A_DIM : 0);
        attron(a);
        mvaddstr(py, px, p->glyph);
        attroff(a);
    }

    if (g_fog) {
        attr_t fa = COLOR_PAIR(C_FOG) | A_DIM;
        attron(fa);
        for (int i = 0; i < nfog; i++) {
            int fy = (int)fog[i].y;
            if (fy < 0 || fy >= gh)
                continue;
            int fx0 = (int)fog[i].x;
            for (int w = 0; w < fog[i].width; w++) {
                int fx = fx0 + w;
                if (fx < 0 || fx >= gw)
                    continue;
                mvaddstr(fy, fx, opt_ascii ? "~" : "░");
            }
        }
        attroff(fa);
    }

    if (g_raining) {
        /* leans with the wind — vertical when calm, diagonal past a
         * threshold, so a strong blow visibly slants the whole rain */
        const char *streak;
        if (wind > 0.15)      streak = opt_ascii ? "\\" : "╲";
        else if (wind < -0.15) streak = opt_ascii ? "/"  : "╱";
        else                   streak = opt_ascii ? "|"  : "│";

        attr_t ra = COLOR_PAIR(C_RAIN) | (g_night ? A_DIM : 0);
        attron(ra);
        for (int i = 0; i < nrain; i++) {
            int rx = (int)raindrops[i].x, ry = (int)raindrops[i].y;
            if (rx < 0 || rx >= gw || ry < 0 || ry >= gh)
                continue;
            mvaddstr(ry, rx, streak);
        }
        attroff(ra);
    }

    if (g_snowing) {
        attr_t na = COLOR_PAIR(C_SNOW) | (g_night ? A_DIM : 0);
        attron(na);
        for (int i = 0; i < nsnow; i++) {
            const Snowflake *s = &snowflakes[i];
            int sx = (int)s->x, sy = (int)s->y;
            if (sx < 0 || sx >= gw || sy < 0 || sy >= gh)
                continue;
            mvaddstr(sy, sx, s->rest >= 0.0 ? (opt_ascii ? "." : G_DOT)
                                             : "*");
        }
        attroff(na);
    }

    /* debug: dump the weather data at the foot of the tree */
    if (weather_line[0]) {
        attr_t a = A_BOLD | A_REVERSE;
        attron(a);
        mvaddnstr(gh - 1, 0, weather_line, gw);
        attroff(a);
    }

    refresh();
}

/* ---- main ---------------------------------------------------------------------- */

static void resize_grid(void)
{
    gw = COLS;
    gh = LINES;
    free(grid);
    grid = calloc((size_t)gw * gh, sizeof(Cell));
    if (!grid) {
        endwin();
        fprintf(stderr, "csakura: out of memory\n");
        exit(1);
    }
}

static void usage(FILE *out)
{
    fprintf(out,
        "usage: csakura [options]\n"
        "\n"
        "a sakura tree with falling petals for your terminal\n"
        "\n"
        "options:\n"
        "  -f FPS    frames per second, 5-60 (default: 20)\n"
        "  -p NUM    petal density, 1-10 (default: 5)\n"
        "  -w NUM    wind strength, 0-10 (default: 1)\n"
        "  -c NAME   blossom palette (default: sakura)\n"
        "  -a        ASCII glyphs only (no unicode blossoms)\n"
        "  -d, --debug show detailed weather diagnostics at the bottom\n"
        "      --force=day|night|rain|norain|fog|nofog|snow|nosnow|\n"
        "              calm|light|moderate|strong[,...]\n"
        "            skip/override the weather fetch (debug); comma-separate\n"
        "            to combine, e.g. --force=night,snow,strong\n"
        "  -h        show this help\n"
        "  -v        show version\n"
        "\n"
        "palettes:\n"
        "  ");
    for (int i = 0; i < NPALETTES; i++) {
        fprintf(out, "%s%s", PALETTES[i].name, i + 1 < NPALETTES ? ", " : "\n");
        if ((i + 1) % 5 == 0 && i + 1 < NPALETTES)
            fprintf(out, "\n  ");
    }
    fprintf(out,
        "\n"
        "keys:\n"
        "  q / Esc   quit\n"
        "  r         regrow the tree\n"
        "  c         next color palette\n"
        "  C         previous color palette\n");
}

int main(int argc, char **argv)
{
    static const struct option long_opts[] = {
        { "force", required_argument, NULL, 'F' },
        { "debug", no_argument,       NULL, 'd' },
        { NULL, 0, NULL, 0 },
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "f:p:w:c:ahvd", long_opts, NULL)) != -1) {
        switch (opt) {
        case 'd':
            opt_debug = true;
            break;
        case 'f':
            opt_fps = atoi(optarg);
            if (opt_fps < 5)  opt_fps = 5;
            if (opt_fps > 60) opt_fps = 60;
            break;
        case 'p':
            opt_density = atoi(optarg);
            if (opt_density < 1)  opt_density = 1;
            if (opt_density > 10) opt_density = 10;
            break;
        case 'w':
            opt_wind = atof(optarg);
            if (opt_wind < 0.0)  opt_wind = 0.0;
            if (opt_wind > 10.0) opt_wind = 10.0;
            break;
        case 'c': {
            int idx = find_palette(optarg);
            if (idx < 0) {
                fprintf(stderr, "csakura: unknown palette '%s'\n", optarg);
                fprintf(stderr, "try: ");
                for (int i = 0; i < NPALETTES; i++)
                    fprintf(stderr, "%s%s", PALETTES[i].name,
                            i + 1 < NPALETTES ? ", " : "\n");
                return 1;
            }
            opt_palette = idx;
            break;
        }
        case 'a':
            opt_ascii = true;
            break;
        case 'F': {
            char buf[128];
            snprintf(buf, sizeof(buf), "%s", optarg);

            bool bad = false;
            for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) {
                if (strcmp(tok, "day") == 0)          opt_force = 1;
                else if (strcmp(tok, "night") == 0)   opt_force = 2;
                else if (strcmp(tok, "rain") == 0)    opt_force_rain = 1;
                else if (strcmp(tok, "norain") == 0)  opt_force_rain = 2;
                else if (strcmp(tok, "fog") == 0)     opt_force_fog = 1;
                else if (strcmp(tok, "nofog") == 0)   opt_force_fog = 2;
                else if (strcmp(tok, "calm") == 0)      opt_force_wind = 1;
                else if (strcmp(tok, "light") == 0)     opt_force_wind = 2;
                else if (strcmp(tok, "moderate") == 0)  opt_force_wind = 3;
                else if (strcmp(tok, "strong") == 0)    opt_force_wind = 4;
                else if (strcmp(tok, "snow") == 0)      opt_force_snow = 1;
                else if (strcmp(tok, "nosnow") == 0)    opt_force_snow = 2;
                else { bad = true; break; }
            }
            if (bad) {
                fprintf(stderr,
                    "csakura: --force values must be day, night, rain, "
                    "norain, fog, nofog, snow, nosnow, calm, light, "
                    "moderate, or strong (got '%s')\n", optarg);
                return 1;
            }
            break;
        }
        case 'v':
            printf("csakura %s\n", VERSION);
            return 0;
        case 'h':
            usage(stdout);
            return 0;
        default:
            usage(stderr);
            return 1;
        }
    }

    setlocale(LC_ALL, "");
    srand((unsigned)(time(NULL) ^ getpid()));

    signal(SIGINT, on_signal);
    signal(SIGTERM, on_signal);

    /* fetch once, before curses takes over the terminal, so the blocking
     * network calls don't happen mid-animation */
    curl_global_init(CURL_GLOBAL_DEFAULT);

    WeatherResult wr0;
    compute_weather(&wr0);
    apply_weather(&wr0);
    if (!wr0.ok)
        snprintf(weather_line, sizeof(weather_line), " clima: sin datos (sin conexion) ");

    /* background refresh: location, weather and every effect derived from
     * it all get re-checked every WEATHER_REFRESH_SECS, without blocking
     * the animation loop — check_weather_update() picks up the result */
    pthread_t weather_tid;
    if (pthread_create(&weather_tid, NULL, weather_thread_main, NULL) == 0)
        pthread_detach(weather_tid);

    initscr();
    noecho();
    cbreak();
    curs_set(0);
    keypad(stdscr, TRUE);
    nodelay(stdscr, TRUE);

    if (has_colors())
        init_colors();

    resize_grid();
    gen_tree();
    reset_petals(true);
    reset_rain(true);
    reset_fog();
    reset_snow(true);

    const double dt = 1.0 / opt_fps;

    while (running) {
        int ch = getch();
        if (ch == 'q' || ch == 'Q' || ch == 27)
            break;
        if (ch == 'r' || ch == 'R') {
            gen_tree();
            reset_petals(false);
        }
        if (ch == 'c') {
            opt_palette = (opt_palette + 1) % NPALETTES;
            apply_palette();
            gen_tree();
            reset_petals(false);
        }
        if (ch == 'C') {
            opt_palette = (opt_palette + NPALETTES - 1) % NPALETTES;
            apply_palette();
            gen_tree();
            reset_petals(false);
        }
        if (ch == KEY_RESIZE) {
            resize_grid();
            gen_tree();
            reset_petals(true);
            reset_rain(true);
            reset_fog();
            reset_snow(true);
        }

        check_weather_update();
        update_petals(dt);
        update_rain();
        update_fog();
        update_snow(dt);
        draw();
        napms(1000 / opt_fps);
    }

    endwin();
    free(grid);
    curl_global_cleanup();
    return 0;
}
