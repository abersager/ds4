/* ds4-ui -- a friendly terminal UI for ds4.
 *
 * It replaces the script-driven workflow with a single full-screen TUI that:
 *   1. manages model downloads (wraps ./download_model.sh)
 *   2. starts/stops the local ./ds4-server
 *   3. wires Claude Code to the local server, and cleanly restores Claude Code
 *      to normal when the server stops or the UI exits.
 *
 * It is deliberately lightweight: no inference, no GPU code, no model loading.
 * Just libc + a small TUI. The raw-mode / signal-restore scaffold mirrors the
 * pattern used by ds4_eval.c.
 */

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>

/* ----------------------------------------------------------------------- */
/* ANSI helpers (same palette as ds4_eval.c).                              */
/* ----------------------------------------------------------------------- */

#define ANSI_RESET "\x1b[0m"
#define ANSI_DIM "\x1b[90m"
#define ANSI_RED "\x1b[31m"
#define ANSI_GREEN "\x1b[32m"
#define ANSI_YELLOW "\x1b[33m"
#define ANSI_BLUE "\x1b[34m"
#define ANSI_CYAN "\x1b[36m"
#define ANSI_BOLD "\x1b[1m"
#define ANSI_REV "\x1b[7m"

/* ----------------------------------------------------------------------- */
/* Small dynamic string buffer.                                            */
/* ----------------------------------------------------------------------- */

typedef struct {
    char *p;
    size_t len, cap;
} sbuf;

static void sb_reserve(sbuf *b, size_t add) {
    if (b->len + add + 1 <= b->cap) return;
    size_t cap = b->cap ? b->cap : 256;
    while (b->len + add + 1 > cap) cap *= 2;
    char *np = realloc(b->p, cap);
    if (!np) { perror("realloc"); exit(1); }
    b->p = np;
    b->cap = cap;
}
static void sb_put(sbuf *b, const char *s, size_t n) {
    sb_reserve(b, n);
    memcpy(b->p + b->len, s, n);
    b->len += n;
    b->p[b->len] = 0;
}
static void sb_puts(sbuf *b, const char *s) { sb_put(b, s, strlen(s)); }
static void sb_putc(sbuf *b, char c) { sb_put(b, &c, 1); }
static void sb_free(sbuf *b) { free(b->p); b->p = NULL; b->len = b->cap = 0; }

/* Append `s` as a JSON string literal, escaping the minimum required set. */
static void sb_json_str(sbuf *b, const char *s) {
    sb_putc(b, '"');
    for (; *s; s++) {
        unsigned char c = (unsigned char)*s;
        switch (c) {
        case '"':  sb_puts(b, "\\\""); break;
        case '\\': sb_puts(b, "\\\\"); break;
        case '\n': sb_puts(b, "\\n"); break;
        case '\r': sb_puts(b, "\\r"); break;
        case '\t': sb_puts(b, "\\t"); break;
        default:
            if (c < 0x20) {
                char tmp[8];
                snprintf(tmp, sizeof(tmp), "\\u%04x", c);
                sb_puts(b, tmp);
            } else {
                sb_putc(b, (char)c);
            }
        }
    }
    sb_putc(b, '"');
}

/* ----------------------------------------------------------------------- */
/* Tiny JSON scanner (only what we need to edit ~/.claude/settings.json).   */
/* We never reserialize members we do not understand: their raw bytes are   */
/* preserved verbatim, so user hooks/permissions/theme are untouched.       */
/* ----------------------------------------------------------------------- */

typedef struct {
    char key[160];
    const char *vstart;
    size_t vlen;
} jmember;

static const char *js_ws(const char *p) {
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;
    return p;
}
static const char *js_str_end(const char *p) { /* p at opening quote */
    p++;
    while (*p) {
        if (*p == '\\') { if (!p[1]) return NULL; p += 2; continue; }
        if (*p == '"') return p + 1;
        p++;
    }
    return NULL;
}
static const char *js_val_end(const char *p) {
    p = js_ws(p);
    if (*p == '"') return js_str_end(p);
    if (*p == '{' || *p == '[') {
        char open = *p, close = (open == '{') ? '}' : ']';
        int depth = 0;
        while (*p) {
            if (*p == '"') { const char *e = js_str_end(p); if (!e) return NULL; p = e; continue; }
            if (*p == open) depth++;
            else if (*p == close) { depth--; if (depth == 0) return p + 1; }
            p++;
        }
        return NULL;
    }
    const char *s = p;
    while (*p && *p != ',' && *p != '}' && *p != ']' &&
           *p != ' ' && *p != '\t' && *p != '\n' && *p != '\r')
        p++;
    return p > s ? p : NULL;
}

/* Unescape a JSON string [qopen..) into dst (best effort, common escapes). */
static void js_key_copy(const char *qopen, const char *qclose, char *dst, size_t dstsz) {
    const char *p = qopen + 1;          /* skip opening quote */
    const char *end = qclose - 1;       /* closing quote */
    size_t i = 0;
    while (p < end && i + 1 < dstsz) {
        if (*p == '\\' && p + 1 < end) {
            p++;
            char c = *p;
            switch (c) {
            case 'n': c = '\n'; break;
            case 't': c = '\t'; break;
            case 'r': c = '\r'; break;
            default: break; /* \" \\ \/ etc -> literal next char */
            }
            dst[i++] = c;
            p++;
        } else {
            dst[i++] = *p++;
        }
    }
    dst[i] = 0;
}

/* Parse the members of the object whose span starts at objstart ('{'). */
static int js_members(const char *objstart, jmember *out, int maxn) {
    const char *p = js_ws(objstart);
    if (*p != '{') return -1;
    p = js_ws(p + 1);
    if (*p == '}') return 0;
    int n = 0;
    while (1) {
        p = js_ws(p);
        if (*p != '"') return -1;
        const char *kend = js_str_end(p);
        if (!kend) return -1;
        if (n >= maxn) return -1;
        js_key_copy(p, kend, out[n].key, sizeof(out[n].key));
        p = js_ws(kend);
        if (*p != ':') return -1;
        p = js_ws(p + 1);
        const char *vstart = p;
        const char *vend = js_val_end(p);
        if (!vend) return -1;
        out[n].vstart = vstart;
        out[n].vlen = (size_t)(vend - vstart);
        n++;
        p = js_ws(vend);
        if (*p == ',') { p++; continue; }
        if (*p == '}') return n;
        return -1;
    }
}

static const jmember *jm_find(const jmember *m, int n, const char *key) {
    for (int i = 0; i < n; i++)
        if (!strcmp(m[i].key, key)) return &m[i];
    return NULL;
}

/* ----------------------------------------------------------------------- */
/* Paths and small file utilities.                                         */
/* ----------------------------------------------------------------------- */

static char g_home[1024];
static char g_ds4dir[1100];        /* ~/.ds4 */
static char g_statepath[1200];     /* ~/.ds4/state */
static char g_backuppath[1200];    /* ~/.ds4/claude-settings.backup.json */
static char g_claudedir[1100];     /* ~/.claude */
static char g_settingspath[1200];  /* ~/.claude/settings.json */

static void paths_init(void) {
    const char *h = getenv("HOME");
    if (!h || !*h) h = ".";
    snprintf(g_home, sizeof(g_home), "%s", h);
    snprintf(g_ds4dir, sizeof(g_ds4dir), "%s/.ds4", g_home);
    snprintf(g_statepath, sizeof(g_statepath), "%s/state", g_ds4dir);
    snprintf(g_backuppath, sizeof(g_backuppath), "%s/claude-settings.backup.json", g_ds4dir);
    snprintf(g_claudedir, sizeof(g_claudedir), "%s/.claude", g_home);
    snprintf(g_settingspath, sizeof(g_settingspath), "%s/settings.json", g_claudedir);
}

/* Read a whole file into a malloc'd NUL-terminated buffer. */
static char *read_file(const char *path, size_t *out_len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return NULL; }
    long sz = ftell(f);
    if (sz < 0) { fclose(f); return NULL; }
    rewind(f);
    char *buf = malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return NULL; }
    size_t got = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    buf[got] = 0;
    if (out_len) *out_len = got;
    return buf;
}

/* Atomic write: temp file in the same directory, then rename. */
static int write_file_atomic(const char *path, const char *data, size_t len, mode_t mode) {
    char tmp[1300];
    snprintf(tmp, sizeof(tmp), "%s.ds4tmp", path);
    int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, mode);
    if (fd < 0) return -1;
    size_t off = 0;
    while (off < len) {
        ssize_t w = write(fd, data + off, len - off);
        if (w < 0) { if (errno == EINTR) continue; close(fd); unlink(tmp); return -1; }
        off += (size_t)w;
    }
    if (close(fd) != 0) { unlink(tmp); return -1; }
    if (rename(tmp, path) != 0) { unlink(tmp); return -1; }
    return 0;
}

static bool path_exists(const char *path) {
    struct stat st;
    return stat(path, &st) == 0;
}

static uint64_t fnv1a(const char *data, size_t len) {
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < len; i++) {
        h ^= (unsigned char)data[i];
        h *= 1099511628211ULL;
    }
    return h;
}

/* ----------------------------------------------------------------------- */
/* Persistent UI state (~/.ds4/state), simple key=value lines.             */
/* ----------------------------------------------------------------------- */

typedef struct {
    /* server options */
    int ctx;
    int tokens;          /* max output tokens per response, 0 = server default */
    int port;
    char host[64];
    char kvdir[512];
    int kvmb;
    char mtp[512];
    int threads;         /* 0 = auto */
    int ssd;             /* stream weights from SSD for models larger than RAM */
    /* claude binding bookkeeping (for the fast restore path) */
    int cc_had_settings;
    unsigned long long cc_connected_hash;
    unsigned long long cc_connected_len;
    /* server adoption hint across launches */
    long server_pid;
} ui_state;

static ui_state g_state;

static void state_defaults(void) {
    memset(&g_state, 0, sizeof(g_state));
    g_state.ctx = 100000;
    g_state.tokens = 0;
    g_state.port = 8000;
    snprintf(g_state.host, sizeof(g_state.host), "127.0.0.1");
    g_state.kvmb = 8192;
    g_state.kvdir[0] = 0;
    g_state.mtp[0] = 0;
    g_state.threads = 0;
    g_state.ssd = 0;
    g_state.server_pid = 0;
}

static void state_load(void) {
    state_defaults();
    size_t len = 0;
    char *buf = read_file(g_statepath, &len);
    if (!buf) return;
    char *save = NULL;
    for (char *line = strtok_r(buf, "\n", &save); line; line = strtok_r(NULL, "\n", &save)) {
        char *eq = strchr(line, '=');
        if (!eq) continue;
        *eq = 0;
        const char *k = line, *v = eq + 1;
        if (!strcmp(k, "ctx")) g_state.ctx = atoi(v);
        else if (!strcmp(k, "tokens")) g_state.tokens = atoi(v);
        else if (!strcmp(k, "port")) g_state.port = atoi(v);
        else if (!strcmp(k, "host")) snprintf(g_state.host, sizeof(g_state.host), "%s", v);
        else if (!strcmp(k, "kvdir")) snprintf(g_state.kvdir, sizeof(g_state.kvdir), "%s", v);
        else if (!strcmp(k, "kvmb")) g_state.kvmb = atoi(v);
        else if (!strcmp(k, "mtp")) snprintf(g_state.mtp, sizeof(g_state.mtp), "%s", v);
        else if (!strcmp(k, "threads")) g_state.threads = atoi(v);
        else if (!strcmp(k, "ssd")) g_state.ssd = atoi(v);
        else if (!strcmp(k, "cc_had_settings")) g_state.cc_had_settings = atoi(v);
        else if (!strcmp(k, "cc_connected_hash")) g_state.cc_connected_hash = strtoull(v, NULL, 10);
        else if (!strcmp(k, "cc_connected_len")) g_state.cc_connected_len = strtoull(v, NULL, 10);
        else if (!strcmp(k, "server_pid")) g_state.server_pid = atol(v);
    }
    free(buf);
}

static void ensure_ds4dir(void) {
    mkdir(g_ds4dir, 0700);
}

static void state_save(void) {
    ensure_ds4dir();
    sbuf b = {0};
    char line[1200];
    snprintf(line, sizeof(line), "ctx=%d\n", g_state.ctx); sb_puts(&b, line);
    snprintf(line, sizeof(line), "tokens=%d\n", g_state.tokens); sb_puts(&b, line);
    snprintf(line, sizeof(line), "port=%d\n", g_state.port); sb_puts(&b, line);
    snprintf(line, sizeof(line), "host=%s\n", g_state.host); sb_puts(&b, line);
    snprintf(line, sizeof(line), "kvdir=%s\n", g_state.kvdir); sb_puts(&b, line);
    snprintf(line, sizeof(line), "kvmb=%d\n", g_state.kvmb); sb_puts(&b, line);
    snprintf(line, sizeof(line), "mtp=%s\n", g_state.mtp); sb_puts(&b, line);
    snprintf(line, sizeof(line), "threads=%d\n", g_state.threads); sb_puts(&b, line);
    snprintf(line, sizeof(line), "ssd=%d\n", g_state.ssd); sb_puts(&b, line);
    snprintf(line, sizeof(line), "cc_had_settings=%d\n", g_state.cc_had_settings); sb_puts(&b, line);
    snprintf(line, sizeof(line), "cc_connected_hash=%llu\n", g_state.cc_connected_hash); sb_puts(&b, line);
    snprintf(line, sizeof(line), "cc_connected_len=%llu\n", g_state.cc_connected_len); sb_puts(&b, line);
    snprintf(line, sizeof(line), "server_pid=%ld\n", g_state.server_pid); sb_puts(&b, line);
    write_file_atomic(g_statepath, b.p ? b.p : "", b.len, 0600);
    sb_free(&b);
}

/* ----------------------------------------------------------------------- */
/* Model catalog. Mirrors download_model.sh -- keep in sync with that      */
/* script (the single source of truth for URLs and the download logic).    */
/* ----------------------------------------------------------------------- */

typedef struct {
    const char *target;    /* argument passed to download_model.sh */
    const char *label;
    const char *size;
    const char *rec;       /* who/what it is for (helps you pick) */
    const char *desc;      /* one-line description */
    const char *filename;  /* primary GGUF filename for installed/active checks */
    bool single_file;      /* true if this model can become ds4flash.gguf */
    bool is_pro;
} catalog_entry;

static const catalog_entry CATALOG[] = {
    {"q2-imatrix", "Flash q2 (imatrix)", "~81 GB", "96-128 GB RAM (start here)",
     "2-bit routed experts; the recommended everyday Flash model.",
     "DeepSeek-V4-Flash-IQ2XXS-w2Q2K-AProjQ8-SExpQ8-OutQ8-chat-v2-imatrix.gguf", true, false},
    {"q2-q4-imatrix", "Flash q2/q4 mixed", "~98 GB", "128 GB RAM (quality)",
     "Mostly q2 with the last 6 layers at q4 for a quality bump.",
     "DeepSeek-V4-Flash-Layers37-42Q4KExperts-OtherExpertLayersIQ2XXSGateUp-Q2KDown-AProjQ8-SExpQ8-OutQ8-chat-v2-imatrix-fixed.gguf", true, false},
    {"q4-imatrix", "Flash q4 (imatrix)", "~153 GB", "256 GB+ RAM",
     "4-bit routed experts; higher quality, larger footprint.",
     "DeepSeek-V4-Flash-Q4KExperts-F16HC-F16Compressor-F16Indexer-Q8Attn-Q8Shared-Q8Out-chat-v2-imatrix.gguf", true, false},
    {"pro-q2-imatrix", "Pro q2 (imatrix)", "~430 GB", "512 GB RAM",
     "DeepSeek V4 PRO at q2, single file. Much larger model.",
     "DeepSeek-V4-Pro-IQ2XXS-w2Q2K-AProjQ8-SExpQ8-OutQ8-Instruct-imatrix.gguf", true, true},
    {"pro-q4-layers00-30", "Pro q4 layers 0-30 (dist.)", "~426 GB", "distributed: coordinator",
     "First half (layers 0-30) of the PRO q4 split, for a 2-machine run.",
     "DeepSeek-V4-Pro-Q4K-Layers00-30.gguf", false, true},
    {"pro-q4-layers31-output", "Pro q4 layers 31-out (dist.)", "~412 GB", "distributed: worker",
     "Second half (layers 31-output) of the PRO q4 split, for a 2-machine run.",
     "DeepSeek-V4-Pro-Q4K-Layers-31-output.gguf", false, true},
    {"mtp", "MTP speculative (optional)", "~3.5 GB", "optional add-on",
     "Speculative-decoding helper for Flash; enable later with --mtp.",
     "DeepSeek-V4-Flash-MTP-Q4K-Q8_0-F32.gguf", false, false},
};
static const int CATALOG_N = (int)(sizeof(CATALOG) / sizeof(CATALOG[0]));

static const char *gguf_dir(void) {
    const char *d = getenv("DS4_GGUF_DIR");
    return (d && *d) ? d : "gguf";
}

static bool model_installed(const catalog_entry *e) {
    char path[2048];
    snprintf(path, sizeof(path), "%s/%s", gguf_dir(), e->filename);
    return path_exists(path);
}

/* basename of the current ds4flash.gguf symlink target, or empty. */
static void active_model_basename(char *out, size_t outsz) {
    out[0] = 0;
    char buf[2048];
    ssize_t n = readlink("ds4flash.gguf", buf, sizeof(buf) - 1);
    if (n <= 0) return;
    buf[n] = 0;
    const char *slash = strrchr(buf, '/');
    snprintf(out, outsz, "%s", slash ? slash + 1 : buf);
}

static const char *active_model_alias(void) {
    char base[2048];
    active_model_basename(base, sizeof(base));
    if (strstr(base, "Pro") || strstr(base, "PRO")) return "deepseek-v4-pro";
    return "deepseek-v4-flash";
}

static int set_active_model(const catalog_entry *e) {
    if (!e->single_file) return -1;
    char target[2048];
    snprintf(target, sizeof(target), "%s/%s", gguf_dir(), e->filename);
    if (!path_exists(target)) return -1;
    unlink("ds4flash.gguf");
    return symlink(target, "ds4flash.gguf");
}

/* ----------------------------------------------------------------------- */
/* Claude Code binding: env keys we inject into ~/.claude/settings.json.    */
/* Mirrors the README ~/bin/claude-ds4 wrapper.                            */
/* ----------------------------------------------------------------------- */

static const char *MANAGED_KEYS[] = {
    "ANTHROPIC_BASE_URL",
    "ANTHROPIC_AUTH_TOKEN",
    "ANTHROPIC_API_KEY",
    "ANTHROPIC_MODEL",
    "ANTHROPIC_DEFAULT_SONNET_MODEL",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL",
    "ANTHROPIC_DEFAULT_OPUS_MODEL",
    "CLAUDE_CODE_SUBAGENT_MODEL",
    "ANTHROPIC_CUSTOM_MODEL_OPTION",
    "ANTHROPIC_CUSTOM_MODEL_OPTION_NAME",
    "ANTHROPIC_CUSTOM_MODEL_OPTION_DESCRIPTION",
    "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC",
    "CLAUDE_CODE_DISABLE_NONSTREAMING_FALLBACK",
    "CLAUDE_STREAM_IDLE_TIMEOUT_MS",
};
static const int MANAGED_N = (int)(sizeof(MANAGED_KEYS) / sizeof(MANAGED_KEYS[0]));

static bool is_managed_key(const char *k) {
    for (int i = 0; i < MANAGED_N; i++)
        if (!strcmp(k, MANAGED_KEYS[i])) return true;
    return false;
}

static void managed_value(const char *key, const char *port, const char *alias,
                          char *out, size_t outsz) {
    if (!strcmp(key, "ANTHROPIC_BASE_URL"))
        snprintf(out, outsz, "http://127.0.0.1:%s", port);
    else if (!strcmp(key, "ANTHROPIC_AUTH_TOKEN"))
        snprintf(out, outsz, "dsv4-local");
    else if (!strcmp(key, "ANTHROPIC_API_KEY"))
        snprintf(out, outsz, "%s", "");
    else if (!strcmp(key, "ANTHROPIC_CUSTOM_MODEL_OPTION_NAME"))
        snprintf(out, outsz, "DeepSeek V4 (ds4 local)");
    else if (!strcmp(key, "ANTHROPIC_CUSTOM_MODEL_OPTION_DESCRIPTION"))
        snprintf(out, outsz, "ds4.c local GGUF");
    else if (!strcmp(key, "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC"))
        snprintf(out, outsz, "1");
    else if (!strcmp(key, "CLAUDE_CODE_DISABLE_NONSTREAMING_FALLBACK"))
        snprintf(out, outsz, "1");
    else if (!strcmp(key, "CLAUDE_STREAM_IDLE_TIMEOUT_MS"))
        snprintf(out, outsz, "600000");
    else /* model name keys */
        snprintf(out, outsz, "%s", alias);
}

/* Serialize a managed value as a JSON string into an sbuf. */
static void emit_managed_value(sbuf *b, const char *key, const char *port, const char *alias) {
    char val[1024];
    managed_value(key, port, alias, val, sizeof(val));
    sb_json_str(b, val);
}

/* Build the "connected" settings.json. Returns malloc'd string or NULL on
 * a JSON parse error (in which case we must not touch the file). */
static char *cc_build_connected(const char *orig, const char *port, const char *alias) {
    const char *src = (orig && *orig) ? orig : "{}";
    /* Locate the top-level object. */
    const char *obj = js_ws(src);
    if (*obj != '{') return NULL;

    static jmember top[256];
    int ntop = js_members(obj, top, 256);
    if (ntop < 0) return NULL;

    /* Parse existing env members, if any. */
    static jmember env[256];
    int nenv = 0;
    const jmember *envm = jm_find(top, ntop, "env");
    if (envm) {
        nenv = js_members(envm->vstart, env, 256);
        if (nenv < 0) return NULL;
    }

    sbuf b = {0};
    sb_puts(&b, "{\n");

    /* Copy all top-level members except env/_ds4_managed, verbatim. */
    for (int i = 0; i < ntop; i++) {
        if (!strcmp(top[i].key, "env") || !strcmp(top[i].key, "_ds4_managed")) continue;
        sb_puts(&b, "  ");
        sb_json_str(&b, top[i].key);
        sb_puts(&b, ": ");
        sb_put(&b, top[i].vstart, top[i].vlen);
        sb_puts(&b, ",\n");
    }

    /* env block: unmanaged originals (verbatim) + our managed keys. */
    sb_puts(&b, "  \"env\": {\n");
    bool first = true;
    for (int i = 0; i < nenv; i++) {
        if (is_managed_key(env[i].key)) continue;
        if (!first) sb_puts(&b, ",\n");
        first = false;
        sb_puts(&b, "    ");
        sb_json_str(&b, env[i].key);
        sb_puts(&b, ": ");
        sb_put(&b, env[i].vstart, env[i].vlen);
    }
    for (int i = 0; i < MANAGED_N; i++) {
        if (!first) sb_puts(&b, ",\n");
        first = false;
        sb_puts(&b, "    ");
        sb_json_str(&b, MANAGED_KEYS[i]);
        sb_puts(&b, ": ");
        emit_managed_value(&b, MANAGED_KEYS[i], port, alias);
    }
    sb_puts(&b, "\n  },\n");

    /* _ds4_managed sentinel: keys + port + alias + prev values we overrode. */
    sb_puts(&b, "  \"_ds4_managed\": {\n");
    sb_puts(&b, "    \"k\": [");
    for (int i = 0; i < MANAGED_N; i++) {
        if (i) sb_putc(&b, ',');
        sb_json_str(&b, MANAGED_KEYS[i]);
    }
    sb_puts(&b, "],\n    \"port\": ");
    sb_json_str(&b, port);
    sb_puts(&b, ",\n    \"alias\": ");
    sb_json_str(&b, alias);
    sb_puts(&b, ",\n    \"p\": {");
    bool pfirst = true;
    for (int i = 0; i < nenv; i++) {
        if (!is_managed_key(env[i].key)) continue;
        if (!pfirst) sb_putc(&b, ',');
        pfirst = false;
        sb_json_str(&b, env[i].key);
        sb_puts(&b, ": ");
        sb_put(&b, env[i].vstart, env[i].vlen);
    }
    sb_puts(&b, "}\n  }\n}\n");

    return b.p;
}

/* Build the "restored" settings.json by surgically removing our keys.
 * Sets *became_empty if the result has no top-level members at all. */
static char *cc_build_restored(const char *cur, bool *became_empty) {
    *became_empty = false;
    const char *obj = js_ws(cur ? cur : "");
    if (*obj != '{') return NULL;

    static jmember top[256];
    int ntop = js_members(obj, top, 256);
    if (ntop < 0) return NULL;

    const jmember *sentinel = jm_find(top, ntop, "_ds4_managed");
    const jmember *envm = jm_find(top, ntop, "env");

    /* Read port/alias/prev from the sentinel (if present). */
    char port[64] = "8000", alias[64] = "deepseek-v4-flash";
    static jmember prev[64];
    int nprev = 0;
    if (sentinel) {
        static jmember sm[16];
        int nsm = js_members(sentinel->vstart, sm, 16);
        if (nsm < 0) return NULL;
        const jmember *pm = jm_find(sm, nsm, "port");
        if (pm && pm->vlen >= 2) {
            size_t n = pm->vlen - 2 < sizeof(port) - 1 ? pm->vlen - 2 : sizeof(port) - 1;
            memcpy(port, pm->vstart + 1, n); port[n] = 0;
        }
        const jmember *am = jm_find(sm, nsm, "alias");
        if (am && am->vlen >= 2) {
            size_t n = am->vlen - 2 < sizeof(alias) - 1 ? am->vlen - 2 : sizeof(alias) - 1;
            memcpy(alias, am->vstart + 1, n); alias[n] = 0;
        }
        const jmember *ppm = jm_find(sm, nsm, "p");
        if (ppm) {
            nprev = js_members(ppm->vstart, prev, 64);
            if (nprev < 0) nprev = 0;
        }
    }

    /* Rebuild the env members list. */
    static jmember env[256];
    int nenv = 0;
    if (envm) {
        nenv = js_members(envm->vstart, env, 256);
        if (nenv < 0) return NULL;
    }

    sbuf envb = {0};
    int env_count = 0;
    for (int i = 0; i < nenv; i++) {
        if (is_managed_key(env[i].key)) {
            /* Did we set this? Compare current value to what we injected. */
            sbuf inj = {0};
            emit_managed_value(&inj, env[i].key, port, alias);
            bool ours = (inj.len == env[i].vlen) &&
                        memcmp(inj.p, env[i].vstart, env[i].vlen) == 0;
            sb_free(&inj);
            if (ours) {
                /* Our value, untouched: restore a pre-existing value if any. */
                const jmember *pv = jm_find(prev, nprev, env[i].key);
                if (pv) {
                    if (env_count) sb_puts(&envb, ",\n");
                    sb_puts(&envb, "    ");
                    sb_json_str(&envb, env[i].key);
                    sb_puts(&envb, ": ");
                    sb_put(&envb, pv->vstart, pv->vlen);
                    env_count++;
                }
                continue; /* otherwise drop */
            }
            /* User changed it after we connected: keep their version. */
        }
        if (env_count) sb_puts(&envb, ",\n");
        sb_puts(&envb, "    ");
        sb_json_str(&envb, env[i].key);
        sb_puts(&envb, ": ");
        sb_put(&envb, env[i].vstart, env[i].vlen);
        env_count++;
    }

    /* Reassemble the top-level object. */
    sbuf b = {0};
    sb_puts(&b, "{\n");
    int top_count = 0;
    for (int i = 0; i < ntop; i++) {
        if (!strcmp(top[i].key, "_ds4_managed")) continue;
        if (!strcmp(top[i].key, "env")) {
            if (env_count == 0) continue; /* drop empty env */
            if (top_count) sb_puts(&b, ",\n");
            sb_puts(&b, "  \"env\": {\n");
            sb_put(&b, envb.p ? envb.p : "", envb.len);
            sb_puts(&b, "\n  }");
            top_count++;
            continue;
        }
        if (top_count) sb_puts(&b, ",\n");
        sb_puts(&b, "  ");
        sb_json_str(&b, top[i].key);
        sb_puts(&b, ": ");
        sb_put(&b, top[i].vstart, top[i].vlen);
        top_count++;
    }
    sb_puts(&b, "\n}\n");
    sb_free(&envb);
    if (top_count == 0) *became_empty = true;
    return b.p;
}

/* Is settings.json currently bound by us? */
static bool cc_is_connected(void) {
    size_t len = 0;
    char *buf = read_file(g_settingspath, &len);
    if (!buf) return false;
    bool found = strstr(buf, "\"_ds4_managed\"") != NULL;
    free(buf);
    return found;
}

/* Connect: snapshot, write merged settings.json. Returns 0 / -1 and a msg. */
static int cc_connect(const char *port, const char *alias, char *msg, size_t msgsz) {
    ensure_ds4dir();
    size_t orig_len = 0;
    char *orig = read_file(g_settingspath, &orig_len);
    int had = orig ? 1 : 0;

    char *connected = cc_build_connected(orig ? orig : "{}", port, alias);
    if (!connected) {
        free(orig);
        snprintf(msg, msgsz, "settings.json is not valid JSON; refused to edit it");
        return -1;
    }

    /* Snapshot the original (or an empty marker) before writing. */
    if (orig) write_file_atomic(g_backuppath, orig, orig_len, 0600);
    else write_file_atomic(g_backuppath, "", 0, 0600);

    mkdir(g_claudedir, 0755);
    mode_t mode = 0644;
    struct stat st;
    if (orig && stat(g_settingspath, &st) == 0) mode = st.st_mode & 0777;

    size_t clen = strlen(connected);
    int rc = write_file_atomic(g_settingspath, connected, clen, mode);
    if (rc == 0) {
        g_state.cc_had_settings = had;
        g_state.cc_connected_len = clen;
        g_state.cc_connected_hash = fnv1a(connected, clen);
        state_save();
        snprintf(msg, msgsz, "connected: default `claude` now uses ds4 on :%s", port);
    } else {
        snprintf(msg, msgsz, "failed to write %s", g_settingspath);
    }
    free(connected);
    free(orig);
    return rc;
}

/* Restore: bring settings.json back to normal. Returns 0 / -1 and a msg. */
static int cc_restore(char *msg, size_t msgsz) {
    size_t cur_len = 0;
    char *cur = read_file(g_settingspath, &cur_len);
    if (!cur || !strstr(cur, "\"_ds4_managed\"")) {
        free(cur);
        unlink(g_backuppath);
        snprintf(msg, msgsz, "Claude Code already normal");
        return 0;
    }

    /* Fast path: file unchanged since we wrote it -> restore exact snapshot. */
    if (g_state.cc_connected_len == cur_len &&
        g_state.cc_connected_hash == fnv1a(cur, cur_len)) {
        if (g_state.cc_had_settings) {
            size_t blen = 0;
            char *bak = read_file(g_backuppath, &blen);
            if (bak) {
                write_file_atomic(g_settingspath, bak, blen, 0644);
                free(bak);
            }
        } else {
            unlink(g_settingspath);
        }
        unlink(g_backuppath);
        free(cur);
        snprintf(msg, msgsz, "Claude Code restored to normal");
        return 0;
    }

    /* Slow path: user edited settings.json -> surgical removal. */
    bool empty = false;
    char *restored = cc_build_restored(cur, &empty);
    if (!restored) {
        /* Malformed JSON: fall back to the original snapshot to guarantee
         * Claude Code returns to normal (may discard concurrent edits). */
        size_t blen = 0;
        char *bak = read_file(g_backuppath, &blen);
        if (bak) {
            if (g_state.cc_had_settings) write_file_atomic(g_settingspath, bak, blen, 0644);
            else unlink(g_settingspath);
            free(bak);
        }
        unlink(g_backuppath);
        free(cur);
        snprintf(msg, msgsz, "Claude Code restored from backup (edited file was invalid)");
        return 0;
    }

    if (empty && !g_state.cc_had_settings) {
        unlink(g_settingspath);
    } else {
        write_file_atomic(g_settingspath, restored, strlen(restored), 0644);
    }
    unlink(g_backuppath);
    free(restored);
    free(cur);
    snprintf(msg, msgsz, "Claude Code restored to normal");
    return 0;
}

/* ----------------------------------------------------------------------- */
/* Child process management (downloads and the server).                    */
/* ----------------------------------------------------------------------- */

#define CHILD_NLINES 7
#define CHILD_LINEW 512

typedef struct {
    pid_t pid;
    int fd;            /* read end of merged stdout+stderr, non-blocking */
    int running;
    int exited;
    int exit_code;
    char status[CHILD_LINEW];               /* latest progress / line */
    char lines[CHILD_NLINES][CHILD_LINEW];  /* recent completed lines (ring) */
    int nlines;
    char cur[CHILD_LINEW];
    size_t curlen;
    double progress;   /* 0..1 parsed from a percentage, or -1 */
    int ready;         /* server: saw "listening on http://" */
    int failed;        /* server: saw "failed to listen" */
} child_proc;

static void child_init(child_proc *c) {
    memset(c, 0, sizeof(*c));
    c->pid = -1;
    c->fd = -1;
    c->progress = -1;
}

/* env_extra: NULL-terminated array of "KEY=VALUE" strings to set in child. */
static int child_spawn(child_proc *c, char *const argv[], char *const env_extra[]) {
    int p[2];
    if (pipe(p) != 0) return -1;
    pid_t pid = fork();
    if (pid < 0) { close(p[0]); close(p[1]); return -1; }
    if (pid == 0) {
        /* child */
        setsid();
        dup2(p[1], STDOUT_FILENO);
        dup2(p[1], STDERR_FILENO);
        close(p[0]);
        close(p[1]);
        if (env_extra)
            for (int i = 0; env_extra[i]; i++) putenv(env_extra[i]);
        execvp(argv[0], argv);
        fprintf(stderr, "ds4-ui: failed to exec %s: %s\n", argv[0], strerror(errno));
        _exit(127);
    }
    close(p[1]);
    fcntl(p[0], F_SETFL, O_NONBLOCK);
    child_init(c);
    c->pid = pid;
    c->fd = p[0];
    c->running = 1;
    return 0;
}

static void child_push_line(child_proc *c) {
    snprintf(c->status, sizeof(c->status), "%s", c->cur);
    if (c->curlen > 0) {
        memmove(c->lines[0], c->lines[1], sizeof(c->lines[0]) * (CHILD_NLINES - 1));
        snprintf(c->lines[CHILD_NLINES - 1], CHILD_LINEW, "%s", c->cur);
        if (c->nlines < CHILD_NLINES) c->nlines++;
    }
    c->cur[0] = 0;
    c->curlen = 0;
}

static void child_parse_progress(child_proc *c) {
    /* Look for the last NN.N% token in the current segment. */
    const char *s = c->cur;
    const char *pct = NULL;
    for (const char *q = s; *q; q++)
        if (*q == '%') pct = q;
    if (!pct) return;
    const char *e = pct;
    const char *b = pct;
    while (b > s && (isdigit((unsigned char)b[-1]) || b[-1] == '.')) b--;
    if (b == e) return;
    char num[32];
    size_t n = (size_t)(e - b);
    if (n >= sizeof(num)) n = sizeof(num) - 1;
    memcpy(num, b, n);
    num[n] = 0;
    double v = atof(num);
    if (v >= 0 && v <= 100) c->progress = v / 100.0;
}

static void child_poll(child_proc *c) {
    if (c->fd >= 0) {
        char buf[4096];
        for (;;) {
            ssize_t n = read(c->fd, buf, sizeof(buf));
            if (n > 0) {
                for (ssize_t i = 0; i < n; i++) {
                    char ch = buf[i];
                    if (ch == '\n') {
                        if (!c->ready && strstr(c->cur, "listening on http://")) c->ready = 1;
                        if (!c->failed && strstr(c->cur, "failed to listen")) c->failed = 1;
                        child_push_line(c);
                    } else if (ch == '\r') {
                        child_parse_progress(c);
                        snprintf(c->status, sizeof(c->status), "%s", c->cur);
                        c->cur[0] = 0;
                        c->curlen = 0;
                    } else {
                        if (c->curlen + 1 < CHILD_LINEW) c->cur[c->curlen++] = ch;
                        c->cur[c->curlen] = 0;
                    }
                }
                continue;
            }
            if (n == 0) { close(c->fd); c->fd = -1; break; }
            break; /* EAGAIN */
        }
    }
    if (c->running) {
        int st;
        pid_t r = waitpid(c->pid, &st, WNOHANG);
        if (r == c->pid) {
            c->running = 0;
            c->exited = 1;
            c->exit_code = WIFEXITED(st) ? WEXITSTATUS(st) : -1;
            if (!c->ready && !c->failed && c->cur[0]) child_push_line(c);
        }
    }
}

static void child_stop(child_proc *c) {
    if (!c->running || c->pid <= 0) return;
    kill(c->pid, SIGTERM);
    for (int i = 0; i < 50; i++) { /* up to ~5s */
        int st;
        if (waitpid(c->pid, &st, WNOHANG) == c->pid) { c->running = 0; c->exited = 1; break; }
        usleep(100000);
    }
    if (c->running) {
        kill(c->pid, SIGKILL);
        int st;
        waitpid(c->pid, &st, 0);
        c->running = 0;
        c->exited = 1;
    }
    if (c->fd >= 0) { close(c->fd); c->fd = -1; }
}

/* ----------------------------------------------------------------------- */
/* Global UI state.                                                        */
/* ----------------------------------------------------------------------- */

typedef enum { SCREEN_MODELS = 0, SCREEN_SERVER, SCREEN_CLAUDE } screen_t;

typedef struct {
    bool active;             /* alt screen / raw mode engaged */
    bool quit;
    screen_t screen;
    int sel;                 /* model selection index */
    int srv_sel;             /* server-options field index */
    int cols, rows;
    struct termios orig_termios;
    bool raw_mode;
    child_proc download;
    child_proc server;
    bool download_busy;
    bool server_running;
    bool cc_connected;
    char hf_token[1024];     /* session-only HF token, empty if none */
    char msg[512];           /* transient status message */
} ui_t;

static ui_t g_ui;
static volatile sig_atomic_t g_signal_quit = 0;

static void set_msg(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(g_ui.msg, sizeof(g_ui.msg), fmt, ap);
    va_end(ap);
}

/* ----------------------------------------------------------------------- */
/* Terminal raw mode / restore (mirrors ds4_eval.c).                       */
/* ----------------------------------------------------------------------- */

static void term_move(int row, int col) { printf("\x1b[%d;%dH", row, col); }
static void term_clear_eol(void) { fputs("\x1b[K", stdout); }

static void terminal_size(int *cols, int *rows) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) != 0 || ws.ws_col == 0 || ws.ws_row == 0) {
        *cols = 80; *rows = 24; return;
    }
    *cols = ws.ws_col; *rows = ws.ws_row;
}

static char g_stdout_buf[1 << 16];

static void tui_enter(void) {
    /* Full buffering: each frame is flushed as one write, avoiding flicker. */
    setvbuf(stdout, g_stdout_buf, _IOFBF, sizeof(g_stdout_buf));
    if (tcgetattr(STDIN_FILENO, &g_ui.orig_termios) != 0) return;
    struct termios raw = g_ui.orig_termios;
    raw.c_lflag &= ~(ICANON | ECHO);
    raw.c_cc[VMIN] = 0;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSANOW, &raw) != 0) return;
    g_ui.raw_mode = true;
    fputs("\x1b[?1049h\x1b[?25l", stdout);
    fflush(stdout);
    g_ui.active = true;
}

static void tui_leave(void) {
    if (g_ui.raw_mode) {
        tcsetattr(STDIN_FILENO, TCSANOW, &g_ui.orig_termios);
        g_ui.raw_mode = false;
    }
    if (g_ui.active) {
        fputs(ANSI_RESET "\x1b[?25h\x1b[?1049l", stdout);
        fflush(stdout);
        g_ui.active = false;
    }
}

/* Cleanup invoked from atexit and the normal quit path. Idempotent. */
static void cleanup_all(void) {
    tui_leave();
    if (g_ui.server.running) child_stop(&g_ui.server);
    if (g_ui.download.running) child_stop(&g_ui.download);
    if (cc_is_connected()) {
        char m[512];
        cc_restore(m, sizeof(m));
    }
    g_state.server_pid = 0;
    state_save();
}

static void on_signal(int sig) {
    /* Minimal async-signal-safe terminal repair; the main loop notices the
     * flag and runs the full cleanup (JSON restore is not async-safe). */
    if (g_ui.raw_mode) {
        tcsetattr(STDIN_FILENO, TCSANOW, &g_ui.orig_termios);
        g_ui.raw_mode = false;
    }
    if (g_ui.active) {
        const char restore[] = ANSI_RESET "\x1b[?25h\x1b[?1049l";
        if (write(STDOUT_FILENO, restore, sizeof(restore) - 1) == -1) {}
        g_ui.active = false;
    }
    g_signal_quit = sig;
}

/* ----------------------------------------------------------------------- */
/* Modal line input (used for token/option entry).                         */
/* Returns 0 on Enter (out filled), -1 on ESC/cancel.                       */
/* ----------------------------------------------------------------------- */

static int ui_prompt(const char *label, char *out, size_t outsz, bool mask) {
    struct termios m = g_ui.orig_termios;
    m.c_lflag &= ~(ICANON | ECHO);
    m.c_cc[VMIN] = 1;
    m.c_cc[VTIME] = 0;
    tcsetattr(STDIN_FILENO, TCSANOW, &m);

    size_t len = 0;
    out[0] = 0;
    int rc = 0;
    fputs("\x1b[?25h", stdout);
    for (;;) {
        term_move(g_ui.rows, 1);
        term_clear_eol();
        printf(ANSI_BOLD "%s" ANSI_RESET " ", label);
        if (mask) for (size_t i = 0; i < len; i++) fputc('*', stdout);
        else fputs(out, stdout);
        fflush(stdout);

        char c;
        ssize_t n = read(STDIN_FILENO, &c, 1);
        if (n <= 0) { if (g_signal_quit) { rc = -1; break; } continue; }
        if (c == '\r' || c == '\n') { rc = 0; break; }
        if (c == 27) { rc = -1; break; }                  /* ESC cancels */
        if (c == 127 || c == 8) { if (len > 0) { len--; out[len] = 0; } continue; }
        if ((unsigned char)c >= 32 && len + 1 < outsz) { out[len++] = c; out[len] = 0; }
    }
    fputs("\x1b[?25l", stdout);
    /* Back to the main loop's non-blocking raw mode. */
    struct termios raw = g_ui.orig_termios;
    raw.c_lflag &= ~(ICANON | ECHO);
    raw.c_cc[VMIN] = 0;
    raw.c_cc[VTIME] = 0;
    tcsetattr(STDIN_FILENO, TCSANOW, &raw);
    return rc;
}

static int ui_prompt_int(const char *label, int cur, int *out) {
    char buf[64];
    char lbl[128];
    snprintf(lbl, sizeof(lbl), "%s [%d]:", label, cur);
    if (ui_prompt(lbl, buf, sizeof(buf), false) != 0) return -1;
    if (buf[0] == 0) return -1;
    *out = atoi(buf);
    return 0;
}

/* ----------------------------------------------------------------------- */
/* Drawing.                                                                */
/* ----------------------------------------------------------------------- */

static void draw_tab(const char *key, const char *name, bool active) {
    if (active) printf(" " ANSI_REV ANSI_BOLD " %s %s " ANSI_RESET, key, name);
    else printf("  " ANSI_DIM "%s" ANSI_RESET " %s ", key, name);
}

static int draw_header(void) {
    term_move(1, 1); term_clear_eol();
    fputs(ANSI_BOLD "ds4-ui" ANSI_RESET, stdout);
    draw_tab("1", "Models", g_ui.screen == SCREEN_MODELS);
    draw_tab("2", "Server", g_ui.screen == SCREEN_SERVER);
    draw_tab("3", "Claude Code", g_ui.screen == SCREEN_CLAUDE);
    printf("   " ANSI_DIM "q:quit" ANSI_RESET);
    term_move(2, 1); term_clear_eol();
    for (int i = 0; i < g_ui.cols && i < 200; i++) fputc('-', stdout);
    return 4; /* first body row */
}

static void draw_models(int row) {
    char active[2048];
    active_model_basename(active, sizeof(active));

    term_move(row++, 3); term_clear_eol();
    if (g_ui.download_busy)
        fputs(ANSI_DIM "Up/Down select  -  [x] cancel download  -  [t] HF token" ANSI_RESET, stdout);
    else
        fputs(ANSI_DIM "Up/Down select  -  [d] download  -  [l] set active  -  [t] HF token" ANSI_RESET, stdout);
    term_move(row++, 3); term_clear_eol();
    fputs(ANSI_DIM "Big files, but downloads resume if interrupted - you can quit and come back." ANSI_RESET, stdout);
    row++;

    for (int i = 0; i < CATALOG_N; i++) {
        const catalog_entry *e = &CATALOG[i];
        bool inst = model_installed(e);
        bool is_active = active[0] && !strcmp(active, e->filename);
        term_move(row++, 3); term_clear_eol();
        bool selrow = (i == g_ui.sel);
        if (selrow) fputs(ANSI_REV, stdout);
        const char *mark = is_active ? ANSI_GREEN "->" ANSI_RESET
                         : inst ? ANSI_GREEN " v" ANSI_RESET : "  ";
        printf("%s %-26.26s %-8s %-26.26s", mark, e->label, e->size, e->rec);
        if (selrow) fputs(ANSI_RESET, stdout);
    }

    /* Details / guidance for the highlighted model. */
    const catalog_entry *sel = &CATALOG[g_ui.sel];
    bool sel_inst = model_installed(sel);
    bool sel_active = active[0] && !strcmp(active, sel->filename);
    if (row < g_ui.rows - 6) {
        row++;
        term_move(row++, 3); term_clear_eol();
        printf(ANSI_BOLD "%s" ANSI_RESET "   %s on disk   -   for %s", sel->label, sel->size, sel->rec);
        term_move(row++, 5); term_clear_eol();
        printf(ANSI_DIM "%s" ANSI_RESET, sel->desc);
        term_move(row++, 5); term_clear_eol();
        if (sel_active) fputs(ANSI_GREEN "this is the active model" ANSI_RESET, stdout);
        else if (sel_inst && sel->single_file) fputs("installed - press [l] to make it the active model", stdout);
        else if (sel_inst) fputs("installed (add-on / distributed piece; not a standalone model)", stdout);
        else if (sel->single_file) fputs("press [d] to download and make it the active model", stdout);
        else fputs("press [d] to download (add-on / distributed piece; not auto-activated)", stdout);
        if (sel->is_pro) {
            term_move(row++, 5); term_clear_eol();
            fputs(ANSI_DIM "PRO files use the HuggingFace CLI: pip install -U huggingface_hub hf_xet" ANSI_RESET, stdout);
        }
    }

    if (row < g_ui.rows - 2) {
        term_move(row++, 3); term_clear_eol();
        bool tok = g_ui.hf_token[0] || getenv("HF_TOKEN");
        char hf_cache[1200];
        snprintf(hf_cache, sizeof(hf_cache), "%s/.cache/huggingface/token", g_home);
        if (!tok && path_exists(hf_cache)) tok = true;
        printf(ANSI_DIM "HF token: %s   -   gguf dir: %s" ANSI_RESET,
               tok ? "available" : "none (only needed for gated repos; [t] to set)", gguf_dir());
    }

    if (g_ui.download_busy || g_ui.download.exited) {
        row++;
        term_move(row++, 3); term_clear_eol();
        fputs(ANSI_BOLD "Download" ANSI_RESET, stdout);
        if (g_ui.download.progress >= 0) {
            int w = 30, fill = (int)(g_ui.download.progress * w);
            printf("  [");
            for (int i = 0; i < w; i++) fputc(i < fill ? '#' : ' ', stdout);
            printf("] %.1f%%", g_ui.download.progress * 100.0);
        }
        term_move(row++, 5); term_clear_eol();
        printf(ANSI_DIM "%.*s" ANSI_RESET, g_ui.cols - 6, g_ui.download.status);
        if (g_ui.download.exited) {
            term_move(row++, 5); term_clear_eol();
            if (g_ui.download.exit_code == 0)
                fputs(ANSI_GREEN "download finished" ANSI_RESET, stdout);
            else
                printf(ANSI_RED "download exited with code %d" ANSI_RESET, g_ui.download.exit_code);
        }
    }
}

/* Server-options fields (mirror the common ./ds4-server flags). */
enum { SF_CTX = 0, SF_TOKENS, SF_HOST, SF_PORT, SF_KVDIR, SF_KVMB, SF_MTP, SF_THREADS, SF_SSD, SF_COUNT };

static const char *SRV_FIELD_NAME[SF_COUNT] = {
    "context length", "max output tokens", "host", "port",
    "kv-disk cache dir", "kv-disk cache MB", "mtp model", "threads", "ssd streaming",
};
static const char *SRV_FIELD_FLAG[SF_COUNT] = {
    "--ctx", "--tokens", "--host", "--port",
    "--kv-disk-dir", "--kv-disk-space-mb", "--mtp", "--threads", "--ssd-streaming",
};
static const char *SRV_FIELD_HINT[SF_COUNT] = {
    "context window in tokens; larger needs more RAM",
    "cap on tokens per response (0 = server default)",
    "bind address; 127.0.0.1 is local-only, 0.0.0.0 exposes it",
    "TCP port to listen on",
    "directory for the on-disk KV cache (empty = off)",
    "max disk the KV cache may use, in MB",
    "optional speculative-decoding GGUF (empty = off)",
    "worker threads (0 = auto)",
    "stream weights from SSD for models larger than RAM",
};

static void srv_field_value(int idx, char *out, size_t n) {
    switch (idx) {
    case SF_CTX:     snprintf(out, n, "%d", g_state.ctx); break;
    case SF_TOKENS:  if (g_state.tokens > 0) snprintf(out, n, "%d", g_state.tokens); else snprintf(out, n, "default"); break;
    case SF_HOST:    snprintf(out, n, "%s", g_state.host); break;
    case SF_PORT:    snprintf(out, n, "%d", g_state.port); break;
    case SF_KVDIR:   snprintf(out, n, "%s", g_state.kvdir[0] ? g_state.kvdir : "(off)"); break;
    case SF_KVMB:    snprintf(out, n, "%d MB", g_state.kvmb); break;
    case SF_MTP:     snprintf(out, n, "%s", g_state.mtp[0] ? g_state.mtp : "(off)"); break;
    case SF_THREADS: if (g_state.threads > 0) snprintf(out, n, "%d", g_state.threads); else snprintf(out, n, "auto"); break;
    case SF_SSD:     snprintf(out, n, "%s", g_state.ssd ? "on" : "off"); break;
    default:         out[0] = 0; break;
    }
}

static void draw_server(int row) {
    term_move(row++, 3); term_clear_eol();
    if (g_ui.server_running)
        fputs(ANSI_DIM "Server running - stop it to change options." ANSI_RESET, stdout);
    else
        fputs(ANSI_DIM "Up/Down select  -  Enter/[e] edit  -  [s] start server" ANSI_RESET, stdout);
    row++;

    for (int i = 0; i < SF_COUNT; i++) {
        char val[600];
        srv_field_value(i, val, sizeof(val));
        term_move(row++, 3); term_clear_eol();
        if (i == g_ui.srv_sel) {
            fputs(ANSI_REV, stdout);
            printf("  %-20s %-32.32s", SRV_FIELD_NAME[i], val);
            fputs(ANSI_RESET, stdout);
        } else {
            printf("  %-20s %-32.32s " ANSI_DIM "%s" ANSI_RESET, SRV_FIELD_NAME[i], val, SRV_FIELD_FLAG[i]);
        }
    }

    term_move(row++, 3); term_clear_eol();
    printf(ANSI_DIM "%s  (%s)" ANSI_RESET, SRV_FIELD_HINT[g_ui.srv_sel], SRV_FIELD_FLAG[g_ui.srv_sel]);
    row++;

    char active[2048];
    active_model_basename(active, sizeof(active));
    term_move(row++, 3); term_clear_eol();
    if (!active[0]) fputs(ANSI_YELLOW "No active model. Download one on the Models tab first." ANSI_RESET, stdout);
    else printf(ANSI_DIM "active model: %.*s" ANSI_RESET, g_ui.cols - 18, active);

    term_move(row++, 3); term_clear_eol();
    if (g_ui.server_running && g_ui.server.ready)
        printf(ANSI_GREEN ANSI_BOLD "RUNNING" ANSI_RESET "  pid %d on http://%s:%d   [x] stop",
               (int)g_ui.server.pid, g_state.host, g_state.port);
    else if (g_ui.server_running)
        printf(ANSI_YELLOW "STARTING..." ANSI_RESET "  pid %d   [x] stop", (int)g_ui.server.pid);
    else
        fputs(ANSI_DIM "STOPPED" ANSI_RESET "   [s] start server", stdout);

    /* recent server log */
    if (g_ui.server.nlines && row < g_ui.rows - 2) {
        term_move(row++, 3); term_clear_eol();
        fputs(ANSI_DIM "server log:" ANSI_RESET, stdout);
        for (int i = 0; i < g_ui.server.nlines && row < g_ui.rows - 1; i++) {
            term_move(row++, 5); term_clear_eol();
            printf(ANSI_DIM "%.*s" ANSI_RESET, g_ui.cols - 6, g_ui.server.lines[i]);
        }
    }
}

static void draw_claude(int row) {
    term_move(row++, 3); term_clear_eol();
    if (g_ui.cc_connected)
        fputs(ANSI_GREEN ANSI_BOLD "CONNECTED" ANSI_RESET
              "  the default `claude` command routes to ds4", stdout);
    else
        fputs(ANSI_DIM "normal" ANSI_RESET "  Claude Code uses its usual configuration", stdout);
    row++;
    term_move(row++, 3); term_clear_eol();
    if (!g_ui.cc_connected) {
        if (g_ui.server_running && g_ui.server.ready)
            fputs("Press " ANSI_BOLD "[c]" ANSI_RESET " to connect Claude Code to the running server.", stdout);
        else
            fputs(ANSI_YELLOW "Start the server (Server tab) before connecting." ANSI_RESET, stdout);
    } else {
        fputs("Press " ANSI_BOLD "[r]" ANSI_RESET " to disconnect and restore Claude Code.", stdout);
    }
    row++;
    term_move(row++, 3); term_clear_eol();
    printf(ANSI_DIM "Writes an env block to %s and restores it on stop/quit." ANSI_RESET, g_settingspath);

    /* Warn about a shell-exported override that would win over settings.json */
    const char *shenv = getenv("ANTHROPIC_BASE_URL");
    if (shenv && *shenv) {
        term_move(row++, 3); term_clear_eol();
        fputs(ANSI_YELLOW "Note: ANTHROPIC_BASE_URL is exported in your shell and overrides settings.json." ANSI_RESET, stdout);
    }
}

static void draw_footer(void) {
    term_move(g_ui.rows - 1, 1); term_clear_eol();
    for (int i = 0; i < g_ui.cols && i < 200; i++) fputc('-', stdout);
    term_move(g_ui.rows, 1); term_clear_eol();
    if (g_ui.msg[0]) printf(ANSI_CYAN "%.*s" ANSI_RESET, g_ui.cols - 1, g_ui.msg);
}

static void redraw(void) {
    terminal_size(&g_ui.cols, &g_ui.rows);
    int row = draw_header();
    /* Wipe the whole body+footer region before repainting, so a screen that
     * draws fewer lines than the previous one leaves no stale content. */
    term_move(row, 1);
    fputs("\x1b[J", stdout);
    switch (g_ui.screen) {
    case SCREEN_MODELS: draw_models(row); break;
    case SCREEN_SERVER: draw_server(row); break;
    case SCREEN_CLAUDE: draw_claude(row); break;
    }
    draw_footer();
    fflush(stdout);
}

/* ----------------------------------------------------------------------- */
/* Actions.                                                                */
/* ----------------------------------------------------------------------- */

static void start_download(void) {
    if (g_ui.download_busy) { set_msg("a download is already running"); return; }
    if (!path_exists("download_model.sh")) { set_msg("download_model.sh not found (run from the ds4 dir)"); return; }
    const catalog_entry *e = &CATALOG[g_ui.sel];
    char *argv[] = { (char *)"./download_model.sh", (char *)e->target, NULL };
    char tokenenv[1100];
    char *env_extra[2] = { NULL, NULL };
    if (g_ui.hf_token[0]) {
        snprintf(tokenenv, sizeof(tokenenv), "HF_TOKEN=%s", g_ui.hf_token);
        env_extra[0] = tokenenv;
    }
    if (child_spawn(&g_ui.download, argv, env_extra) == 0) {
        g_ui.download_busy = true;
        set_msg("downloading %s (%s) - resumes if interrupted; press [x] to cancel", e->label, e->size);
    } else {
        set_msg("failed to start download");
    }
}

static void start_server(void) {
    if (g_ui.server_running) { set_msg("server already running"); return; }
    if (!path_exists("ds4-server")) { set_msg("ds4-server not built (run `make` first)"); return; }
    char active[2048];
    active_model_basename(active, sizeof(active));
    if (!active[0] && !path_exists("ds4flash.gguf")) {
        set_msg("no active model -- download/select one on the Models tab");
        return;
    }
    char ctxs[32], ports[32], kvmbs[32], tokens_s[32], threads_s[32];
    snprintf(ctxs, sizeof(ctxs), "%d", g_state.ctx);
    snprintf(ports, sizeof(ports), "%d", g_state.port);
    snprintf(kvmbs, sizeof(kvmbs), "%d", g_state.kvmb);
    snprintf(tokens_s, sizeof(tokens_s), "%d", g_state.tokens);
    snprintf(threads_s, sizeof(threads_s), "%d", g_state.threads);
    char *argv[28];
    int a = 0;
    argv[a++] = (char *)"./ds4-server";
    argv[a++] = (char *)"--ctx"; argv[a++] = ctxs;
    argv[a++] = (char *)"--host"; argv[a++] = g_state.host;
    argv[a++] = (char *)"--port"; argv[a++] = ports;
    argv[a++] = (char *)"--cors";
    if (g_state.tokens > 0) { argv[a++] = (char *)"--tokens"; argv[a++] = tokens_s; }
    if (g_state.threads > 0) { argv[a++] = (char *)"--threads"; argv[a++] = threads_s; }
    if (g_state.ssd) { argv[a++] = (char *)"--ssd-streaming"; }
    if (g_state.kvdir[0]) {
        argv[a++] = (char *)"--kv-disk-dir"; argv[a++] = g_state.kvdir;
        argv[a++] = (char *)"--kv-disk-space-mb"; argv[a++] = kvmbs;
    }
    if (g_state.mtp[0]) { argv[a++] = (char *)"--mtp"; argv[a++] = g_state.mtp; }
    argv[a] = NULL;
    if (child_spawn(&g_ui.server, argv, NULL) == 0) {
        g_ui.server_running = true;
        g_state.server_pid = g_ui.server.pid;
        state_save();
        set_msg("starting server (loading model, this can take a while)...");
    } else {
        set_msg("failed to start ds4-server");
    }
}

/* Stop the server and, because the binding is tied to the server lifecycle,
 * restore Claude Code to normal. */
static void stop_server(void) {
    if (g_ui.server.running) child_stop(&g_ui.server);
    g_ui.server_running = false;
    g_state.server_pid = 0;
    state_save();
    if (g_ui.cc_connected) {
        char m[512];
        cc_restore(m, sizeof(m));
        g_ui.cc_connected = false;
        set_msg("server stopped; %s", m);
    } else {
        set_msg("server stopped");
    }
}

static void connect_claude(void) {
    if (g_ui.cc_connected) { set_msg("already connected"); return; }
    if (!(g_ui.server_running && g_ui.server.ready)) {
        set_msg("start the server first, then connect");
        return;
    }
    char port[32];
    snprintf(port, sizeof(port), "%d", g_state.port);
    char m[512];
    if (cc_connect(port, active_model_alias(), m, sizeof(m)) == 0) {
        g_ui.cc_connected = true;
    }
    set_msg("%s", m);
}

static void disconnect_claude(void) {
    if (!g_ui.cc_connected && !cc_is_connected()) { set_msg("already normal"); return; }
    char m[512];
    cc_restore(m, sizeof(m));
    g_ui.cc_connected = false;
    set_msg("%s", m);
}

static void edit_server_field(int idx) {
    if (g_ui.server_running) { set_msg("stop the server to change options"); return; }
    int v;
    char buf[600];
    switch (idx) {
    case SF_CTX:
        if (ui_prompt_int("context length", g_state.ctx, &v) == 0 && v > 0) { g_state.ctx = v; state_save(); }
        break;
    case SF_TOKENS:
        if (ui_prompt_int("max output tokens (0=default)", g_state.tokens, &v) == 0 && v >= 0) { g_state.tokens = v; state_save(); }
        break;
    case SF_HOST:
        if (ui_prompt("host:", buf, sizeof(buf), false) == 0 && buf[0]) { snprintf(g_state.host, sizeof(g_state.host), "%s", buf); state_save(); }
        break;
    case SF_PORT:
        if (ui_prompt_int("port", g_state.port, &v) == 0 && v > 0 && v < 65536) { g_state.port = v; state_save(); }
        break;
    case SF_KVDIR:
        if (ui_prompt("kv-disk-dir (empty=off):", buf, sizeof(buf), false) == 0) { snprintf(g_state.kvdir, sizeof(g_state.kvdir), "%s", buf); state_save(); }
        break;
    case SF_KVMB:
        if (ui_prompt_int("kv-disk cache MB", g_state.kvmb, &v) == 0 && v > 0) { g_state.kvmb = v; state_save(); }
        break;
    case SF_MTP:
        if (ui_prompt("mtp gguf path (empty=off):", buf, sizeof(buf), false) == 0) { snprintf(g_state.mtp, sizeof(g_state.mtp), "%s", buf); state_save(); }
        break;
    case SF_THREADS:
        if (ui_prompt_int("threads (0=auto)", g_state.threads, &v) == 0 && v >= 0) { g_state.threads = v; state_save(); }
        break;
    case SF_SSD:
        g_state.ssd = !g_state.ssd; state_save();
        set_msg("ssd streaming %s", g_state.ssd ? "on" : "off");
        break;
    }
}

/* ----------------------------------------------------------------------- */
/* Key handling.                                                           */
/* ----------------------------------------------------------------------- */

enum { KEY_UP = 1000, KEY_DOWN, KEY_LEFT, KEY_RIGHT };

static void handle_key(int k) {
    /* global */
    if (k == 'q' || k == 'Q') { g_ui.quit = true; return; }
    if (k == '1') { g_ui.screen = SCREEN_MODELS; return; }
    if (k == '2') { g_ui.screen = SCREEN_SERVER; return; }
    if (k == '3') { g_ui.screen = SCREEN_CLAUDE; return; }

    if (g_ui.screen == SCREEN_MODELS) {
        if (k == KEY_UP) { if (g_ui.sel > 0) g_ui.sel--; }
        else if (k == KEY_DOWN) { if (g_ui.sel < CATALOG_N - 1) g_ui.sel++; }
        else if (k == 'd' || k == 'D' || k == '\r' || k == '\n') start_download();
        else if (k == 'x' || k == 'X') {
            if (g_ui.download_busy) {
                child_stop(&g_ui.download);
                g_ui.download_busy = false;
                set_msg("download canceled");
            }
        }
        else if (k == 'l' || k == 'L') {
            if (set_active_model(&CATALOG[g_ui.sel]) == 0) set_msg("active model set");
            else set_msg("cannot set active (not installed or multi-file)");
        } else if (k == 't' || k == 'T') {
            if (ui_prompt("HuggingFace token:", g_ui.hf_token, sizeof(g_ui.hf_token), true) == 0)
                set_msg("HF token set for this session");
        }
    } else if (g_ui.screen == SCREEN_SERVER) {
        if (k == KEY_UP) { if (g_ui.srv_sel > 0) g_ui.srv_sel--; }
        else if (k == KEY_DOWN) { if (g_ui.srv_sel < SF_COUNT - 1) g_ui.srv_sel++; }
        else if (k == 's' || k == 'S') start_server();
        else if (k == 'x' || k == 'X') stop_server();
        else if (k == 'e' || k == 'E' || k == '\r' || k == '\n') edit_server_field(g_ui.srv_sel);
    } else if (g_ui.screen == SCREEN_CLAUDE) {
        if (k == 'c' || k == 'C') connect_claude();
        else if (k == 'r' || k == 'R') disconnect_claude();
    }
}

static void read_keys(void) {
    char buf[64];
    ssize_t n = read(STDIN_FILENO, buf, sizeof(buf));
    if (n <= 0) return;
    int esc = 0;
    for (ssize_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)buf[i];
        if (esc == 0) {
            if (c == 27) esc = 1;
            else handle_key(c);
        } else if (esc == 1) {
            esc = (c == '[' || c == 'O') ? 2 : 0;
        } else {
            if (c == 'A') handle_key(KEY_UP);
            else if (c == 'B') handle_key(KEY_DOWN);
            else if (c == 'C') handle_key(KEY_RIGHT);
            else if (c == 'D') handle_key(KEY_LEFT);
            esc = 0;
        }
    }
}

/* ----------------------------------------------------------------------- */
/* Non-interactive helpers.                                                */
/* ----------------------------------------------------------------------- */

static int run_restore(void) {
    paths_init();
    state_load();
    char m[512];
    cc_restore(m, sizeof(m));
    printf("ds4-ui: %s\n", m);
    return 0;
}

static int run_status(void) {
    paths_init();
    state_load();
    char active[2048];
    active_model_basename(active, sizeof(active));
    printf("active model : %s\n", active[0] ? active : "(none)");
    printf("claude code  : %s\n", cc_is_connected() ? "CONNECTED (routes to ds4)" : "normal");
    if (g_state.server_pid > 0 && kill((pid_t)g_state.server_pid, 0) == 0)
        printf("server pid   : %ld (alive)\n", g_state.server_pid);
    else
        printf("server pid   : none\n");
    return 0;
}

/* Pure in-memory tests of the settings.json connect/restore logic. They never
 * touch any real file, so they are safe to run anytime. */
static int g_test_fail;
static void check(int cond, const char *name) {
    printf("  [%s] %s\n", cond ? "ok" : "FAIL", name);
    if (!cond) g_test_fail++;
}

static int run_selftest(void) {
    const char *PORT = "8000", *ALIAS = "deepseek-v4-flash";

    /* Case A: empty settings. */
    {
        char *con = cc_build_connected("{}", PORT, ALIAS);
        check(con != NULL, "A: connect builds");
        check(con && strstr(con, "\"_ds4_managed\""), "A: sentinel present");
        check(con && strstr(con, "\"ANTHROPIC_BASE_URL\": \"http://127.0.0.1:8000\""), "A: base url injected");
        check(con && strstr(con, "\"CLAUDE_CODE_SUBAGENT_MODEL\": \"deepseek-v4-flash\""), "A: subagent model injected");
        bool empty = false;
        char *res = cc_build_restored(con, &empty);
        check(res != NULL, "A: restore builds");
        check(res && !strstr(res, "_ds4_managed"), "A: sentinel removed");
        check(res && !strstr(res, "ANTHROPIC_BASE_URL"), "A: injected key removed");
        check(empty, "A: result is empty object");
        free(con); free(res);
    }

    /* Case B: preserves unrelated keys and a pre-existing env var. */
    {
        const char *orig = "{ \"permissions\": {\"allow\":[\"Bash\"]}, \"env\": { \"FOO\": \"bar\" }, \"theme\": \"dark\" }";
        char *con = cc_build_connected(orig, PORT, ALIAS);
        check(con && strstr(con, "\"permissions\""), "B: keeps permissions");
        check(con && strstr(con, "\"theme\""), "B: keeps theme");
        check(con && strstr(con, "\"FOO\": \"bar\""), "B: keeps env FOO");
        bool empty = false;
        char *res = cc_build_restored(con, &empty);
        check(res && strstr(res, "\"permissions\""), "B: restore keeps permissions");
        check(res && strstr(res, "\"FOO\": \"bar\""), "B: restore keeps env FOO");
        check(res && !strstr(res, "_ds4_managed"), "B: restore drops sentinel");
        check(res && !strstr(res, "ANTHROPIC_BASE_URL"), "B: restore drops injected");
        check(!empty, "B: result not empty");
        free(con); free(res);
    }

    /* Case C: user already had a managed key -> original value is restored. */
    {
        const char *orig = "{ \"env\": { \"ANTHROPIC_BASE_URL\": \"https://api.anthropic.com\" } }";
        char *con = cc_build_connected(orig, PORT, ALIAS);
        check(con && strstr(con, "https://api.anthropic.com"), "C: prev value saved in sentinel");
        check(con && strstr(con, "\"ANTHROPIC_BASE_URL\": \"http://127.0.0.1:8000\""), "C: live value overridden");
        bool empty = false;
        char *res = cc_build_restored(con, &empty);
        check(res && strstr(res, "https://api.anthropic.com"), "C: original value restored");
        check(res && !strstr(res, "127.0.0.1"), "C: injected value gone");
        check(res && !strstr(res, "_ds4_managed"), "C: sentinel gone");
        free(con); free(res);
    }

    /* Case D: user edited a managed value after connect -> their value is kept. */
    {
        const char *edited =
            "{ \"env\": { \"ANTHROPIC_MODEL\": \"user-custom\", "
            "\"ANTHROPIC_BASE_URL\": \"http://127.0.0.1:8000\" }, "
            "\"_ds4_managed\": { \"k\": [\"ANTHROPIC_BASE_URL\",\"ANTHROPIC_MODEL\"], "
            "\"port\":\"8000\", \"alias\":\"deepseek-v4-flash\", \"p\": {} } }";
        bool empty = false;
        char *res = cc_build_restored(edited, &empty);
        check(res && strstr(res, "\"ANTHROPIC_MODEL\": \"user-custom\""), "D: keeps user-edited value");
        check(res && !strstr(res, "ANTHROPIC_BASE_URL"), "D: drops untouched injected key");
        check(res && !strstr(res, "_ds4_managed"), "D: drops sentinel");
        free(res);
    }

    printf("\n%s\n", g_test_fail ? "SELFTEST FAILED" : "selftest passed");
    return g_test_fail ? 1 : 0;
}

/* Restore a stale binding left by a crashed previous session. */
static void self_heal(void) {
    if (!cc_is_connected()) return;
    /* If a server we recorded is still alive, another instance likely owns the
     * binding -- don't fight it. */
    if (g_state.server_pid > 0 && kill((pid_t)g_state.server_pid, 0) == 0) {
        set_msg("note: a previous session is still connected (pid %ld)", g_state.server_pid);
        g_ui.cc_connected = true;
        return;
    }
    char m[512];
    cc_restore(m, sizeof(m));
    set_msg("recovered: %s", m);
}

/* ----------------------------------------------------------------------- */
/* Entry point.                                                            */
/* ----------------------------------------------------------------------- */

/* Move to the directory of argv[0] so ./ds4-server, ./download_model.sh and
 * ds4flash.gguf resolve regardless of where the binary was launched from. */
static void chdir_to_self(const char *arg0) {
    const char *slash = strrchr(arg0, '/');
    if (!slash) return;
    char dir[2048];
    size_t n = (size_t)(slash - arg0);
    if (n >= sizeof(dir)) return;
    memcpy(dir, arg0, n);
    dir[n] = 0;
    if (chdir(dir) != 0) { /* non-fatal */ }
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--selftest")) return run_selftest();
        if (!strcmp(argv[i], "--restore")) return run_restore();
        if (!strcmp(argv[i], "--status")) return run_status();
        if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            printf("ds4-ui -- terminal UI for ds4 model downloads and Claude Code integration\n\n");
            printf("Usage:\n  ds4-ui            launch the interactive UI\n");
            printf("  ds4-ui --status   print server/binding status and exit\n");
            printf("  ds4-ui --restore  restore Claude Code to normal and exit\n");
            return 0;
        }
    }

    chdir_to_self(argv[0]);
    paths_init();
    state_load();

    if (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)) {
        fprintf(stderr, "ds4-ui: needs an interactive terminal (try --status or --restore)\n");
        return 1;
    }

    child_init(&g_ui.download);
    child_init(&g_ui.server);
    g_ui.cc_connected = cc_is_connected();

    self_heal();

    atexit(cleanup_all);
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = on_signal;        /* no SA_RESTART: interrupt poll()/read() */
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGHUP, &sa, NULL);
    sigaction(SIGQUIT, &sa, NULL);

    tui_enter();
    redraw();

    while (!g_ui.quit) {
        struct pollfd fds[3];
        int nf = 0;
        fds[nf].fd = STDIN_FILENO; fds[nf].events = POLLIN; nf++;
        if (g_ui.download.fd >= 0) { fds[nf].fd = g_ui.download.fd; fds[nf].events = POLLIN; nf++; }
        if (g_ui.server.fd >= 0) { fds[nf].fd = g_ui.server.fd; fds[nf].events = POLLIN; nf++; }

        int pr = poll(fds, nf, 200);
        if (g_signal_quit) break;
        if (pr > 0 && (fds[0].revents & POLLIN)) read_keys();

        /* Pump children. */
        if (g_ui.download.fd >= 0 || g_ui.download.running) {
            child_poll(&g_ui.download);
            if (!g_ui.download.running && g_ui.download_busy) g_ui.download_busy = false;
        }
        if (g_ui.server.fd >= 0 || g_ui.server.running) {
            bool was = g_ui.server.running;
            child_poll(&g_ui.server);
            if (was && !g_ui.server.running) {
                /* Server exited on its own: tear down the binding too. */
                g_ui.server_running = false;
                g_state.server_pid = 0;
                state_save();
                if (g_ui.cc_connected) {
                    char m[512];
                    cc_restore(m, sizeof(m));
                    g_ui.cc_connected = false;
                }
                set_msg("server exited (code %d); Claude Code restored", g_ui.server.exit_code);
            }
        }

        redraw();
    }

    cleanup_all();
    if (g_signal_quit) {
        /* Re-raise with default disposition so exit status reflects the signal. */
        signal(g_signal_quit, SIG_DFL);
        raise(g_signal_quit);
    }
    return 0;
}
