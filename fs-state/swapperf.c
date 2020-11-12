#include "fileutil.h"
#include "swapperf.h"

static int n_swaps;
static char **swapdevs;

void iostat_diff(struct iostat *diff, struct iostat *a, struct iostat *b)
{
    diff->reads_success = a->reads_success - b->reads_success;
    diff->reads_merged = a->reads_merged - b->reads_merged;
    diff->bytes_read = a->bytes_read - b->bytes_read;
    diff->time_read = a->time_read - b->time_read;
    diff->writes_complete = a->writes_complete - b->writes_complete;
    diff->writes_merged = a->writes_merged - b->writes_merged;
    diff->bytes_written = a->bytes_written - b->bytes_written;
    diff->time_write = a->time_write - b->time_write;
    /* io_progress represents num of I/Os that are currently in progress and
     * it's not accumulative, so that field should not be diffed */
}

/* Retrieve a field from a line of data separated by whitespaces.
 * Returns pointer to the character right after the parsed field
 *
 * For example:
 * line = "    123   456   abc  ...def"
 *                ^
 *               where returned pointer points
 * *fieldbuf = "123"
 * fieldlen = 3
 *
 * */
const char *nextfield(const char *line, char **fieldbuf, size_t *fieldlen)
{
    size_t len = 0;
    const char *ptr = line;
    char *buf = NULL;
    /* bypass spaces, tabs and newline symbols */
    for (; *ptr != '\0' && (*ptr == ' ' || *ptr == '\t' || *ptr == '\n'); ++ptr);
    /* measure the length of field */
    for (const char *tmp = ptr; *tmp != '\0' && *tmp != ' '; ++tmp, ++len);
    
    *fieldlen = len;
    if (len == 0) {
        *fieldbuf = NULL;
        return NULL;
    }
    
    buf = malloc(len + 1);
    buf[len] = '\0';
    for (int i = 0; i < len; ++ptr, ++i) {
        buf[i] = *ptr;
    }
    *fieldbuf = buf;
    return ptr;
}

static char *strdup_(const char *s)
{
    size_t len = strnlen(s, NAME_MAX);
    char *newstr = malloc(len + 1);
    assert(newstr);
    
    newstr[len] = '\0';
    strncpy(newstr, s, len);
    return newstr;
}

/* Parse a line of data from /proc/diskstats and stores the metrics in *st */
static void parse_diskstat_line(const char *line, struct iostat *st)
{
    int i = 1;
    const char *ptr = line;
    while (1) {
        size_t fieldlen;
        char *fieldbuf;
        ptr = nextfield(ptr, &fieldbuf, &fieldlen);
        if (!ptr)
            break;
        if (i == 1) {
            st->major = atoi(fieldbuf);
        } else if (i == 2) {
            st->minor = atoi(fieldbuf);
        } else if (i == 3) {
            st->_malloced_name = true;
            st->devname = strdup_(fieldbuf);
        } else if (i == 4) {
            st->reads_success = atol(fieldbuf);
        } else if (i == 5) {
            st->reads_merged = atol(fieldbuf);
        } else if (i == 6) {
            st->bytes_read = atol(fieldbuf) * 512;
        } else if (i == 7) {
            st->time_read = atol(fieldbuf);
        } else if (i == 8) {
            st->writes_complete = atol(fieldbuf);
        } else if (i == 9) {
            st->writes_merged = atol(fieldbuf);
        } else if (i == 10) {
            st->bytes_written = atol(fieldbuf) * 512;
        } else if (i == 11) {
            st->time_write = atol(fieldbuf);
        } else if (i == 12) {
            st->io_progress = atol(fieldbuf);
        } else if (i == 13) {
            st->time_io = atol(fieldbuf);
        }
        free(fieldbuf);
        ++i;
    }
}

/* Check if the supplied device name (without '/dev/' full path) is used
 * for swapping */
static bool is_swap_device(const char *devname)
{
    for (int i = 0; i < n_swaps; ++i) {
        char *ptr = swapdevs[i];
        for (; *ptr != '\0'; ++ptr);
        for (; ptr >= swapdevs[i] && *ptr != '/'; --ptr);
        ++ptr;
        if (strncmp(ptr, devname, NAME_MAX) == 0)
            return true;
    }
    return false;
}

void get_swapstats(struct iostat *stats)
{
    FILE *fp = fopen("/proc/diskstats", "r");
    if (!fp) {
        fprintf(stderr, "Cannot open /proc/diskstats (%s)\n", errnoname(errno));
        exit(1);
    }
    
    char *linebuf = NULL;
    size_t n = 0;
    ssize_t readlen;
    int i = 0;
    while ((readlen = getline(&linebuf, &n, fp)) >= 0) {
        struct iostat info;
        parse_diskstat_line(linebuf, &info);
        if (is_swap_device(info.devname)) {
            memcpy(stats + i, &info, sizeof(struct iostat));
            ++i;
        } else {
            free(info.devname);
        }

        free(linebuf);
        linebuf = NULL;
        n = 0;
    }
    fclose(fp);
}

/* Release ->devname to avoid memory leak
 * This does NOT free *stats itself */
void put_swapstats(struct iostat *stats)
{
    for (int i = 0; i < n_swaps; ++i) {
        if (stats[i]._malloced_name) {
            free(stats[i].devname);
        }
    }
}

int num_swap_devices()
{
    return n_swaps;
}

static bool is_swappath_valid(const char *swappath, size_t slen)
{
    /* Filter out the title/header */
    if (strncmp(swappath, "Filename", slen) == 0)
        return false;

    /* The swap file should be located in /dev folder */
    const char *prefix = "/dev/";
    if (strncmp(swappath, prefix, strlen(prefix)) != 0)
        return false;

    /* It should be a block device. Otherwise, it cannot be vmstat'ed */
    struct stat st;
    int ret = stat(swappath, &st);
    if (ret < 0) {
        fprintf(stderr, "Cannot stat %s (%d)\n", swappath, errno);
        return false;
    }

    return S_ISBLK(st.st_mode);
}

void get_swaps()
{
    int swaps_len = 10;
    FILE *fp = fopen("/proc/swaps", "r");
    assert(fp);

    swapdevs = malloc(swaps_len * sizeof(char *));
    assert(swapdevs);

    char *linebuf = NULL;
    size_t n = 0;
    ssize_t ret;
    while ((ret = getline(&linebuf, &n, fp)) >= 0) {
        /* Though it's rare to have more than 10 swap devices, we'd still better
         * consider this corner case */
        if (n_swaps >= swaps_len) {
            swaps_len *= 2;
            swapdevs = realloc(swapdevs, swaps_len * sizeof(char *));
            assert(swapdevs);
        }

        char *swappath;
        nextfield(linebuf, &swappath, &n);
        if (is_swappath_valid(swappath, n)) {
            swapdevs[n_swaps] = swappath;
            n_swaps++;
        } else {
            free(swappath);
        }

        free(linebuf);
        linebuf = NULL;
        n = 0;
    }
    fclose(fp);
}

static void __attribute__((destructor)) swapperf_exit()
{
    for (int i = 0; i < n_swaps; ++i) {
        free(swapdevs[i]);
    }
    free(swapdevs);
}
