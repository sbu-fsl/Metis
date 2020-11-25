#include "fileutil.h"
#include "swapperf.h"
#include <sys/vfs.h>
#include <sys/sysinfo.h>
#include <pthread.h>

static FILE *perflog_fp;
static int curpid;
static int perf_logger_stop = 0;
static pthread_t perf_logger_id;

/* From /proc/[pid]/stat */
struct proc_stat {
    /* f1 */
    int pid;
    /* f3: See man proc: /proc/[pid]/stat field (3) */
    char state;
    /* f4 */
    int ppid;
    /* f10: Minor faults that haven't required loading a memory page from disk */
    unsigned long minflt;
    /* f12: Major faults that **have** required loading a page from disk */
    unsigned long majflt;
    /* f14 */
    unsigned long utime;
    /* f15 */
    unsigned long ktime;
    /* f20 */
    unsigned long num_threads;
    /* f23 */
    unsigned long vsize;
    /* f24 */
    long psize;
};

static void get_proc_stat(struct proc_stat *st)
{
    char statpath[32];
    FILE *statfp = NULL;

    snprintf(statpath, 32, "/proc/%d/stat", curpid);
    statfp = fopen(statpath, "r");

    if (!statfp) {
        fprintf(stderr, "Cannot open %s - what's wrong? (%d)\n",
                statpath, errno);
        exit(1);
    }

    ssize_t readsz = 0;
    for (int i = 1; readsz >= 0; ++i) {
        char *fieldbuf = NULL;
        char *end;
        size_t n = 0;
        readsz = getdelim(&fieldbuf, &n, ' ', statfp);
        if (readsz <= 0)
            continue;

        if (i == 3) {
            st->state = fieldbuf[0];
        } else if (i == 4) {
            st->ppid = atoi(fieldbuf);
        } else if (i == 10) {
            st->minflt = strtoul(fieldbuf, &end, 10);
        } else if (i == 12) {
            st->majflt = strtoul(fieldbuf, &end, 10);
        } else if (i == 14) {
            st->utime = strtoul(fieldbuf, &end, 10);
        } else if (i == 15) {
            st->ktime = strtoul(fieldbuf, &end, 10);
        } else if (i == 20) {
            st->num_threads = strtoul(fieldbuf, &end, 10);
        } else if (i == 23) {
            st->vsize = strtoul(fieldbuf, &end, 10);
        } else if (i == 24) {
            st->psize = atol(fieldbuf);
            st->psize = st->psize * 4096;
        }

        free(fieldbuf);
    }
    st->pid = curpid;
    fclose(statfp);
}

struct fs_stat {
    size_t capacity;
    size_t bytes_free;
    size_t bytes_avail;
    size_t total_inodes;
    size_t free_inodes;
    size_t block_size;
};

static int get_fs_stat(const char *mp, struct fs_stat *st)
{
    struct statfs raw_st;
    int ret = statfs(mp, &raw_st);
    if (ret < 0) {
        fprintf(stderr, "Cannot stat file system at %s: %d\n", mp, errno);
        return ret;
    }
    size_t bs = raw_st.f_bsize;
    st->capacity = raw_st.f_blocks * bs;
    st->bytes_free = raw_st.f_bfree * bs;
    st->bytes_avail = raw_st.f_bavail * bs;
    st->total_inodes = raw_st.f_files;
    st->free_inodes = raw_st.f_ffree;
    st->block_size = bs;
    return ret;
}

static struct fs_stat fsinfos[N_FS];
static pthread_mutex_t fsinfo_lock;

void record_fs_stat()
{
    struct fs_stat my_fsstats[N_FS];
    for (int i = 0; i < N_FS; ++i) {
        get_fs_stat(basepaths[i], &my_fsstats[i]);
    }
    pthread_mutex_lock(&fsinfo_lock);
    memcpy(fsinfos, my_fsstats, sizeof(struct fs_stat) * N_FS);
    pthread_mutex_unlock(&fsinfo_lock);
}

void record_performance()
{
    static bool inited = false;
    static size_t last_count = 0;
    static struct timespec last_ts = {0};
    static struct iostat *last_swaps_stat;
    static int n_swaps;

    struct timespec now, diff, epoch;
    current_utc_time(&now);

    if (!inited) {
        last_ts = now;
        /* metrics about the model checker itself */
        fprintf(perflog_fp, "epoch,fsops_rate,proc_state,minor_flt,major_flt,"
                "utime,ktime,num_threads,vmem_sz,pmem_sz,");
        /* metrics of the swap devices activity */
        n_swaps = num_swap_devices();
        last_swaps_stat = malloc(n_swaps * sizeof(struct iostat));
        assert(last_swaps_stat);
        get_swapstats(last_swaps_stat);
	fprintf(perflog_fp, "swap_bytes_used,");
        for (int i = 0; i < n_swaps; ++i) {
            fprintf(perflog_fp, "swap_%s_bytes_read,swap_%s_bytes_written,",
                    last_swaps_stat[i].devname, last_swaps_stat[i].devname);
        }
        /* metrics of the file systems being tested */
        for (int i = 0; i < N_FS; ++i) {
            const char *mp = fslist[i];
            fprintf(perflog_fp, "%s_capacity,%s_free,%s_inodes,%s_ifree,",
                    mp, mp, mp, mp);
        }
        fprintf(perflog_fp, "\n");
        inited = true;
    }

    timediff(&diff, &now, &last_ts);
    timediff(&epoch, &now, &begin_time);

    float timediff = diff.tv_sec + diff.tv_nsec * 1e-9;
    /* Calculate avg fs ops rate in the past $interval seconds */
    float rate = (count) ? (count - last_count) / timediff : 0.0;
    last_ts = now;
    last_count = count;
    /* Retrieve proc stat */
    struct proc_stat ps = {0};
    get_proc_stat(&ps);
    /* Out first half of the metrics */
    fprintf(perflog_fp, "%ld.%09ld,%.3f,%c,%lu,%lu,%lu,%lu,%lu,%lu,%ld,",
            epoch.tv_sec, epoch.tv_nsec, rate, ps.state, ps.minflt, 
            ps.majflt, ps.utime, ps.ktime, ps.num_threads, ps.vsize,
            ps.psize);
    /* Retrieve swap activity */
    struct iostat *swaps_stat;
    struct iostat *swaps_diff;
    struct sysinfo info;
    int ret = sysinfo(&info);
    if (ret != 0) {
        fprintf(stderr, "Cannot get sysinfo: %s\n", errnoname(errno));
        exit(1);
    }
    fprintf(perflog_fp, "%lu,", info.totalswap - info.freeswap);
    swaps_stat = malloc(2 * n_swaps * sizeof(struct iostat));
    swaps_diff = swaps_stat + n_swaps;
    get_swapstats(swaps_stat);
    iostat_diff(swaps_diff, swaps_stat, last_swaps_stat);
    for (int i = 0; i < n_swaps; ++i) {
        double read_rate = swaps_diff[i].bytes_read / timediff;
        double write_rate = swaps_diff[i].bytes_written / timediff;
        fprintf(perflog_fp, "%.2f,%.2f,", read_rate, write_rate);
    }
    /* Free last_swaps_stat[i].devname to avoid memory leak */
    put_swapstats(last_swaps_stat);
    memcpy(last_swaps_stat, swaps_stat, n_swaps * sizeof(struct iostat));
    free(swaps_stat);
    /* Iterate each file system */
    struct fs_stat cur_fsstats[N_FS];
    pthread_mutex_lock(&fsinfo_lock);
    memcpy(cur_fsstats, fsinfos, sizeof(struct fs_stat) * N_FS);
    pthread_mutex_unlock(&fsinfo_lock);
    for (int i = 0; i < N_FS; ++i) {
        struct fs_stat *fs = cur_fsstats + i;
        fprintf(perflog_fp, "%zu,%zu,%zu,%zu,", fs->capacity, fs->bytes_free,
                fs->total_inodes, fs->free_inodes);
    }
    fprintf(perflog_fp, "\n");
    fflush(perflog_fp);
}

void* perf_logger(void *arg)
{
    while (!perf_logger_stop) {
        record_performance();
        sleep(PERF_INTERVAL);
    }
    return NULL;
}

void start_perf_metrics_thread()
{
    pthread_attr_t attr;
    int ret = pthread_attr_init(&attr);
    assert(ret == 0);
    ret = pthread_create(&perf_logger_id, &attr, perf_logger, NULL);
    assert(ret == 0);
    pthread_mutex_init(&fsinfo_lock, NULL);
}

void seed_rand_with_urandom()
{
    int randfd = open("/dev/urandom", O_RDONLY);
    /* Will fall back to timestamp if the rand device is not available */
    unsigned seed = time(0);
    if (randfd < 0) {
        fprintf(stderr, "Failed to open /dev/urandom: %d. Will use timestamp "
                "to seed rand() RNG instead.\n", errno);
    } else {
        read(randfd, &seed, sizeof(unsigned));
        close(randfd);
    }
    srand(seed);
}

static void __attribute__((constructor)) perf_init()
{
    seed_rand_with_urandom();
    get_swaps();
    current_utc_time(&begin_time);
    perflog_fp = fopen(PERF_LOG_PATH, "w");
    if (!perflog_fp) {
        fprintf(stderr, "Cannot create or open perf log file at %s (%d)\n",
                PERF_LOG_PATH, errno);
        abort();
    }
    curpid = getpid();
}

static void __attribute__((destructor)) perf_exit()
{
    perf_logger_stop = 1;
    pthread_join(perf_logger_id, NULL);
    pthread_mutex_destroy(&fsinfo_lock);
    if (perflog_fp)
        fclose(perflog_fp);
}
