/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */
 
#include <stdarg.h>
#include <pthread.h>
#include <signal.h>

#include "log.h"

/* Config values */
static size_t log_queue_init_size = 10240;
/* When the log file exceeds this size limit, the log daemon will
 * rotate the log */
static size_t logfile_size_limit = 1024 * 1024 * 1024;
static int log_daemon_interval = 1;
static int run_daemon = 0;

static struct logger output;
static struct logger error;
static struct logger seq;

static vector_t log_queue;
static pthread_t logd_id;
static pthread_mutex_t loglock;

/* Rotate the log to reduce disk space consumption.
 * If the name of the logger is 'output', logrotate() will:
 *   1) close the file (so that the space it occupies would become freeable);
 *   2) rename 'output.log' to 'output.N.log'
 *   3) compress 'output.N.log' in the background
 *   4) reopen and recreate 'output.log'
 */
static void logrotate(struct logger *lgr)
{
    char logpath1[PATH_MAX] = {0};
    char logpath2[PATH_MAX] = {0};
    int N = 1;
    /* Only regular files should be rotated */
    if (!S_ISREG(lgr->type)) {
        return;
    }
    if (lgr->file)
        fclose(lgr->file);
    snprintf(logpath1, PATH_MAX, "%s.log", lgr->name);
    /* Rename <name>.log to <name>.N.log where N is the first unused integer */
    while (1) {
        char compr_cmd[ARG_MAX] = {0};
        snprintf(logpath2, PATH_MAX, "%s.%d.log.gz", lgr->name, N);
        if (access(logpath2, F_OK) == 0) {
            N++;
            continue;
        }
        snprintf(logpath2, PATH_MAX, "%s.%d.log", lgr->name, N);
        if (access(logpath2, F_OK) == 0) {
            N++;
            continue;
        }
        int ret = rename(logpath1, logpath2);
        assert(ret == 0);
        /* Compress the rotated log */
        snprintf(compr_cmd, PATH_MAX + 8, "gzip %s &", logpath2);
        ret = system(compr_cmd);
        break;
    }
    /* Reopen log file */
    lgr->file = fopen(logpath1, "w");
    lgr->bytes_written = 0;
    assert(lgr->file != NULL);
}

static void do_write_log(void)
{
    vector_t my_queue;
    /* Lock the global message queue, and replace it with a new one */
    pthread_mutex_lock(&loglock);
    /* A shallow copy */
    my_queue = log_queue;
    /* Reinitialize the global msg queue */
    vector_init(&log_queue, struct log_entry, log_queue_init_size);
    assert(my_queue.data);
    pthread_mutex_unlock(&loglock);

    /* Iterate the copy of the message queue and write logs */
    struct log_entry *entry;
    vector_iter(&my_queue, struct log_entry, entry) {
        ssize_t ret = fwrite(entry->content, 1, entry->loglen,
                entry->dest->file);
        assert(ret >= 0);
        fflush(entry->dest->file);
        free(entry->content);
        entry->content = NULL;
        entry->loglen = 0;
        entry->dest->bytes_written += ret;
        /* Rotate the log file if needed */
        if (entry->dest->bytes_written >= logfile_size_limit) {
            logrotate(entry->dest);
        }
    }

    vector_destroy(&my_queue);
}

static void *log_daemon(void *arg)
{
    while (run_daemon) {
        sleep(log_daemon_interval);
        do_write_log();
    }
    return NULL;
}

static void abort_handler(int sig)
{
    destroy_log_daemon();
    exit(sig);
}

static int _submit_log(struct logger *dest, const char *fmt, va_list args)
{
    struct log_entry ent;
    int ret;
    va_list args2;

    va_copy(args2, args);
    /* Get the length first, then allocate space for the content */
    ret = vsnprintf(NULL, 0, fmt, args);
    if (ret < 0)
        return ret;
    ent.content = malloc(ret + 1);
    if (ent.content == NULL)
        return -ENOMEM;
    /* Fill content to the allocated space */
    vsprintf(ent.content, fmt, args2);
    ent.loglen = ret;
    ent.dest = dest;

    /* Insert the log into the message queue */
    pthread_mutex_lock(&loglock);
    vector_add(&log_queue, &ent);
    pthread_mutex_unlock(&loglock);
    return ret;
}

int submit_log(struct logger *dest, const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    return _submit_log(dest, fmt, args);
}

int submit_message(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    return _submit_log(&output, fmt, args);
}

int vsubmit_message(const char *fmt, va_list args)
{
    return _submit_log(&output, fmt, args);
}

int submit_error(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    return _submit_log(&error, fmt, args);
}

int vsubmit_error(const char *fmt, va_list args) 
{
    return _submit_log(&error, fmt, args);
}

int submit_seq(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    return _submit_log(&seq, fmt, args);
}

int vsubmit_seq(const char *fmt, va_list args)
{
    return _submit_log(&seq, fmt, args);
}

void make_logger(struct logger *lgr, const char *name, FILE *default_fp)
{
    struct logger res = {
        .name = NULL,
        .file = default_fp,
        .bytes_written = 0,
        .type = 0
    };

    struct stat finfo = {0};
    char logpath[PATH_MAX] = {0};
    int ret;

    /* Make a copy of the logger name */
    size_t namelen = strnlen(name, PATH_MAX);
    char *name_copy = calloc(namelen + 1, sizeof(char));
    assert(name_copy != NULL);
    strncpy(name_copy, name, namelen);
    res.name = name_copy;

    /* Check existence of the log file */
    snprintf(logpath, PATH_MAX, "%s.log", name);
    ret = stat(logpath, &finfo);
    if (ret == 0 && S_ISREG(finfo.st_mode)) {
        /* Rotate the log file if it exists and is a regular file */
        res.type = finfo.st_mode;
        logrotate(&res);
    } else if (ret != 0 && errno == ENOENT) {
        /* Try creating if the file does not exist */
        res.file = fopen(logpath, "w");
        if (res.file == NULL) {
            fprintf(stderr, "%s: cannot create and open %s.\n",
                    __func__, logpath);
            goto fallback;
        }
        res.type = __S_IFREG;
    } else {
        /* If stat failed due to reasons other than ENOENT, or if
         * the file is not a regular file, something is wrong. */
        fprintf(stderr, "%s: stat '%s': errno = %d, mode = %o\n",
                __func__, logpath, errno, finfo.st_mode);
        goto fallback;
    }
    *lgr = res;
    return;

fallback:
    free(res.name);
    res.name = NULL;
    res.file = default_fp;
    *lgr = res;
}

void destroy_log_daemon()
{
    run_daemon = 0;
    pthread_join(logd_id, NULL);
    do_write_log();
    pthread_mutex_destroy(&loglock);
}

void init_log_daemon(const char *output_log_name, const char *err_log_name,
        const char *seq_name)
{
    int ret;
    pthread_attr_t logd_attrs;
    /* Initialize loggers */
    make_logger(&output, output_log_name, stdout);
    make_logger(&error, err_log_name, stderr);
    make_logger(&seq, seq_name, stdout);

    /* Set up signal handlers */
    signal(SIGABRT, abort_handler);
    signal(SIGSEGV, abort_handler);
    signal(SIGHUP, abort_handler);

    /* Set up the message queue */
    vector_init(&log_queue, struct log_entry, log_queue_init_size);

    /* Spawn log daemon thread */
    ret = pthread_attr_init(&logd_attrs);
    assert(ret == 0);
    run_daemon = 1;
    ret = pthread_create(&logd_id, &logd_attrs, log_daemon, NULL);
    assert(ret == 0);
    pthread_mutex_init(&loglock, NULL);
}

ssize_t get_progname(char *outbuf)
{
    int fd;
    char buffer[PATH_MAX + 1] = {0};
    ssize_t readres, ret = 0;
    ssize_t starti = 0, endi;

    fd = open("/proc/self/cmdline", O_RDONLY);
    if (fd < 0)
        return -errno;
    
    readres = read(fd, buffer, PATH_MAX);
    close(fd);

    if (readres < 0)
        return -errno;

    // find the first NULL terminator
    for (endi = 0; endi <= PATH_MAX && buffer[endi]; ++endi);
    // find the last slash
    for (starti = endi; starti >= 0 && buffer[starti] != '/'; --starti);
    // copy the progname to outbuf
    for (ssize_t i = starti + 1; i <= endi; ++i, ++ret) {
        *outbuf = buffer[i];
        outbuf++;
    }
    return ret;
}
