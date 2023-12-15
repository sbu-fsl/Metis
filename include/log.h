/*
 * Copyright (c) 2020-2023 Yifei Liu
 * Copyright (c) 2020-2023 Wei Su
 * Copyright (c) 2020-2023 Erez Zadok
 * Copyright (c) 2020-2023 Stony Brook University
 * Copyright (c) 2020-2023 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#ifndef _MCFS_LOG_H
#define _MCFS_LOG_H

#include "common_headers.h"

#ifdef __cplusplus
extern "C" {
#endif

struct logger {
    FILE *file;
    /* name: relative or absolute path to the log file, but excludes
     * the '.log' extension suffix. */
    char *name;
    size_t bytes_written;
    /* To be assigned from stat.st_mode */
    mode_t type;
};

struct log_entry {
    struct logger *dest;
    size_t loglen;
    char *content;
};

// Get a string of current date and time in the format of yyyymmdd-hhmmss
static inline void get_datetime_stamp(char *strbuf, size_t maxlen) {
  time_t now;
  struct tm now_tm;
  now = time(NULL);
  gmtime_r(&now, &now_tm);
  strftime(strbuf, maxlen, "%Y%m%d-%H%M%S", &now_tm);
}

static inline void add_ts_to_logname(char *strbuf, size_t maxlen,
    const char *logname, const char *progname, const char *suffix) {
  // yyyymmdd-hhmmss'\0' -> total 16 characters
  char tsbuf[16] = {0};
  get_datetime_stamp(tsbuf, 16);
  snprintf(strbuf, maxlen, "%s-%s-%s-%d%s", logname, progname, tsbuf, getpid(),
           suffix);
}

int submit_log(struct logger *dest, const char *fmt, ...);
int submit_message(const char *fmt, ...);
int vsubmit_message(const char *fmt, va_list args);
int submit_error(const char *fmt, ...);
int vsubmit_error(const char *fmt, va_list args);
int submit_seq(const char *fmt, ...);
int vsubmit_seq(const char *fmt, va_list args);
void make_logger(struct logger *lgr, const char *name, FILE *default_fp);
void init_log_daemon(const char *output_log_name, const char *err_log_name,
        const char *seq_name);
void destroy_log_daemon();
ssize_t get_progname(char *outbuf);

#ifdef __cplusplus
}
#endif

#endif
