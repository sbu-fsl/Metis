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

#ifndef _NANOTIMING_H_
#define _NANOTIMING_H_

#include <stdio.h>

#ifdef __MACH__
#include <mach/clock.h>
#include <mach/mach.h>
#else
#include <time.h>
#include <sys/time.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * current_utc_time:- Retrieve current UTC time and output it via
 *                    struct timespec
 */
void current_utc_time(struct timespec *ts);
void timediff(struct timespec *res, struct timespec *end, struct timespec *start);
// 
/**
 * benchmark:- Run specified function and report the time it took.
 * @func: The function to use.
 * @arg:  The void pointer arg to pass in
 *
 * Note that there is a convention over the function to be benchmarked.
 * It is supposed to be in the form `int func(void *args)`
 * The integer return value indicates its "exit status", and the void *
 * argument it receives can be used for anything but usually a list of
 * parameters it needs.
 *
 * For example:
 *
 * struct func_arg_list {
 *      int a;
 *      int b;
 * };
 *
 * int func(void *args)
 * {
 *     struct func_arg_list *pars;
 *     if (!args) {
 *         return -1;
 *     }
 *     pars = (struct func_arg_list *)args;
 *
 *     // The payload to do...
 *
 *     // If success
 *     return 0;
 * }
 *
 * The return value is a `struct timespec` representing the time
 * it used to finish the function.
 */
struct timespec benchmark(int (*func)(void *), void *);
/**
 * bechmark_mt:- Benchmark for multiple times
 * @func: the function to benchmark
 * @arg: the void pointer arg to pass in
 * @times: number of iterations
 */
struct timespec benchmark_mt(int (*func)(void *), void *, unsigned int times);

#ifdef __cplusplus
}
#endif

#endif
