## Other Components:

### example

A simple C program that demonstrates running a sequence of I/O test
operations using multiple threads/processes.

Use `make; ./test` to run this test program.

### promela-demo

A demo Promela model that runs a series of I/O ops on both TFS
and RFS non-deterministically and compare the behavior of them. We
actually don't care about whether the operations succeed or fail, but
we check if the behavior (e.g. return value [except open()], error code,
file (non)existence and file content) on the two file systems are equal.
Ahe test model will abort if there is a discrepancy of behavior between
TFS and RFS.

Use `make run` to run the test model.

This folder also contains many other experiments and demos that play
with promela and Spin.

### mcl-demo

A file system model checker written totally in C++, based on the model
checker that is used by eXplode project (Junfeng Yang, et al), called
MCL/CMC.

We are not currently developing it further because CMC is too old and not
well maintained as a mature product.

### python-demo

A python program written by Haolin Yu that tries to detect non-deterministic
`if-fi` statements in Promela code that could be translated from ambiguous
NFS RFC specs.

### common

Common code that will be use all other projects in this repo.

    * `errnoname.c`: Translate errno to its macro name
    * `nanotiming.c`: Timing utility functions

### include

    * `common_types.h`
    * `errnoname.h`
    * `nanotiming.h`
    * `path_utils.h`

## Common helper functions

### Errno conversion

```c
// #include "errnoname.h"
char const *errnoname(int errno_);
```

Convert the error code number into its macro name. For example, `2` will be
converted to `"ENOENT"`.

### Timing and benchmarking

#### 1. Get current time in nanosecond precision

```c
// #include "nanotiming.h"
void current_utc_time(struct timespec *ts);
```

`struct timespec` is in the following form:

```c
struct timespec {
    time_t tv_sec;
    long tv_nsec;
};
```

### 2. Calculate the difference of two timespecs

```c
// #include "nanotiming.h"
void timediff(struct timespec *res, struct timespec *end, struct timespec *start);
```

### 3. Benchmarking

```c
// #include "nanotiming.h"
struct timespec benchmark(int (*func)(void *), void *arg);
struct timespec benchmark_mt(int (*func)(void *), void *arg, unsigned int times);
```

`benchmark` will run `func(arg)` once and return the execution time.
`benchmark_mt` will run `func(arg)` `times` times and return the average
execution time.
