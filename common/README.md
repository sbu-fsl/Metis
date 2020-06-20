# common - commonly-used functionalities

This directory contains some commonly-used C programs.

## errnoname.c

The errnoname.c defines a function ***errnoname*** which takes error number as argument and returns the corresponding error name. We can use this function to record the error name along with error number when an error occurs.

## nanotiming.c

The nanotiming.c defines several time-related functionalities.

- **current_utc_time**: passes _struct timespec *_ as argument and gets the current UTC time to the pointer. (**__MACH__** MACRO should be defined if use OS X)
- **unify_timedelta**: normalize the struct timespec by converting negative tv_nsec (nanoseconds) to positive with decrease tv_sec (seconds). This will be used when calcalutes timediff().
- **timediff**: passes three _struct timespec *_ ,res, end, start, as arguments. This function gets the timediff between end and start (end-start) and returns the timediff result in res.
- **benchmark**: benchmark function _func_ with its arguments _arg_, which returns the executed time of this specific function.
- **benchmark_mt**: compared to benchmark, benchmark_mt computes the executed time with run *func* multiple times (specified as *times*) and returns the timediff result in res.
