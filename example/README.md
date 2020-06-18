# example - an example to execute sequence of filesystem syscalls with multi-threading

This directory includes test.c and Makefile that runs sequence of filesystem syscalls and outputs the results to text and json files.

## How to run

To run this example, use `make; ./test`; to clean generated resources, use `make clean`.

## Design

This program creates a specified number (`n_workers`) of workers and each worker is associated with a **struct worker_arg** that includes `worker_id` (worker/thread id), `data` (*dsize* random bytes from `/dev/urandom`), `dsize` (size of *data*), `dirname` (dirname used for testing mkdir/rmdir syscall), `filename` (filename used for testing open/write/close/unlink syscall).

Each worker creates a new thread that invokes `worker()` function with _iters_ iteration times. The worker() function runs the file syscalls (mkdir, rmdir, open, write, close, unlink) sequentially. Different with directly using syscall, worker calls a wrapper for the syscall, which adds a random time (1~100ms) sleeping and mutex lock to ensure that multiple threads share the same resource (dir, file) without race condition.

## Event Data Structure

The data structure to record the events named as `struct test_event` which includes several fields:

- **struct timespec ts**: the timediff start from the beginning of program
- **ssize_t ret**: the return value of tested f/s syscalls
- **int err**: error number
- **int workerid**: `worker_id` the id of worker from `0` to `n_workers-1`
- **char func[10]**: the name of function that used to test (e.g., mkdir/open)
- **char \*argstr**: variable argument string for f/s syscalls

A struct named `event_vec` is used to organize the multiple events. We will output the details of the execution based on `event_vec`.

## Output

After the execuation of `./test`, it will generate two files: test.log and test.log.json. These are the output of recorded events with plain text and JSON format respectively. The formats of output are written as follows:

- **test.log**: \
[seconds.nanoseconds] thread: worker/thread id, func = 'syscall function name' (mkdir/rmdir/open/write/etc.), ret = return value with name of the function, error = error name with errno
- **test.log.json**: \
{ \
  &nbsp; &nbsp;"ts": seconds.nanoseconds, (the time used from beginning of the program) \
  &nbsp; &nbsp;"thread": worker/thread id, (from `0` to `n_workers-1`) \
  &nbsp; &nbsp;"func": "syscall function name", (mkdir/rmdir/open/write/etc.) \
  &nbsp; &nbsp;"ret": return value, \
  &nbsp; &nbsp;"err": error number, \
  &nbsp; &nbsp;"args": a json format of arguments used for syscall (e.g., path, flags, mode) \
}
