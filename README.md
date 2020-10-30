# NFSv4 Model Checking Project

## Components:

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

### fs-state

The Spin-based file system model checker we are currently developing.
This checker will run a set of file system operations (system calls)
non-deterministically on multiple file systems, and then compare their
behavior. If there's any discrepancy, the checker will log it.

Please enter the folder to see detailed document and code.

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

### kernel

Kernel modules that helps the file system model checker

### common

Common code that will be use all other projects in this repo.

    * `errnoname.c`: Translate errno to its macro name
    * `nanotiming.c`: Timing utility functions

### include

    * `common_types.h`
    * `errnoname.h`
    * `nanotiming.h`
    * `path_utils.h`

