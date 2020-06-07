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
The test model will abort if there is a discrepancy of behavior between
TFS and RFS.

Use `make run` to run the test model.

