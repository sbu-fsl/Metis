#!/bin/bash

FTRACE_DIR="/sys/kernel/debug/tracing"

# ftrace step 1: disable tracing
sudo bash -c 'echo 0 > '$FTRACE_DIR'/tracing_on'

# ftrace step 2: set ftrace function tracer
sudo bash -c 'echo function > '$FTRACE_DIR'/current_tracer'

# ftrace step 3: set up Function Filters including all nilfs2 functions and down_write/up_write functions
sudo bash -c 'echo nilfs_* > '$FTRACE_DIR'/set_ftrace_filter'
sudo bash -c 'echo down_write >> '$FTRACE_DIR'/set_ftrace_filter'
sudo bash -c 'echo up_write >> '$FTRACE_DIR'/set_ftrace_filter'

# ftrace step 4: Tracing specific PID
sudo bash -c 'echo $$ > '$FTRACE_DIR'/set_ftrace_pid'

# ftrace step 5: Enable Tracing and Targetted tracing (trace events related to a specific command)
sudo bash -c 'echo 1 > '$FTRACE_DIR'/tracing_on'

# ftrace step (optional): Clear the trace
# sudo sh -c 'echo 0 > '$FTRACE_DIR'/trace'

# ftrace step 6: Collect Trace Data for operations
