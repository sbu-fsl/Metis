#!/bin/bash

# Output CSV file
CSV_FILE="verifs2_pan_process_metrics.csv"

# Function to get process metrics
get_process_metrics() {
    local process_name=$1
    local process_id=$(pgrep -o "$process_name")
    
    if [ -z "$process_id" ]; then
        echo "$process_name,Process not found,,,,,,,," >> $CSV_FILE
        return
    fi
    
    # Get process times and memory usage using ps
    local ps_output=$(ps -p $process_id -o pid,etime,utime,stime,cputime,rss --no-headers)
    
    # Extract times and memory usage
    local elapsed_time=$(echo $ps_output | awk '{print $2}')
    local user_time=$(ps -p $process_id -o etime=,utime= --no-headers | awk '{print $2}' | awk -F: '{if(NF==2) {print $1*60 + $2} else if (NF==3) {print $1*3600 + $2*60 + $3} else {print $1}}')
    local system_time=$(ps -p $process_id -o etime=,stime= --no-headers | awk '{print $2}' | awk -F: '{if(NF==2) {print $1*60 + $2} else if (NF==3) {print $1*3600 + $2*60 + $3} else {print $1}}')
    local cpu_time=$(ps -p $process_id -o etime=,cputime= --no-headers | awk '{print $2}' | awk -F: '{if(NF==2) {print $1*60 + $2} else if (NF==3) {print $1*3600 + $2*60 + $3} else {print $1}}')
    local mem_usage=$(echo $ps_output | awk '{print $6}')
    
    # Convert RSS from KB to bytes
    mem_usage=$((mem_usage * 1024))

    # Get I/O statistics from /proc
    local io_stats=$(cat /proc/$process_id/io)
    local read_bytes=$(echo "$io_stats" | grep "read_bytes" | awk '{print $2}')
    local write_bytes=$(echo "$io_stats" | grep "write_bytes" | awk '{print $2}')
    
    echo "$process_name,$elapsed_time,$user_time,$system_time,$cpu_time,$mem_usage,$read_bytes,$write_bytes"
}

# Initialize CSV file with headers
echo "Process,Elapsed Time (s),User Time (s),System Time (s),CPU Time (s),Memory Usage (bytes),Read Bytes,Write Bytes" > $CSV_FILE

# Infinite loop to record process metrics every 5 minutes
while true; do
    pan_metrics=$(get_process_metrics "pan")
    verifs2_metrics=$(get_process_metrics "verifs2")
    
    if [ ! -z "$pan_metrics" ]; then
        echo $pan_metrics >> $CSV_FILE
    fi
    
    if [ ! -z "$verifs2_metrics" ]; then
        echo $verifs2_metrics >> $CSV_FILE
    fi
    
    # Sleep for 5 minutes (300 seconds)
    sleep 300
done
