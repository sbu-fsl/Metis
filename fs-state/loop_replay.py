import subprocess
import time

# Replayer command to execute
command = "sudo ./replay -K 0:ext4:256:jfs:16384"

# Number of execution iterations
num_executions = 2

for i in range(num_executions):
    log_file = f"py_replay_jfs_{i + 1}.log"

    # Execute the command and capture output
    with open(log_file, "w") as log:
        process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

        # Continuously capture output and write to log file
        while True:
            output = process.stdout.readline()
            if output == b'' and process.poll() is not None:
                break
            if output:
                log.write(output.decode())
                print(output.decode(), end='')  # Print output to console as well

    # sleep (duration in secs) before next execution
    time.sleep(5)  