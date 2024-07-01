# This Makefile compiles and generates the executable for the replayer 
# that replays the sequence log for JFS

replayer: replay.c
	gcc -o replay replay.c

clean:
	rm -rf replay *.o
	rm -rf /mnt/test-*/test*
