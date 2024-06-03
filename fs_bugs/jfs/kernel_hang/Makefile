override CFLAGS += -g -D PRINTF -fcommon
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz -lm

cleanlib:
	rm -rf *.o

replayer: replay.c
	gcc -o replay replay.c $(CFLAGS) $(LIBS)
				
clean:
	rm -rf test test.txt pan* *.log *.csv *.o *.a *.img absfs *.trail script* swarm_done* .pml_tmp mcfs-main.pml.swarm \
	rm -rf /mnt/test-*/test*