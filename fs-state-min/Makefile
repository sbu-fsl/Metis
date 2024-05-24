override CFLAGS += -g -D PRINTF -fcommon -DCBUF_IMAGE -DFILEDIR_POOL -DCOMPLEX_FSOPS # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz -lm

cleanlib:
	rm -rf *.o

replayer_min: replay_min.c
	gcc -o replay_min replay_min.c -DNO_FS_STAT $(CFLAGS) $(LIBS)
				
clean:
	rm -rf test test.txt pan* *.log *.csv *.o *.a *.img absfs *.trail script* swarm_done* .pml_tmp mcfs-main.pml.swarm \
	rm -rf /mnt/test-*/test*
