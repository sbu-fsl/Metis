COMMON_DIR=../common
override CFLAGS += -g -I../include -D PRINTF -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread # -D T_RAND -D P_RAND
#set VECTORSZ=10486000 if test ramdisk (CONFIG_BLK_DEV_RAM) Default: 2100000

all: demo.pml abstractfs operations
	./gen_parameters.sh > parameters.pml; \
	spin -a demo.pml; \
	gcc -o pan pan.c fileutil.c swapperf.c perf.c operations.o mount.c $(COMMON_DIR)/*.c abstract_fs.a $(CFLAGS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

abstractfs: $(COMMON_DIR)/abstract_fs.cpp
	g++ -std=c++11 -fPIC -I../include -o abstract_fs.o -c $<
	ar rcs abstract_fs.a abstract_fs.o

operations: $(COMMON_DIR)/operations.c
	gcc -o operations.o -I../include -c $<

abstractfs-test: $(COMMON_DIR)/abstract_fs.cpp
	g++ -std=c++11 -g -Wall -Werror -o absfs $< -DABSFS_TEST \
		-I../include -lssl -lcrypto -lrt -lstdc++ -lstdc++fs

pathutils: $(COMMON_DIR)/path_utils.cpp
	g++ -fPIC -I../include -o path_utils.o -c $<
	ar rcs path_utils.a path_utils.o

replayer: replay.c operations.c mount.c
	gcc -o replay replay.c operations.c mount.c \
		-DNO_FS_STAT $(COMMON_DIR)/*.c $(CFLAGS)

clean:
	rm -rf test test.txt pan* *.log *.o *.a absfs *.trail \
	rm -rf /mnt/test-*/test*
