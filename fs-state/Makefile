COMMON_DIR=../common
override CFLAGS += -g -I../include -iquote /home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/criu/include -I/home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/lib/c/ -I/home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/images/ -D PRINTF -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -L /home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/lib/c/ -L /home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/images/ -L. -lcriu #-D T_RAND -D P_RAND
#set VECTORSZ=10486000 if test ramdisk (CONFIG_BLK_DEV_RAM) Default: 2100000

TESTS += fileutil

#$(foreach t, $(TESTS), $(eval $(call genb, $(t))))

%.o: %.c
	gcc -c $^ -iquote /home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/criu/include -I/home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/lib/c/ -I/home/gomathi/criu-3.15/test/others/libcriu/../../../../criu/images/  abstract_fs.a  -o $@ -Werror

all: demo.pml abstractfs
	spin -a demo.pml; \
	gcc  -L. -lcriu -o pan pan.c fileutil.c swapperf.c perf.c operations.c mount.c $(COMMON_DIR)/*.c abstract_fs.a $(CFLAGS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

ramdisk: demo_ramdisk.pml
	spin -a demo_ramdisk.pml; \
	gcc -o pan pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

run_ramdisk: ramdisk
	./pan | less -N; \
	rm -rf /mnt/test-ramdisk-*/test* || true; \	

abstractfs: abstract_fs.cpp
	g++ -fPIC -I../include -o abstract_fs.o -c abstract_fs.cpp
	ar rcs abstract_fs.a abstract_fs.o

abstractfs-test: abstract_fs.cpp
	g++ -g -Wall -Werror -o absfs abstract_fs.cpp -DABSFS_TEST \
		-I../include -lssl -lcrypto -lrt -lstdc++ -lstdc++fs

pathutils: $(COMMON_DIR)/path_utils.cpp
	g++ -fPIC -I../include -o path_utils.o -c $(COMMON_DIR)/path_utils.cpp
	ar rcs path_utils.a path_utils.o

replayer: replay.c operations.c mount.c
	gcc -o replay replay.c operations.c mount.c \
		-DNO_FS_STAT $(COMMON_DIR)/*.c $(CFLAGS)

clean:
	rm -rf test test.txt pan* *.log *.o *.a absfs *.trail \
	rm -rf /mnt/test-*/test*
