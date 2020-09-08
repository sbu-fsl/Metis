COMMON_DIR=../common
override CFLAGS += -g -I../include -D PRINTF -D VECTORSZ=4200000 -lssl -lcrypto -lrt -lstdc++ # -D T_RAND -D P_RAND
#set VECTORSZ=10486000 if test ramdisk (CONFIG_BLK_DEV_RAM) Default: 2100000

all: demo.pml pathutils
	spin -a demo.pml; \
	gcc -o pan pan.c fileutil.c abstract_fs.c $(COMMON_DIR)/*.c path_utils.a $(CFLAGS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

ramdisk: demo_ramdisk.pml
	spin -a demo_ramdisk.pml; \
	gcc -o pan pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

run_ramdisk: ramdisk
	./pan | less -N; \
	rm -rf /mnt/test-ramdisk-*/test* || true; \	

pathutils: $(COMMON_DIR)/path_utils.cpp
	g++ -fPIC -I../include -o path_utils.o -c $(COMMON_DIR)/path_utils.cpp
	ar rcs path_utils.a path_utils.o

clean:
	rm -rf test test.txt pan* *.log *.o *.a absfs *.trail \
	rm -rf /mnt/test-*/test*
