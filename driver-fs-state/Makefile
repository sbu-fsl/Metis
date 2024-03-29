MY_OPEN_FLAG_PATTERN ?= 0
MY_WRITE_SIZE_PATTERN ?= 0
COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../include -D PRINTF -fcommon -DCBUF_IMAGE -DFILEDIR_POOL -DCOMPLEX_FSOPS -DOPEN_FLAG_PATTERN=$(MY_OPEN_FLAG_PATTERN) -DWRITE_SIZE_PATTERN=$(MY_WRITE_SIZE_PATTERN) # -D T_RAND -D P_RAND
override LIBS += -lm -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz
PAN = pan

all: mcfs-main.pml parameters common-libs init_globals.o absfs-set
	spin -a mcfs-main.pml; \
	gcc -g -o $(PAN) pan.c init_globals.o set.o fileutil.c perf.c mount.c setup.c common-libs.a $(CFLAGS) $(LIBS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

init_globals.o: init_globals.c
	gcc -Wall -Werror -o init_globals.o -c $< $(CFLAGS) $(LIBS)

install: cleanlib absfs-set libsmcfs
	spin -a mcfs-main.pml;

cleanlib:
	rm -rf *.o

libsmcfs: init_globals.o set.o fileutil.o perf.o mount.o setup.o $(COMMON_OBJ)
	ar rvs $@.a $^

parameters: parameters.py parameter_util.py
	python3 parameters.py

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

absfs-set: set.cpp init_globals.o
	g++ -std=c++11 -o set.o -c $< $(CFLAGS) $(LIBS)
	
abstractfs-test: $(COMMON_DIR)/abstract_fs.cpp common-libs
	g++ -std=c++11 -g -Wall -Werror -o absfs $< common-libs.a -DABSFS_TEST \
		-I../include -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lprofiler -lxxhash -lz

replayer: replay.c replayutil.o init_globals.o setup.c mount.c common-libs
	gcc -o replay replay.c replayutil.o init_globals.o setup.c mount.c \
		-DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

replayer_dump: replay_dump.c replayutil.o init_globals.o setup.c mount.c common-libs
	gcc -o replay_dump replay_dump.c replayutil.o init_globals.o setup.c mount.c \
		-DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

replayutil.o: replayutil.c 
	gcc -o replayutil.o -fPIC -c replayutil.c $(CFLAGS) $(LIBS)

min_repro: min_repro.c replayutil.o init_globals.o setup.c mount.c common-libs
	gcc -o min_repro min_repro.c replayutil.o init_globals.o setup.c mount.c \
		-DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

clean:
	rm -rf test test.txt pan* *.log *.csv *.o *.a *.img absfs *.trail script* swarm_done* .pml_tmp mcfs-main.pml.swarm \
	rm -rf /mnt/test-*/test*
