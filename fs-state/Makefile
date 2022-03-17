COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../include -D PRINTF -DSWARMID=$(ARGS) # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz
PAN = pan

all: demo.pml parameters common-libs globals absfs-set
	spin -a demo.pml; \
	gcc -g -o $(PAN) pan.c init_globals.o set.o fileutil.c perf.c mount.c setup.c common-libs.a $(CFLAGS) $(LIBS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

globals: init_globals.c
	gcc -Wall -Werror -o init_globals.o -c $< $(CFLAGS) $(LIBS)

init_globals.o: globals

install: cleanlib globals absfs-set libsmcfs
	spin -a demo.pml;

cleanlib:
	rm -rf *.o

libsmcfs: init_globals.o set.o fileutil.o perf.o mount.o setup.o $(COMMON_OBJ)
	ar rvs $@$(ARGS).a $^

parameters: parameters.py parameter_util.py
	python3 parameters.py

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

absfs-set: set.cpp globals
	g++ -std=c++11 -o set.o -c $< $(CFLAGS) $(LIBS)
	
abstractfs-test: $(COMMON_DIR)/abstract_fs.cpp common-libs
	g++ -std=c++11 -g -Wall -Werror -o absfs $< common-libs.a -DABSFS_TEST \
		-I../include -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lprofiler -lxxhash -lz

replayer: replay.c mount.c common-libs
	gcc -o replay replay.c mount.c \
		-DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

clean:
	rm -rf test test.txt pan* *.log *.csv *.o *.a absfs *.trail script* swarm_done* .pml_tmp demo.pml.swarm \
	rm -rf /mnt/test-*/test*
