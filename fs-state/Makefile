COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../include -D PRINTF # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler
PAN = pan

all: demo.pml parameters common-libs absfs-set
	spin -a demo.pml; \
	gcc -o $(PAN) pan.c set.o fileutil.c perf.c mount.c common-libs.a $(CFLAGS) $(LIBS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

parameters: parameters.py parameter_util.py
	python3 parameters.py

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

absfs-set: set.cpp
	g++ -std=c++11 -o set.o -c $< $(CFLAGS) $(LIBS)
	
abstractfs-test: $(COMMON_DIR)/abstract_fs.cpp common-libs
	g++ -std=c++11 -g -Wall -Werror -o absfs $< common-libs.a -DABSFS_TEST \
		-I../include -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lprofiler

replayer: replay.c mount.c common-libs
	gcc -o replay replay.c mount.c \
		-DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

clean:
	rm -rf test test.txt pan* *.log *.o *.a absfs *.trail \
	rm -rf /mnt/test-*/test*
