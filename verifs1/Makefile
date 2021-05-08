COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../include -D PRINTF # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread 

all: crmfs ckpt restore model-checker

model-checker: mc.pml parameters fileutil.c mount.c perf.c common-libs absfs-set
	spin -a mc.pml
	gcc -g -o pan pan.c fileutil.c mount.c perf.c set.o common-libs.a $(CFLAGS) $(LIBS)

parameters: parameters.py parameter_util.py
	python3 parameters.py

crmfs: crmfs.c cr.cpp common-libs
	gcc $(CFLAGS) -o crmfs crmfs.c cr.cpp common-libs.a -lstdc++ -lrt -lfuse

ckpt: ckpt.c common-libs
	gcc $(CFLAGS) -o ckpt ckpt.c common-libs.a

restore: restore.c common-libs
	gcc $(CFLAGS) -o restore restore.c common-libs.a

absfs-set: set.cpp
	g++ -std=c++11 -o set.o -c $< $(CFLAGS) $(LIBS)

replayer: replay.c common-libs 
	gcc -o replay replay.c common-libs.a $(CFLAGS) $(LIBS)

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm -f ckpt restore crmfs *.o *.log .*.swp pan.* *.a pan

