COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../include -D PRINTF -fcommon -DCBUF_IMAGE -DFILEDIR_POOL -DCOMPLEX_FSOPS # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz -lm
PAN = pan

cleanlib:
	rm -rf *.o

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

# replayer_min: replay_min.c init_globals_min.o setup_min.c common-libs
# 	gcc -o replay_min replay_min.c init_globals_min.o setup_min.c \
#                 -DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)

replayer_min: replay_min.c init_globals_min.o common-libs
	gcc -o replay_min replay_min.c init_globals_min.o \
                -DNO_FS_STAT common-libs.a $(CFLAGS) $(LIBS)
				
replayutil_min.o: replayutil_min.c
	gcc -o replayutil_min.o -fPIC -c replayutil_min.c $(CFLAGS) $(LIBS)
		
init_globals_min.o: init_globals_min.c
	gcc -Wall -Werror -o init_globals_min.o -c $< $(CFLAGS) $(LIBS)

clean:
	rm -rf test test.txt pan* *.log *.csv *.o *.a *.img absfs *.trail script* swarm_done* .pml_tmp mcfs-main.pml.swarm \
	rm -rf /mnt/test-*/test*
