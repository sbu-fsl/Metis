COMMON_DIR := ../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../fs-state -I../include -D PRINTF # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz

all: crmfs ckpt restore

install: crmfs
	cp crmfs /usr/local/bin/

crmfs: crmfs.c cr.cpp common-libs
	gcc $(CFLAGS) -o crmfs crmfs.c cr.cpp common-libs.a -lstdc++ -lrt -lfuse

ckpt: ckpt.c common-libs
	gcc $(CFLAGS) -o ckpt ckpt.c common-libs.a

restore: restore.c common-libs
	gcc $(CFLAGS) -o restore restore.c common-libs.a

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm -f ckpt restore crmfs *.o *.log .*.swp pan.* *.a pan

