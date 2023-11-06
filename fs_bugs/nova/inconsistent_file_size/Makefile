CC=gcc

UTILITY_DIR := ../../test_utilities
ABSFS_DIR := ../../compute_absfs

UTILITY_SRC := $(wildcard $(UTILITY_DIR)/*.c)
UTILITY_OBJ := $(patsubst $(UTILITY_DIR)/%,%.o,$(UTILITY_SRC))

ABSFS_SRC := $(wildcard $(ABSFS_DIR)/*.c)
ABSFS_OBJ := $(patsubst $(ABSFS_DIR)/%,%.o,$(ABSFS_SRC))

ALL_OBJ := $(UTILITY_OBJ) $(ABSFS_OBJ)

override CFLAGS += -g -I../../compute_absfs -I../../test_utilities -I../../../include
override LIBS += -lssl -lcrypto -lrt -lpthread -lz -lm -lstdc++fs -lpthread -lprofiler -lxxhash -lstdc++
#-lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz

driver: driver.c all-libs
	$(CC) -o driver driver.c all-libs.a ../../../fs-state/common-libs.a $(CFLAGS) $(LIBS)

test: driver
	sudo bash -x run_driver.sh

all-libs: $(ALL_OBJ)
	ar rvs $@.a $^

%.c.o: $(UTILITY_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.c.o: $(ABSFS_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm -f *.o *.a driver ckpt_tmp.img
