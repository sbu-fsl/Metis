CC=gcc
UTILITY_DIR := ../../test_utilities
UTILITY_SRC := $(wildcard $(UTILITY_DIR)/*.c)
UTILITY_OBJ := $(patsubst $(UTILITY_DIR)/%,%.o,$(UTILITY_SRC))

override CFLAGS += -g -I../../test_utilities 
override LIBS += -lssl -lcrypto -lrt -lpthread -lz

driver: driver.c utility-libs
	$(CC) -o driver driver.c utility-libs.a $(CFLAGS) $(LIBS)

test: driver
	sudo bash -x run_driver.sh

utility-libs: $(UTILITY_OBJ)
	ar rvs $@.a $^

%.c.o: $(UTILITY_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm -f driver
