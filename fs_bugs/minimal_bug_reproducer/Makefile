CC=gcc
UTILITY_DIR := ../test_utilities
UTILITY_SRC := $(wildcard $(UTILITY_DIR)/*.c)
UTILITY_OBJ := $(patsubst $(UTILITY_DIR)/%,%.o,$(UTILITY_SRC))

override CFLAGS += -g -I../test_utilities 

reproducer: reproducer.c utility-libs
	$(CC) -o reproducer reproducer.c utility-libs.a $(CFLAGS) 

test: reproducer
	sudo bash -x run_reproducer.sh

utility-libs: $(UTILITY_OBJ)
	ar rvs $@.a $^

%.c.o: $(UTILITY_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) 

clean:
	rm -f *.o *.a reproducer
