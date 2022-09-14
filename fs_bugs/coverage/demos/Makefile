CC=gcc
UTILITY_DIR := ../../test_utilities
UTILITY_SRC := $(wildcard $(UTILITY_DIR)/*.c)
UTILITY_OBJ := $(patsubst $(UTILITY_DIR)/%,%.o,$(UTILITY_SRC))

override CFLAGS += -g -I../../test_utilities 

syscall_seqs: syscall_seqs.c utility-libs
	$(CC) -o syscall_seqs syscall_seqs.c utility-libs.a $(CFLAGS)

test: syscall_seqs
	sudo bash -x run_syscalls.sh

utility-libs: $(UTILITY_OBJ)
	ar rvs $@.a $^

%.c.o: $(UTILITY_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS)

clean:
	rm -f *.o *.a syscall_seqs
