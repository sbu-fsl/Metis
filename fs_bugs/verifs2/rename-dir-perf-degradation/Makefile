CC=gcc
CFLAGS=-Wall -g
TARGETS=rename-dirs-assert rename-dirs-basic

all: $(TARGETS)

rename-dirs-assert: rename-dirs-assert.c
	$(CC) $(CFLAGS) -o rename-dirs-assert rename-dirs-assert.c

rename-dirs-basic: rename-dirs-basic.c
	$(CC) $(CFLAGS) -o rename-dirs-basic rename-dirs-basic.c

clean:
	rm -f $(TARGETS)
