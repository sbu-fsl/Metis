CC := gcc
CFLAGS := -Wall -Wextra -std=c11

all: ganesha-small-dev

ganesha-small-dev: ganesha-small-dev.o
	$(CC) $(CFLAGS) -o ganesha-small-dev ganesha-small-dev.o

ganesha-small-dev.o: ganesha-small-dev.c
	$(CC) $(CFLAGS) -c ganesha-small-dev.c

clean:
	rm -f ganesha-small-dev *.o
