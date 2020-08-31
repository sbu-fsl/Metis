CC=gcc
CFLAGS=-g -Wall -Wextra -Werror -c
OBJECT=arena_allocator

all: $(OBJECT).o
	$(CC) $^ -o $(OBJECT)

$(OBJECT).o: $(OBJECT).c
	$(CC) $(CFLAGS) $^ -o $@

clean:
	rm -rf $(OBJECT).o $(OBJECT)
