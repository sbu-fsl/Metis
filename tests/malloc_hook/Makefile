CC = gcc
#Cannot use -Werror because ‘__malloc_hook’ and other hooks are deprecated [-Wdeprecated-declarations]
CFLAGS = -g -O2 -Wall -I./include
BUILD = build
#HEADER = $(wildcard ./include/*.h)
OBJECTS = oneblock_hook mutliblock_hook test_heap

all: $(BUILD) $(OBJECTS)

$(OBJECTS): %: %.c $(BUILD)/my_malloc.o $(BUILD)/malloc_hook.o
	$(CC) -o $@ $^ $(CFLAGS)

$(BUILD):
	-mkdir $(BUILD)

$(BUILD)/%.o: src/%.c
	$(CC) -c -o $@ $< $(CFLAGS)

clean:
	-rm -r $(BUILD)
	-rm $(OBJECTS)