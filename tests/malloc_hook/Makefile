CC = gcc
#Cannot use -Werror because ‘__malloc_hook’ and other hooks are deprecated [-Wdeprecated-declarations]
CFLAGS = -g -O2 -Wall -I./include
BUILD = build
<<<<<<< HEAD
#HEADER = $(wildcard ./include/*.h)
OBJECTS = oneblock_hook mutliblock_hook test_heap

all: $(BUILD) $(OBJECTS)

=======
OBJECTS = run_malloc

all: $(BUILD) $(OBJECTS)

run: all
	./$(OBJECTS)

>>>>>>> a61a9f0bf2787bdd30bb38e23f2f6a870a2b43fb
$(OBJECTS): %: %.c $(BUILD)/my_malloc.o $(BUILD)/malloc_hook.o
	$(CC) -o $@ $^ $(CFLAGS)

$(BUILD):
	-mkdir $(BUILD)

$(BUILD)/%.o: src/%.c
	$(CC) -c -o $@ $< $(CFLAGS)

clean:
	-rm -r $(BUILD)
	-rm $(OBJECTS)