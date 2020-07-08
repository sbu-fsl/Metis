CC = gcc
#Cannot use -Werror because ‘__malloc_hook’ and other hooks are deprecated [-Wdeprecated-declarations]
CFLAGS = -g -O2 -Wall -I./include
BUILD = build
OBJECTS = run_malloc

all: $(BUILD) $(OBJECTS)

run: all
	./$(OBJECTS)

$(OBJECTS): %: %.c $(BUILD)/my_malloc.o $(BUILD)/malloc_hook.o
	$(CC) -o $@ $^ $(CFLAGS)

$(BUILD):
	-mkdir $(BUILD)

$(BUILD)/%.o: src/%.c
	$(CC) -c -o $@ $< $(CFLAGS)

clean:
	-rm -r $(BUILD)
	-rm $(OBJECTS)