COMMON_DIR=../../common
override CFLAGS += -I../../include -D PRINTF

all: example2.pml
	spin -a example2.pml; \
	gcc -o pan pan.c $(COMMON_DIR)/*.c $(CFLAGS); \

run: all
	./pan | less -N;

clean:
	rm -rf test test.txt pan* *.log
