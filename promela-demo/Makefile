COMMON_DIR=../common
override CFLAGS += -I../include -D PRINTF

all: demo.pml
	spin -a demo.pml; \
	gcc -o pan pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS) -pthread;  \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

clean:
	rm -rf test test.txt pan* \
	rm -rf /mnt/test-*/test*
