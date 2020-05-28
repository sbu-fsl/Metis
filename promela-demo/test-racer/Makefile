COMMON_DIR=../../common
override CFLAGS += -I../../include -D PRINTF

all: demo.pml
	spin -a demo.pml; \
	gcc -o pan pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

bitstate: demo.pml
	spin -a demo.pml; \
	gcc -DBITSTATE -o bitstate pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

bitstate_random: demo.pml
	spin -a demo.pml; \
	gcc -DBITSTATE -DT_RAND -DP_RAND -o bitstate_random pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

clean:
	rm -rf test test.txt pan* \
	rm -rf /mnt/test-*/test*
