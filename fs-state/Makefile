COMMON_DIR=../common
override CFLAGS += -g -I../include -D PRINTF -D VECTORSZ=525000 -lssl -lcrypto # -D T_RAND -D P_RAND

all: demo.pml
	spin -a demo.pml; \
	gcc -o pan pan.c fileutil.c $(COMMON_DIR)/*.c $(CFLAGS); \

run: all
	./pan | less -N; \
	rm -rf /mnt/test-*/test* || true; \

clean:
	rm -rf test test.txt pan* *.log \
	rm -rf /mnt/test-*/test*
