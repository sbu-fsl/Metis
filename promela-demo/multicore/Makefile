all: multicore.pml
	spin -a multicore.pml; \
	gcc -o pan -DNCORE=8  pan.c;

clean:
	rm pan*
