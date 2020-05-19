override CFLAGS +=

all: select-flags.pml
	spin -a select-flags.pml; \
	gcc -o pan -D PRINTF $(CFLAGS) pan.c;

clean:
	rm pan*
