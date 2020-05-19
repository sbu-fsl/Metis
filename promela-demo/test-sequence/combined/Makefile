override CFLAGS +=

all: example.pml
	spin -a example.pml; \
	gcc -o pan -D PRINTF $(CFLAGS) pan.c ; \

clean:
	rm -rf test test.txt pan* \
