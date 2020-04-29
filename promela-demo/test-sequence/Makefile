all: example.pml
	spin -a example.pml; \
	gcc -o pan -D PRINTF -D NOREDUCE pan.c ; \

clean:
	rm -rf test test.txt pan* \
