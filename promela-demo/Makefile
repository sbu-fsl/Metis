run: demo.pml
	spin -a demo.pml; \
	gcc -std=c99 -o pan pan.c fileutil.c; \
	./pan;

clean:
	rm -rf test test.txt pan* \
	rm -rf /mnt/test-*/test*
