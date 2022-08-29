CC=gcc

write_file: driver.c
	$(CC) -o driver driver.c

run: write_file 
	sudo bash run_test.sh

clean:
	rm -f driver 
