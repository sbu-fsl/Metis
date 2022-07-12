CC=gcc

driver: driver.c
	$(CC) -o driver driver.c

run: driver
	sudo bash -x reproduce_jffs2_mkdir.sh

clean:
	rm -f driver
