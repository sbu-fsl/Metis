CC=gcc

driver: driver.c
	$(CC) -o driver driver.c

jffs2-test: driver
	sudo bash -x reproduce_jffs2_mkdir.sh jffs2

ext4-test: driver
	sudo bash -x reproduce_jffs2_mkdir.sh ext4
	
clean:
	rm -f driver
