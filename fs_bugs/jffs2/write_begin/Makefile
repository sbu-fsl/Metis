CC=gcc

write_file: write_file.c
	$(CC) -o write_file write_file.c

read_file: read_file.c
	$(CC) -o read_file read_file.c

run: write_file read_file
	sudo bash -x reproduce_jffs2_write_begin_issue.sh

clean:
	rm -f write_file read_file
