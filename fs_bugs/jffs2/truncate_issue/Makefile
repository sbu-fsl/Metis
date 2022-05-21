CC=gcc

write_file: write_file.c
	$(CC) -o write_file write_file.c

run: write_file
	sudo bash -x reproduce_jffs2_issue.sh

clean:
	rm -f write_file

