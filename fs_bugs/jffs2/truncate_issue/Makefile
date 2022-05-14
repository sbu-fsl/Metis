write_file: write_file.c
	gcc -o write_file write_file.c

run: write_file
	sudo bash -x reproduce_jffs2_issue.sh

clean:
	rm -f write_file

