CC=gcc

jffs2_eio_reproducer: jffs2_eio_reproducer.c
	$(CC) -o jffs2_eio_reproducer jffs2_eio_reproducer.c

jffs2-test: jffs2_eio_reproducer
	sudo bash -x reproduce_jffs2_eio.sh jffs2
	
clean:
	rm -f reproduce_jffs2_eio
