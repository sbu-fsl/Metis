CC=gcc

mount_betrfs: mount_betrfs.c
	$(CC) -o mount_betrfs mount_betrfs.c

test: mount_betrfs
	sudo bash -x setup_betrfs.sh

test-loop: mount_betrfs
	sudo bash -x setup_betrfs.sh loop

clean:
	rm -f mount_betrfs dummy.dev
