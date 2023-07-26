#include "replayutil.h"

#define DUMP_REPLAY_IMAGES 1

// The seq number to dump images (dump images only if seqid greater or equal to this value)
#define SEQID_DUMP_THRESHOLD 17126800

int seq = 0;

vector_t states;

/* Replayer dump device utilities */
static size_t state_depth = 0;

static int ensure_dump_dir(const char *folder)
{
    struct stat st;
    int ret = stat(folder, &st);
    /* Try creating the folder if it doesn't exist */
    if (ret < 0 && errno == ENOENT) {
        ret = mkdir(folder, 0755);
        if (ret < 0) {
            fprintf(stderr, "[ERROR]: %s: cannot create folder %s (%s)\n", __func__,
                    folder, errnoname(errno));
            return -errno;
        }
    } else if (ret < 0) {
        fprintf(stderr, "[ERROR]: %s: failed to stat %s, error is %s\n", __func__,
                folder, errnoname(errno));
        return -errno;
    } else {
        if (!S_ISDIR(st.st_mode)) {
            errno = ENOTDIR;
            fprintf(stderr, "[ERROR]: %s: folder %s is not a directory.\n", __func__,
                    folder);
            return -ENOTDIR;
        }
    }
    return 0;
}


static void dump_replay_mmaped(const char *folder, int i, char *fs_img)
{
	char outpath[PATH_MAX] = {0};
	snprintf(outpath, PATH_MAX, "%s/%s-mmap-%d-%zu.img", folder,
            get_fslist()[i], seq, state_depth);
    const size_t bs = 4096;
    int dmpfd = open(outpath, O_CREAT | O_RDWR | O_TRUNC, 0666);
    if (dmpfd < 0) {
        fprintf(stderr, "[ERROR]: cannot create file %s", outpath);
        return;
    }

	int fsfd = open(get_devlist()[i], O_RDWR);
    size_t remaining = fsize(fsfd);
    char *ptr = fs_img;
    while (remaining > 0) {
        size_t writelen = (remaining >= bs) ? bs : remaining;
        ssize_t writeres = write(dmpfd, ptr, writelen);
        if (writeres < 0) {
            fprintf(stderr, "[ERROR]: cannot write data to image dump %s", outpath);
            close(dmpfd);
            break;
        }
        ptr += writeres;
        remaining -= writeres;
    }
    close(dmpfd);
	close(fsfd);
}

static void dump_replay_device(const char *folder, int i)
{
	char *devname = get_devlist()[i];
	char *fsname = get_fslist()[i];

    char cmd[ARG_MAX] = {0};
    snprintf(cmd, ARG_MAX, "dd if=%s of=%s/%s-dev-%d-%zu.img bs=4k status=none",
             devname, folder, fsname, seq, state_depth);
    int status = system(cmd);
    if (WIFEXITED(status)) {
        if (WEXITSTATUS(status) != 0) {
            fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd exited with %d.",
                    fsname, devname, WEXITSTATUS(status));
        }
    } else if (WIFSIGNALED(status)) {
        fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd was terminated by signal "
                "%d.", fsname, devname, WTERMSIG(status));
    } else {
        fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd has exit code %d.",
                fsname, devname, status);
    }
}

static void dump_replay_fs_images(const char *folder, char **fs_imgs)
{
    assert(ensure_dump_dir(folder) == 0);
    for (int i = 0; i < get_n_fs(); ++i) {
        /* Dump the mmap'ed object */
        dump_replay_mmaped(folder, i, fs_imgs[i]);
        /* Dump the device by direct copying */
        dump_replay_device(folder, i);
    }

}

int main(int argc, char **argv)
{
	FILE *seqfp = fopen("sequence-pan-20220522-182011-2443643.log", "r");
	ssize_t len;
	size_t linecap = 0;
	char *linebuf = NULL;
	if (!seqfp) {
		printf("Cannot open sequence.log. Does it exist?\n");
		exit(1);
	}
	replayer_init(states);
	setup_filesystems();
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d ", seq);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);
		bool flag_ckpt = false, flag_restore = false;
		mountall();
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
			do_write_file(&argvec, seq);
		} else if (strncmp(funcname, "truncate", len) == 0) {
			do_truncate(&argvec);
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(&argvec);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(&argvec);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(&argvec);
		} else if (strncmp(funcname, "checkpoint", len) == 0) {
			flag_ckpt = true;
			seq--;
		} else if (strncmp(funcname, "restore", len) == 0) {
			flag_restore = true;
			seq--;
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		seq++;
		unmount_all_strict();
		if (flag_ckpt)
			checkpoint(seq, states);
		if (flag_restore)
			restore(states);
		errno = 0;
		free(line);
		destroy_fields(&argvec);
	}
	fclose(seqfp);
	free(linebuf);

	return 0;
}
