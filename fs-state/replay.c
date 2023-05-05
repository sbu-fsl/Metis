#include "replayutil.h"

int seq = 0;

vector_t states;

/* Before running this program, you need to specify a sequence.log file
 * Usage: sudo ./replay -K 0:ext4:256:jfs:16384 2>&1 > replay_jfs.log
 */
int main(int argc, char **argv)
{
	FILE *seqfp = fopen("sequence.log", "r");
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
		} else if (strncmp(funcname, "rename", len) == 0) {
			do_rename(&argvec);
		} else if (strncmp(funcname, "symlink", len) == 0) {
			do_symlink(&argvec);
		} else if (strncmp(funcname, "link", len) == 0) {
			do_link(&argvec);
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
