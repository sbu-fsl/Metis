/*
 * MCFS minimal bug reproducer 
 */
#include "replayutil.h"

#define MAX_LINE_LENGTH 256

int seq = 0;

static long find_last_checkpoint_offset(FILE *seqfp)
{
    int ch, count, i, j;
    long offset = 0;
    bool found_checkpoint = 0;
    char forward_line[MAX_LINE_LENGTH];
    char reverse_line[MAX_LINE_LENGTH];
    // Move file pointer to the end of file
    fseek(seqfp, 0L, SEEK_END);

    // Read file backwards
    while (ftell(seqfp) > 1) {
        fseek(seqfp, -2, SEEK_CUR);
        if (ftell(seqfp) <= 2)
            break;
        // Read one character
        ch = fgetc(seqfp);
        count = 0;
        while(ch != '\n'){
            reverse_line[count] = ch;
            ++count;
            if(ftell(seqfp) < 2)
                break;
            fseek(seqfp, -2, SEEK_CUR);
            ch = fgetc(seqfp);
        }
        // Record current file offset
        offset = ftell(seqfp);
        // Reverse the line 
        j = 0;
        for (i = count - 1; i >= 0 && count > 0; i--) {
            forward_line[j] = reverse_line[i];
            j++;
        }
        forward_line[j] = '\0';
        // Check if the line contains the "checkpoint" string
        if (strstr(forward_line, "checkpoint")) {
            found_checkpoint = 1;
            break;
        }
    }

    if (!found_checkpoint) {
        fprintf(stderr, "No checkpoint found in sequence file\n");
        fclose(seqfp);
        exit(1);
    }

    return offset;
}

int main(int argc, char **argv)
{
    if (argc < 4) {
        fprintf(stderr, "Usage: %s -K fs1:size1:fs2:size2 seqlog \n", argv[0]);
        exit(1);
    }
    char *seqlog = argv[3];
    FILE *seqfp;
    long offset;
    size_t linecap = 0;
    ssize_t len;
    char *linebuf = NULL;

    srand(time(0));

    // Read sequence file from bottom to top
    seqfp = fopen(seqlog, "r");
    if (seqfp == NULL) {
        fprintf(stderr, "Cannot open sequence.log. Does it exist?\n");
        exit(1);
    }

    offset = find_last_checkpoint_offset(seqfp);
    printf("Got offset: %ld\n", offset);

    // Seek to offset of last checkpoint
    fseek(seqfp, offset, SEEK_SET);

    // Read the file from the offset
    while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
        // Copy the line
        char *line = malloc(len + 1);
        line[len] = '\0';
        strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
        /* parse the line */
        vector_t argvec;
        extract_fields(&argvec, line, ", ");
        char *funcname = *vector_get(&argvec, char *, 0);
        // Mount the file systems
        mountall();
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
            seq = rand() % 256;
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
		} else if (strncmp(funcname, "checkpoint", len) != 0 && 
                   strncmp(funcname, "restore", len) != 0) {
			printf("Unrecognized op: %s\n", funcname);
            exit(1);
		}
        // Unmount the file systems
        unmount_all_strict();
		free(line);
		destroy_fields(&argvec);
    }
    // Close the file
    fclose(seqfp);
    if (linebuf) {
        free(linebuf);
    }

    return 0;
}
