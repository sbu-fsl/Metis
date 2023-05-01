#include "mounts.h"
#include "fstestutil.h"

#define MAX_LINE_LENGTH 256

static long find_last_checkpoint_offset(FILE *fp)
{
    int ch, count, i, j;
    long offset = 0;
    bool found_checkpoint = 0;
    char line[MAX_LINE_LENGTH];
    char reverse_line[MAX_LINE_LENGTH];
    // Move file pointer to the end of file
    fseek(fp, 0L, SEEK_END);

    // Read file backwards
    while (ftell(fp) > 1) {
        fseek(fp, -2, SEEK_CUR);
        if (ftell(fp) <= 2)
            break;
        // Read one character
        ch = fgetc(fp);
        count = 0;
        while(ch != '\n'){
            reverse_line[count] = ch;
            ++count;
            if(ftell(fp) < 2)
                break;
            fseek(fp, -2, SEEK_CUR);
            ch = fgetc(fp);
        }
        // Record current file offset
        offset = ftell(fp);
        // Reverse the line 
        j = 0;
        for (i = count - 1; i >= 0 && count > 0; i--) {
            line[j] = reverse_line[i];
            j++;
        }
        line[j] = '\0';
        // Check if the line contains the "checkpoint" string
        if (strstr(line, "checkpoint")) {
            found_checkpoint = 1;
            break;
        }
    }

    if (!found_checkpoint) {
        fprintf(stderr, "No checkpoint found in sequence file\n");
        fclose(fp);
        exit(1);
    }

    return offset;
}

int main(int argc, char **argv)
{
    if (argc < 8) {
        fprintf(stderr, "Usage %s seqlog fs1 fs2 mp1 mp2 dev1 dev2\n", argv[0]);
        exit(1);
    }

    char *seqlog = argv[1];
    char *fs1 = argv[2];
    char *fs2 = argv[3];
    char *mp1 = argv[4];
    char *mp2 = argv[5];
    char *dev1 = argv[6];
    char *dev2 = argv[7];

    FILE *fp;
    long offset;
    size_t len = 0;
    ssize_t read;
    char *rear_line = NULL;

    // Read sequence file from bottom to top
    fp = fopen(seqlog, "r");
    if (fp == NULL) {
        fprintf(stderr, "Failed to open sequence file\n");
        exit(1);
    }

    offset = find_last_checkpoint_offset(fp);
    printf("Got offset: %ld\n", offset);

    // Seek to offset
    fseek(fp, offset, SEEK_SET);

    // Read the file from the offset
    while ((read = getline(&rear_line, &len, fp)) != -1) {
        // printf("Retrieved line of length %zu:\n", read);
        printf("%s", rear_line);
    }

    // Close the file
    fclose(fp);

    if (rear_line) {
        free(rear_line);
    }

    return 0;
}
