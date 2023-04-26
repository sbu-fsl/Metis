#include "mounts.h"
#include "fstestutil.h"

#define MAX_LINE_LENGTH 256

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
    char reverse_line[MAX_LINE_LENGTH];
    char line[MAX_LINE_LENGTH];
    int ch, count, i, j;
    long offset;
    bool found_checkpoint = 0;

    // Read sequence file from bottom to top
    fp = fopen(seqlog, "r");
    if (fp == NULL) {
        fprintf(stderr, "Failed to open sequence file\n");
        exit(1);
    }

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

    printf("Got offset: %ld\n", offset);

    // Close the file
    fclose(fp);

    return 0;
}
