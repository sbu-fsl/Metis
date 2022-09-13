


int main(int argc, char *argv[])
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <mountpoint> <loop_max>\n", argv[0]);
        exit(1);
    }
    char *mp = NULL;
    char *char_dev = "mtd0", *blk_dev = "/dev/mtdblock0";

    while (loop_id < loop_max) {
        
    }
    return 0;
}
