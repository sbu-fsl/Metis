#include "circular_buf.h"

void circular_buf_init(circular_buf_sum_t **fsimg_bufs, int n_fs, size_t *devsize_kb) {
    // init circular_buf_sum
    (*fsimg_bufs) = malloc(sizeof(circular_buf_sum_t));
    (*fsimg_bufs)->buf_num = n_fs;
    (*fsimg_bufs)->cir_bufs = calloc(n_fs, sizeof(circular_buf_t));

    // init circular_buf
    for(int i = 0; i < n_fs; ++i) {
        (*fsimg_bufs)->cir_bufs[i].head_idx = 0;
        // init fsimg_buf
        for (int j = 0; j < BUF_SIZE; ++j) {
            (*fsimg_bufs)->cir_bufs[i].img_buf[j].state = malloc(devsize_kb[i] * KB_TO_BYTES);
            (*fsimg_bufs)->cir_bufs[i].img_buf[j].ckpt = true;
            (*fsimg_bufs)->cir_bufs[i].img_buf[j].depth = 0;
            (*fsimg_bufs)->cir_bufs[i].img_buf[j].seqid = 0;
        }
    }
}

void insert_circular_buf(circular_buf_sum_t *fsimg_bufs, int fs_idx, 
                            size_t devsize_kb, void *save_state, 
                            size_t state_depth, size_t seq_id, bool is_ckpt) 
{
    size_t head = fsimg_bufs->cir_bufs[fs_idx].head_idx;

    memcpy(fsimg_bufs->cir_bufs[fs_idx].img_buf[head].state, save_state, 
        devsize_kb * KB_TO_BYTES);
    fsimg_bufs->cir_bufs[fs_idx].img_buf[head].depth = state_depth;
    fsimg_bufs->cir_bufs[fs_idx].img_buf[head].seqid = seq_id;
    fsimg_bufs->cir_bufs[fs_idx].img_buf[head].ckpt = is_ckpt;

    fsimg_bufs->cir_bufs[fs_idx].head_idx = (head + 1) % BUF_SIZE;
}

void dump_all_circular_bufs(circular_buf_sum_t *fsimg_bufs, char **fslist, 
    size_t *devsize_kb)
{
    size_t head = 0; 
    size_t state_depth = 0;
    size_t seq_id = 0;
    bool is_ckpt = true;
    char dump_path[PATH_MAX] = {0};
    const size_t bs = 4096;
    int dmpfd = -1;

    for(size_t i = 0; i < fsimg_bufs->buf_num; ++i) {
        head = fsimg_bufs->cir_bufs[i].head_idx;
        for(size_t j = 0; j < BUF_SIZE; ++j) {
            size_t idx = (j + head) % BUF_SIZE;
            state_depth = fsimg_bufs->cir_bufs[i].img_buf[idx].depth;
            seq_id = fsimg_bufs->cir_bufs[i].img_buf[idx].seqid;
            is_ckpt = fsimg_bufs->cir_bufs[i].img_buf[idx].ckpt;

            // example: cbuf-ext4-state-3846-seq-123456-ckpt-0.img
            if (is_ckpt) {
                snprintf(dump_path, PATH_MAX, 
                    "cbuf-%s-state-%zu-seq-%zu-ckpt-%zu.img", 
                    fslist[i], state_depth, seq_id, j);
            }
            else {
                snprintf(dump_path, PATH_MAX, 
                    "cbuf-%s-state-%zu-seq-%zu-restore-%zu.img", 
                    fslist[i], state_depth, seq_id, j);                
            }

            dmpfd = open(dump_path, O_CREAT | O_RDWR | O_TRUNC, 0666);
            if (dmpfd < 0) {
                fprintf(stderr, "Cannot create file: %s\n", dump_path);
                exit(1);
            }

            size_t remaining = devsize_kb[i] * 1024;
            char *ptr = fsimg_bufs->cir_bufs[i].img_buf[idx].state;
            while (remaining > 0) {
                size_t writelen = (remaining >= bs) ? bs : remaining;
                ssize_t writeres = write(dmpfd, ptr, writelen);
                if (writeres < 0) {
                    fprintf(stderr, "Cannot write to file: %s\n", dump_path);
                    close(dmpfd);
                    exit(1);
                }
                ptr += writeres;
                remaining -= writeres;
            }
            close(dmpfd);
        }
    }

}

void cleanup_cir_bufs(circular_buf_sum_t *fsimg_bufs)
{
    for(size_t i = 0; i < fsimg_bufs->buf_num; ++i) {
        for(size_t j = 0; j < BUF_SIZE; ++j) {
            if (fsimg_bufs->cir_bufs[i].img_buf[j].state)
                free(fsimg_bufs->cir_bufs[i].img_buf[j].state);
        }
    }

    if (fsimg_bufs->cir_bufs)
        free(fsimg_bufs->cir_bufs);

    if (fsimg_bufs)
        free(fsimg_bufs);
}
