#ifndef _CIRCULAR_BUF_H
#define _CIRCULAR_BUF_H

/* 
 * Note this is not a general-purpose circular buffer
 * It is designed for saving f/s concrete state (image) only
 */

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <linux/limits.h>

#define BUF_SIZE 10
#define KB_TO_BYTES 1024

struct fsimg_buf {
    void *state; // concrete state (f/s image buffer)
    bool ckpt; // if true, checkpointed image; if false, restored image
    size_t depth; // state_depth
    size_t seqid; // seq id (count) corresponds to the image
};

typedef struct fsimg_buf fsimg_buf_t;

// Circular buffer structure for each file system
struct circular_buf {
    fsimg_buf_t img_buf[BUF_SIZE];
    size_t head_idx; // [0, BUF_SIZE - 1]
};

typedef struct circular_buf circular_buf_t;

// Data structure to represent all the circular buffers in MCFS
// The number of circular buffer is equivalent to the number of file systems
struct circular_buf_sum {
    circular_buf_t *cir_bufs; // length is number of f/s 
    unsigned int buf_num; // number of file systems
};

typedef struct circular_buf_sum circular_buf_sum_t;

void circular_buf_init(circular_buf_sum_t *fsimg_bufs, int n_fs, size_t *devsize_kb);
void insert_circular_buf(circular_buf_sum_t *fsimg_bufs, int fs_idx, 
                            size_t devsize_kb, void *save_state, 
                            size_t state_depth, size_t seq_id, bool is_ckpt);
void dump_all_circular_bufs(circular_buf_sum_t *fsimg_bufs, char **fslist, 
    size_t *devsize_kb);

#endif // _CIRCULAR_BUF_H
