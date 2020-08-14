#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// uint32_t size: 4 Bytes
struct blk {
    uint32_t index;
    uint32_t index_of_data;
    uint32_t size_of_data;
    uint32_t index_of_prev_block;
    uint32_t index_of_next_block;
    struct blk *prev;
    struct blk *next;
};

typedef struct blk block;

int blocks = 0;
unsigned char* arena = NULL;
uint32_t size_of_arena;
block *first = NULL;
block *last = NULL;

void init_arena(uint32_t size)
{
    //populate global variable arena_size (total size of arena in bytes)
    size_of_arena = size;
    //allocates memory to arena and calloc sets allocated memory to zero
    arena = malloc(size_of_arena);
    memset(arena, 0, size_of_arena);
    printf("Start addr of arena: %p\n", arena);
    printf("End addr of arena: %p\n", arena+size_of_arena);
}

void map_block_to_arena(block *b) {
    //the start index of the data area is always 12 bytes (3*4bytes uint32_t)longer higher than the beginning index of the block
    b->index_of_data = b->index + 12;

    //int type pointer at the beginning of the block management area
    uint32_t *int_arena = (uint32_t*)(arena + b->index);
    //writing the block management area in the arena 
    int_arena[0] = b->index_of_next_block;
    int_arena[1] = b->index_of_prev_block;
    int_arena[2] = b->size_of_data;
}

void unmap_block_from_arena(block *b) {
    //setting all bytes of the block to 0 
    for (uint32_t i = 0; i < b->size_of_data + 12; ++i)
        arena[b->index + i] = 0;
    //freeing up block memory
    b->next = NULL;
    b->prev = NULL;
    free(b);
}


int alloc_at_begining(uint32_t size) {
    // If has enough space to allocate
    if (size + 12 > size_of_arena){
        return 0;
    }
    // Increment the number of blocks
    blocks++;
    block *b = malloc(sizeof(block));
    //populate block structure
    b->index = 0;
    b->size_of_data = size;
    b->index_of_prev_block = 0;
    b->index_of_next_block = 0;
    b->prev = NULL;
    b->next = NULL;
    map_block_to_arena(b);
    //the newly allocated block will be both the first and the last block (only one block now)
    first = b;
    last = b;
    //return the index of data area
    return b->index_of_data;
}


int alloc_before_first_block(uint32_t size) {
    //increase the number of blocks and allocate a block structure 
    blocks++;
    block *b = malloc(sizeof(block));
    //filling in the fields of the allocated structure
    //Before the first block so the index of this block becomes 0
    b->index = 0;
    b->size_of_data = size;
    b->index_of_prev_block = 0;
    //Next block of this block is the old first block
    b->index_of_next_block = first->index;
    b->prev = NULL;
    //Connection of the old first block and new block
    first->index_of_prev_block = b->index;
    b->next = first;
    first->prev = b;
    //remapping the first block and mapping the assigned new block (first block info changed!)
    map_block_to_arena(b);
    map_block_to_arena(first);
    // new block becomes the first block
    first = b;
    // data area index
    return b->index_of_data;
}

int alloc_between(int block_index, uint32_t size) {
    block *a = first;
    //the blocks are scrolled, until the one with the block_index index is found
    //a is the block with block_index
    for (int i = 0; i < block_index; ++i)
        a = a->next;
    //block following the previous one found
    block *c = a->next;
    //if there is not enough space between the 2 blocks, we abandon the allocation between them 2
    //"c->index - (a->index_of_data + a->size_of_data" is the space between a and c
    if (size + 12 > c->index - (a->index_of_data + a->size_of_data)){
        return 0;
    }
    // if between a and c has enough space, increase the number of blocks and allocate a block structure
    blocks++;
    block *b = malloc(sizeof(block));
    // filling in the fields of the allocated structure
    b->index_of_prev_block = a->index;
    b->index_of_next_block = c->index;
    b->size_of_data = size;
    b->index = a->index_of_data + a->size_of_data;

    //updating the indexes of neighboring blocks
    c->index_of_prev_block = b->index;
    a->index_of_next_block = b->index;

    //forming the connection between the newly added block and the neighboring ones
    a->next = b;
    b->prev = a;
    b->next = c;
    c->prev = b;

    //remapping blocks in the arena
    map_block_to_arena(a);
    map_block_to_arena(b);
    map_block_to_arena(c);

    //data area index
    return b->index_of_data;
}

int alloc_at_end(uint32_t size) {
    //if there is no space after the last block in the arena, the requested block cannot be allocated
    if (last->index_of_data + last->size_of_data + size + 12 > size_of_arena){
        return 0;
    }
    //increasing the number of blocks and allocating a block structure
    blocks++;
    block *b = malloc(sizeof(block));
    //filling in the fields of the allocated structure
    b->index_of_prev_block = last->index;
    b->index_of_next_block = 0;
    b->size_of_data = size;
    //updating the indexes of the newly allocated blocks and the last block
    b->index = last->index_of_data + last->size_of_data;
    last->index_of_next_block = b->index;

    //forming the connection between the last block and the new one allocated
    b->prev = last;
    b->next = NULL;
    last->next = b;

    //remapping blocks in the arena
    map_block_to_arena(b);
    map_block_to_arena(last);

    //the newly allocated block will become the last
    last = b;
    //data area index
    return b->index_of_data;
}

void* my_malloc(uint32_t size) {
    uint32_t data_index;
    // There is no block assigned in arena
    if (first == NULL) {
        data_index = alloc_at_begining(size);
        printf("[DEBUG] alloc_at_begining: %d\n", data_index);
        if(data_index == 0){
            return NULL;
        }
        return (void*)(arena+data_index);
    }
    // if there is space, we will allocate before the first block
    //TODO: Why this condition? AIM TO ADD BEFORE THE FIRST BLOCK
    if (first->index >= size + 12) {
        data_index = alloc_before_first_block(size);
        printf("[DEBUG] alloc_before_first_block: %d\n", data_index);
        return (void*)(arena+data_index);
    }
    //we go through all the blocks and try the allocation between block i and block i + 1, if the allocation was successful we stop
    for (int i = 0; i < blocks - 1; ++i) {
        data_index = alloc_between(i, size);
        printf("[DEBUG] alloc_between: %d\n", data_index);
        if (data_index != 0) {
            return (void*)(arena+data_index);
        }
    }
    //block allocation at the end
    data_index = alloc_at_end(size);
    if (data_index != 0)
    {
        printf("[DEBUG] alloc_at_end: %d\n", data_index);
        return (void*)(arena+data_index);
    }
    else{
        return NULL;
    }
    return NULL;
}


void my_free(uint32_t index) {
    //decrementing the number of blocks
    blocks--;
    block *b = first;
    //as long as the current block exists
    while (b != NULL) {
        //if it is the block with the searched index
        if (b->index_of_data == index) {
            //blocks adjacent to the current block
            block *a = b->prev;
            block *c = b->next;

            //if has both neighbors
            if (a != NULL && c != NULL) {
                //we reconnect with them and remap the blocks in the arena
                a->next = c;
                a->index_of_next_block = c->index;
                c->prev = a;
                c->index_of_prev_block = a->index;
                map_block_to_arena(a);
                map_block_to_arena(c);
            //if it has only the left neighbor
            } else if (a != NULL && c == NULL) {
                //mark the left neighbor as the last block and remap it in the arena
                last = a;
                a->index_of_next_block = 0;
                a->next = NULL;
                map_block_to_arena(a);
            //if it has only the right neighbor
            } else if (a == NULL && c != NULL) {
                //mark the right neighbor as the first block and remap it in the arena
                first = c;
                c->index_of_prev_block = 0;
                c->prev = NULL;
                map_block_to_arena(c);
            //has no neighbors
            } else if (a == NULL && c == NULL) {
                first = NULL;
                last = NULL;
            }

            //unmap the block from the arena and stop the search
            unmap_block_from_arena(b);
            break;
        } else {
            //move to next block
            b = b->next;
        }
    }
}

void print_blocks_list()
{
    block *b = first;
    for (int i = 0; i < blocks; ++i) {
        printf("order=%d\t index=%d\t size=%d\t data_index=%d\t prev_index=%d\t next_index=%d\n",
            i+1, b->index, b->size_of_data, b->index_of_data, b->index_of_prev_block, b->index_of_next_block);
        b = b->next;
    }
}

int main(void)
{
    init_arena(1200);
    /*
    int str_size = 21;
    char *str = (char*)my_malloc(sizeof(char) * str_size);
    if(str != NULL){
        printf("str addr: %p\n", str);
    }
    else{
        printf("my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    strcpy(str, "randomtextrandomtext");
    printf("String is %s\n", str);
    */
    void* ret;

    ret = my_malloc(300);
    if(ret == NULL){
        printf("1my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    print_blocks_list();
    ret = my_malloc(200);
    if(ret == NULL){
        printf("2my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    ret = my_malloc(200);
    if(ret == NULL){
        printf("3my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    ret = my_malloc(200);
    if(ret == NULL){
        printf("4my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    ret = my_malloc(200);
    if(ret == NULL){
        printf("5my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    my_free(0);
    print_blocks_list();
    ret = my_malloc(100);
    if(ret == NULL){
        printf("6my_malloc failed\n");
        exit(EXIT_FAILURE);
    }
    printf("ret: %p\n", ret);

    return 0;
}