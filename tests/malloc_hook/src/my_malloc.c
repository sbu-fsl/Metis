#include "my_malloc.h"

static block_t *first = NULL;

/**
 * @param last The pointer to the last of block linked list
 * @param size The payload size
 */
block_t *create_mem_block(block_t *last, size_t size)
{
    if(size <= 0){
        return NULL;
    }

    block_t *brk_ptr;
    size_t new_size;
    size_t align_shift = 0;
    void *sbrk_ret;
    //Current program break
    brk_ptr = (block_t *)sbrk(0);
    //align address if it is not aligned
    if((size_t)brk_ptr % ALIGNMENT != 0){
        align_shift = ALIGNMENT - ((size_t)brk_ptr % ALIGNMENT);
        brk_ptr = (block_t*)((void*)brk_ptr + align_shift);
    }

    //The new size to extend
    new_size = MAX_VAL(ALIGN(size)+HEADER_SIZE, MINSIZE);

    sbrk_ret = sbrk(new_size + align_shift);
    //if sbrk failed
    if(sbrk_ret == (void*)-1 || sbrk_ret == NULL){
        return NULL;
    }
    else{
        //populate brk_ptr
        brk_ptr->next = NULL;
        brk_ptr->prev = last;
        //when create the block, the block_size == free_size
        brk_ptr->block_size = new_size - HEADER_SIZE;
        //isFree=0 means we MUST be able to use this created block
        //1(block is free)/0(block not free)
        brk_ptr->isFree = 0;
        memset(((char *)brk_ptr) + HEADER_SIZE, 0, size);
        if (last != NULL){
            last = brk_ptr;
        }
    }
    return brk_ptr;
}


block_t* find_free_block(block_t **last, size_t size)
{
    //Search free block from the first block
    block_t *block = first;
    //We want to find a block that is not NULL, isFree == 1, and block_size >= size
    while(block){
        if (block->isFree && block->block_size >= size){
            break;
        }
        else{
            //Update the last pointer
            *last = block;
            block =  block->next;
        }
    }
    return block;
}

void *my_malloc(size_t size)
{
    printf("Using my_malloc...\n");
    block_t *block, *last;    
    //align the size to ensure it is the multiple of ALIGNMENT
    size = ALIGN(size);

    //if the first block is allocated
    if(first != NULL){
        last = (block_t*)first;
        block = find_free_block(&last, size);
        //if found a suitable block
        if (block){
            block->block_size -= size;
            block->isFree = 0;
            //TODO: Split block?
        }
        //if cannot find a suitable block from current block list
        else{
            //extend mem by sbrk and create a new mem block after last
            block = create_mem_block(last, size);
            if (!block){
                return NULL;
            }
            else{
                last->next = block;
            }
        }
    }
    //if the first block is not allocated
    //for a large block allocation, 
    else{
        block = create_mem_block(NULL, size);
        //prev of first block is NULL
        block->prev = NULL;
        //if block is NULL return NULL
        if(!block){
            return NULL;
        }
        first = block;
    }
    if(block != NULL){
        return ((void*)block + HEADER_SIZE);
    }
    else{
        return NULL;
    }
    return NULL;
}

void print_block_list()
{
    block_t *ptr;
    //printf("first pointer when printing list: %p\n", first);
    for (ptr = first; ptr != NULL; ptr = ptr->next){
        char str[] = "null";
        if (ptr->isFree == 0){
            strcpy(str, "used");
        }
        else if (ptr->isFree == 1){
            strcpy(str, "free");
        }
        printf("prev=%p\t next=%p\t size=%ld\t isFree=%s\t data=%d\n",
            ptr->prev, ptr->next, ptr->block_size, str, (int)*ptr->data);
    }
}


void my_free(void* ptr){
    printf("Using my_free...\n");
    if (ptr == NULL){
        return;
    }
    block_t *block;

    block = (block_t*)(ptr - HEADER_SIZE);
    //Set as free
    block->isFree = 1;
    //if last block
    if (block->next == NULL){
        //re-set the break as the last block
        int brk_ret;
        brk_ret = brk(block);
        if (brk_ret == -1){
            printf("brk failed");
            exit(EXIT_FAILURE);
        }
        //also block is the first, clear first
        if(block->prev == NULL){
            first = NULL;
        }
        //not the first (has prev block)
        else{
            block->prev->next = NULL;
        }
    }
    //not last block (block->next != NULL)
    else{
        //next is free block, then merge
        if(block->next->isFree == 1){
            block->block_size += block->next->block_size + HEADER_SIZE;
            block->next = block->next->next;
            block->next->prev = block;
        }
        //has prev block and prev not free
        if(block->prev != NULL && block->prev->isFree == 1){
            block->prev->block_size += block->block_size + HEADER_SIZE;
            block->prev->next = block->next;
            if (block->next != NULL){
                block->next->prev = block->prev;
            }
        }
    }
}