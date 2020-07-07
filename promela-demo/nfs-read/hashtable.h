#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

#ifndef _HASHTABLE_H_
#define _HASHTABLE_H_

#define SIZE 20

struct DataItem {
   int key;
   int offset;
   int count;
   int file_len;
   int type;
   struct DataItem *nextItem;
};

enum RETVAL {
    // STYPE-> same type; DTYPE->different type
    // found same record with the same type or not found return insert_success
    // found same record with a different type return insert_fail
    NOT_FOUND, FOUND_STYPE, FOUND_DTYPE, INSERT_SUCCESS, INSERT_FAIL
};

int hashCode(int key);
struct DataItem *search(int key);
int searchValue(int key, int offset, int count, int file_len, int type);
void insert(int key, int offset, int count, int file_len, int type);
int safeInsert(int key, int offset, int count, int file_len, int type);
int randnum(int min, int max);

#endif