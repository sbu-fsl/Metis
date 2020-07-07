#include "hashtable.h"

struct DataItem* hashArray[SIZE];
struct DataItem* item;

int hashCode(int key) {
   return key % SIZE;
}

// search for the special value set; return -1 when not found
int searchValue(int key, int offset, int count, int file_len, int type) {
   struct DataItem* target = search(key);
   if(target == NULL) {
      return NOT_FOUND;
   }
   else {
      while(target != NULL) {
         if(target->offset == offset && target->count == count && target->file_len == file_len) {
            if(target->type == type) {
               return FOUND_STYPE;
            }
            else {
               return FOUND_DTYPE;
            }
         }
         target = target->nextItem;
      }
      return NOT_FOUND;
   }
}

struct DataItem *search(int key) {
   // get the hash 
   int hashIndex = hashCode(key);  
	if(hashArray[hashIndex] == NULL) {
      return NULL;
   }
   return hashArray[hashIndex];      
}

void insert(int key, int offset, int count, int file_len, int type) {
   struct DataItem *item = (struct DataItem*) malloc(sizeof(struct DataItem));
   item->offset = offset;
   item->count = count;
   item->file_len = file_len;
   item->key = key;

   // get the hash 
   int hashIndex = hashCode(key);
	if(hashArray[hashIndex] == NULL) {
      hashArray[hashIndex] = item;
   }
   // already have an item in this position
   struct DataItem *cursor = hashArray[hashIndex];
   while(cursor->nextItem != NULL) {
      cursor = cursor->nextItem;
   }
   cursor->nextItem = item;
   item->nextItem = NULL;
}

// insert when there is no item having the same value; return -1 if assert failed.
int safeInsert(int key, int offset, int count, int file_len, int type) {
   int retval = searchValue(key, offset, count, file_len, type);
   if(retval == NOT_FOUND) {
      insert(key, offset, count, file_len, type);
      return INSERT_SUCCESS;
   }
   else if(retval == FOUND_STYPE) {
      // exactly same record, ignore
      return INSERT_SUCCESS;
   }
   else {
      // FOUND_DSTYPE
      return INSERT_FAIL;
   }
}

int randnum(int min, int max) {
   return ((rand() % (int)(((max) + 1) - (min))) + (min));
}