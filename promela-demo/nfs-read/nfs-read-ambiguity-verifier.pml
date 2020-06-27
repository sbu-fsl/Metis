c_code {
    \#include "hashtable.c"
    \#include <time.h>
}

c_track "dummyItem" "sizeof(void *)"

chan randr = [3] of {int, int, int};

proctype getRand() {
    int offset, file_len, count;
    c_code {
        PgetRand->offset = randnum(1, 10000);
    }
    c_code {
        PgetRand->file_len = randnum(1, 10000);
    }
    c_code {
        PgetRand->count = randnum(1, 10000);
    }
    randr ! offset, file_len, count;
}

init {
    // seet random seed
    c_code {
        srand(time(NULL));
    }
    // set up dummyItem
    c_code {
        dummyItem = (struct DataItem *) malloc(sizeof(struct DataItem));
        dummyItem -> data = -1;
        dummyItem -> key = -1;
    }
    int offset, file_len, count;
    int loops = 20;
    int counter = 0;
    do
        ::(counter < loops) -> {
            run getRand();
            randr ? offset, file_len, count;
            if
                ::(offset >= file_len) -> {
                    c_code {
                        int key = Pinit->offset + Pinit->file_len + Pinit->count;
                        struct DataItem *data = search(key);
                        if(data == NULL) {
                            insert(key, 1);
                        }
                        else if(data->data != 1) {
                            printf("Ambiguity found with offset %d file_len %d count %d\n", Pinit->offset, Pinit->file_len, Pinit->count);
                            abort();
                        }
                    }
                }
                ::(offset + count < file_len) -> {
                    c_code {
                        int key = Pinit->offset + Pinit->file_len + Pinit->count;
                        struct DataItem *data = search(key);
                        if(data == NULL) {
                            insert(key, 2);
                        }
                        else if(data->data != 2) {
                            printf("Ambiguity found with offset %d file_len %d count %d\n", Pinit->offset, Pinit->file_len, Pinit->count);
                            abort();
                        }
                    }
                }
                ::(offset + count >= file_len) -> {
                    c_code {
                        int key = Pinit->offset + Pinit->file_len + Pinit->count;
                        struct DataItem *data = search(key);
                        if(data == NULL) {
                            insert(key, 3);
                        }
                        else if(data->data != 3) {
                            printf("Ambiguity found with offset %d file_len %d count %d\n", Pinit->offset, Pinit->file_len, Pinit->count);
                            abort();
                        }
                    }
                }
            fi
            counter = counter + 1
        }
        ::else
    od
}