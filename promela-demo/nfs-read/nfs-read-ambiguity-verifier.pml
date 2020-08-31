c_code {
    \#include "hashtable.h"
    \#include <time.h>
}

chan randr = [3] of {int, int, int};

inline addRecord() {
    c_code {
        int key = Pinit->offset + Pinit->file_len + Pinit->count;
        if(safeInsert(key, Pinit->offset, Pinit->count, Pinit->file_len, Pinit->type) == INSERT_FAIL) {
            printf("Ambiguity found with offset %d file_len %d count %d\n", Pinit->offset, Pinit->file_len, Pinit->count);
            // abort();
        }
    }
}

proctype getRand() {
    int offset, file_len, count;
    c_code {
        PgetRand->offset = randnum(1, 5);
    };
    c_code {
        PgetRand->file_len = randnum(1, 5);
    };
    c_code {
        PgetRand->count = randnum(1, 5);
    };
    randr ! offset, file_len, count;
}

init {
    // seet random seed
    c_code {
        srand(time(NULL));
    }
    int offset, file_len, count;
    int loops = 100;
    int counter = 0;
    int type;
    do
        ::(counter < loops) -> {
            run getRand();
            randr ? offset, file_len, count;
            if
                ::(offset >= file_len) -> {
                    type = 1;
                    addRecord();
                }
                ::(offset + count < file_len) -> {
                    type = 2;
                    addRecord();
                }
                ::(offset + count >= file_len) -> {
                    type = 3;
                    addRecord();
                }
            fi
            counter = counter + 1
        }
        ::else
    od
}