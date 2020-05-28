int state;
int flag;

c_code {
    \#include "bitree.h"
    int state2;
    int key;
    bool duplicate;
    int count;
    int openflags;
};

inline select_flag(flag) {
    flag = 0;
    if
        :: flag = flag | 1;
        :: skip;
    fi
    if
        :: flag = flag | 8;
        :: skip;
    fi
    if
        :: flag = flag | 64;
        :: skip;
    fi
}

inline schedule_c_code() {
    if
        :: flag == 0 -> select_flag(flag);
        :: else -> skip;
    fi
    c_code {
        state2 = now.state;
        if (seq_contains(state2, 2)) {
            key = state2 | ((now.flag) << 9);
        } else {
            key = state2;
        }
        duplicate = search(key);
        if (!duplicate) {
            printf("Proc=[%d], count=%d, sequence=%o, flag=%03o\n",
                Pworker->_pid, count, state2, now.flag);
        }
        while (!duplicate && state2 > 0) {
            switch(state2 & 0x7) {
                case 1:
                    printf("Operation 1,");
                    break;
                case 2:
                    openflags = now.flag;
                    now.flag = 0;
                    printf("Operation 2, flag = %03o", openflags);
                    break;
                case 3:
                    printf("Operation 3,");
                    break;
            }
            state2 >>= 3;
            printf("\n");
        };
        if (!duplicate) {
            insert_value(key);
            count++;
            printf("Count = %d\n", count);
        }
    }
}

inline enqueue_id(num) {
    /* left shift for one unit of 3-bits to make space to record current ID */
    /* Works like a queue */
    state = state << 3;
    /* record current ID (let's assume 0 <= num <= 7) */
    state = state | num;;
    /* state &= 0777 - only open the last 3 3-bits and mask out the rest */
    state = state & 511;
}

active [1] proctype worker() {
    do
    :: atomic {
        enqueue_id(1);
        schedule_c_code();
    };
    :: atomic {
        enqueue_id(2);
        schedule_c_code();
    };
    :: atomic {
        enqueue_id(3);
        schedule_c_code();
    };
    od
}
