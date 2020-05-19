int state;

c_code {
    \#include "bitree.h"
    int state2;
    bool duplicate;
    int count;
};

inline schedule_c_code() {
    c_code {
        state2 = now.state;
        duplicate = search(state2);
        while (!duplicate && state2 > 0) {
            switch(state2 & 0x7) {
                case 1:
                    printf("1,");
                    break;
                case 2:
                    printf("2,");
                    break;
                case 3:
                    printf("3,");
                    break;
            }
            state2 >>= 3;
            printf("\n");
        };
        if (!duplicate) {
            insert_value(now.state);
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
        printf("[%d] 1, state=%o\n", _pid, state);
        schedule_c_code();
    };
    :: atomic {
        enqueue_id(2);
        printf("[%d] 2, state=%o\n", _pid, state);
        schedule_c_code();
    };
    :: atomic {
        enqueue_id(3);
        printf("[%d] 3, state=%o\n", _pid, state);
        schedule_c_code();
    };
    od
}
