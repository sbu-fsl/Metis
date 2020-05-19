int state;
int queue;

c_code {
\#include <math.h>
int state2;
};

inline select_flag(flag) {
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

inline enqueue(value, mask) {
    queue = queue << 3;
    queue = queue | value;
    queue = queue & mask;
}

active [1] proctype worker() {
    int mask;
    do ::
        state = 0;
        queue = 0;
        mask = 0;
        select_flag(state);
        /* Determine how many active bits in state */
        /* 1 active bit in flag: mask = (111)_2, open 1 digit in queue;
           2 active bits in flag: mask = (111 111)_2, open 2 digits in queue;
           3 active bits in flag: mask = (111 111 111)_2, open 3 oct digits in queue;
        */
        c_code {
            state2 = now.state;
            while (state2 > 0) {
                if (state2 & 0x7 > 0) {
                    Pworker->mask <<= 3;
                    Pworker->mask |= 0x7;
                }
                state2 >>= 3;
            }
            printf("mask = %03o\n", Pworker->mask);
        };
            
        do
            :: (state & 1) > 0 -> atomic {
                enqueue(1, mask);
                printf("[%d] 1, flag=%o, queue=%o\n", _pid, state, queue);
            };
            :: (state & 8) > 0 -> atomic {
                enqueue(2, mask);
                printf("[%d] 2, flag=%o, queue=%o\n", _pid, state, queue);
            };
            :: (state & 64) > 0 -> atomic {
                enqueue(3, mask);
                printf("[%d] 3, flag=%o, queue=%o\n", _pid, state, queue);
            };
            :: else -> skip; /* skip == 0? */
        od
    od
}
