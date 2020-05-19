int state;

inline enqueue_id(num) {
    /* left shift for one unit of 4-bits to make space to record current ID */
    /* Works like a queue */
    state = state << 4;
    /* record current ID (let's assume 0 <= num <= 15) */
    state = state | num;;
    /* state &= 0xfff - only open the last 2 4-bits and mask out the rest */
    state = state & 255;
}

active [1] proctype worker() {
    do
    :: atomic {
        enqueue_id(1);
        printf("[%d] 1, state=%x\n", _pid, state);
    };
    :: atomic {
        enqueue_id(2);
        printf("[%d] 2, state=%x\n", _pid, state);
    };
    od
}
