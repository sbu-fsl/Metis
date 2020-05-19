int i = 0;

active [2] proctype worker() {
    do
        :: atomic { i = 1; printf("[%d] a, i = %d\n", _pid, i); };
        :: atomic { i = 2; printf("[%d] b, i = %d\n", _pid, i); };
        :: atomic { i = 3; printf("[%d] c, i = %d\n", _pid, i); };
    od
};
