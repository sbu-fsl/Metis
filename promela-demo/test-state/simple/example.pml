int i = 0;

active [2] proctype worker() {
    atomic {i = 1; printf("t%da\n", _pid + 1); };
    atomic {i = 2; printf("t%db\n", _pid + 1); };
    atomic {i = 3; printf("t%dc\n", _pid + 1); };
};
