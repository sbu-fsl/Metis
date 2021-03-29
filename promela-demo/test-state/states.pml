int flag;

inline assign_flags(flag) {
    if
        :: flag = flag | 64;    /* oct: 000100 */   
        :: skip;
    fi
    if
        :: flag = flag | 8;     /* oct: 000010 */
        :: skip;
    fi
    if
        :: flag = flag | 1;     /* oct: 000001 */
        :: skip;
    fi
}

active [1] proctype worker() {
    do
        :: flag = 0;
           assign_flags(flag);
           c_code { printf("%03o\n", now.flag); };
    od
}

