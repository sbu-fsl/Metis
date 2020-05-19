int flag;

inline assign_flags(flag) {
    if
        :: flag = flag | 4096;  /* oct: 010000 */
        :: skip;
    fi
    if
        :: flag = flag | 512;   /* oct: 001000 */  
        :: skip;
    fi
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
    flag = 0;
    assign_flags(flag);
    printf("[%d] %o\n", _pid, flag);
}
