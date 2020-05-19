int state;

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

active [1] proctype worker() {
    do ::
        state = 0;
        select_flag(state);
        if
            :: (state & 1) > 0 ->
                printf("[%d] 1, state=%o\n", _pid, state);
            :: else -> skip;
        fi
        if
            :: (state & 8) > 0 ->
                printf("[%d] 2, state=%o\n", _pid, state);
            :: else -> skip;
        fi
        if
            :: (state & 64) > 0 ->
                printf("[%d] 3, state=%o\n", _pid, state);
            :: else -> skip;
        fi
    od
}
