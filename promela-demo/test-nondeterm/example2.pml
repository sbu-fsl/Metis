mtype:action = {send, reset};

proctype monitor(chan msg) {
    mtype:action act;
    int value = 0, val = 0;
    int true_entries = 0;
    int x;
    do ::
        msg?act,val,x;
        if
            :: (act == send) ->
                true_entries = true_entries + 1;
                value = val;
                c_code { printf("value = %d, true entries = %d\n", Pmonitor->value, Pmonitor->true_entries); };
                assert(true_entries == 1);
            :: (act == reset && value != val) ->
                value = val;
                true_entries = 0;
            :: else -> skip;
        fi
    od
}

init {
    int value;
    chan msg = [1] of {mtype:action, int, int};

    run monitor(msg);

    /* Choose a value */
    if
        :: value = -20;
        :: value = 20;
        :: value = 80;
        :: value = 160;
    fi

    msg!reset,value,0;

    if
        /* ambiguity: if value is negative then both entry 1 and 2 will be true */
        :: (value < 0) -> atomic {
            c_code { printf("value less than 0\n");};
            msg!send,value,1;
        }
        :: (value < 100) -> atomic {
            c_code { printf("value less than 100\n"); };
            msg!send,value,1;
        }
        :: (value >= 100) -> atomic {
            c_code { printf("value greater than 100\n"); };
            msg!send,value,1;
        } 
        :: else -> skip;
    fi
}
