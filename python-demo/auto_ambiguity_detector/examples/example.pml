hidden int true_entries;

init {
    int value;

    /* Choose a value */
    if
        :: value = -20;
        :: value = 20;
        :: value = 80;
        :: value = 160;
    fi

    if
        /* ambiguity: if value is negative then both entry 1 and 2 will be true */
        :: (value < 0) -> true_entries++; c_code { printf("value less than 0\n");};
        :: (value < 100) -> true_entries++; c_code { printf("value less than 100\n"); };
        :: (value >= 100) -> true_entries++; c_code { printf("value greater than 100\n"); };
        :: else -> skip;
    fi
}
