chan randr = [1] of {int};

proctype rand() {
    int randnum = 0;
    do
        :: skip -> {randnum = randnum + 1}
        :: skip -> {randnum = randnum + 3}
        :: skip -> {randnum = randnum + 5}
        :: skip -> {randnum = randnum + 10}
        :: skip -> {randnum = randnum + 20}
        :: break
    od;
    randr ! randnum;
}

init {
    int max_loops = 20;
    int do_loops = 0;
    int offset;
    int file_len;
    int count;
    int if_tests = 0;
    int random_num_tests = 0;
    int result;
    do
        :: (random_num_tests < max_loops) -> {
            run rand();
            randr ? offset;
            run rand();
            randr ? file_len;
            run rand();
            randr ? count;
            if_tests = 0;
            result = -1;
            do
                :: (if_tests < max_loops) -> {
                    if
                        ::(offset >= file_len) -> {
                            if
                                :: (result != 1 && result != -1) -> {
                                    printf("An ambiguity found with offset %d file_len %d count %d.\n", offset, file_len, count);
                                    assert(false);
                                }
                                :: else -> {result = 1}
                            fi
                        }
                        ::(offset + count < file_len) -> {
                            if
                                :: (result != 2 && result != -1) -> {
                                    printf("An ambiguity found with offset %d file_len %d count %d.\n", offset, file_len, count);
                                    assert(false);
                                }
                                :: else -> {result = 2}
                            fi
                        }
                        ::(offset + count >= file_len) -> {
                            if
                                :: (result != 3 && result != -1) -> {
                                    printf("An ambiguity found with offset %d file_len %d count %d.\n", offset, file_len, count);
                                    assert(false);
                                }
                                :: else -> {result = 3}
                            fi
                        }
                    fi
                    if_tests = if_tests + 1;
                }
                :: else -> {break}
            od
            random_num_tests = random_num_tests + 1;
        }
        :: else -> {break}
    od
    printf("Nothing found. More loops needed.\n");
}