c_decl {
    typedef char name_t[10];
};

c_state "name_t prev" "Global";
c_state "name_t name" "Global";

active [1] proctype worker() {
    do
        :: // d_step {
            c_code {
                strncpy(now.prev, now.name, 10);
                memset(now.name, 0, 10);
                sprintf(now.name, "first");
                printf("[%d] %s\n", Pworker->_pid, now.name);
            };
        //};

        :: //d_step {
            c_code {
                strncpy(now.prev, now.name, 10);
                memset(now.name, 0, 10);
                sprintf(now.name, "second");
                printf("[%d] %s\n", Pworker->_pid, now.name);
            };
        //};

        :: //d_step {
            c_code {
                strncpy(now.prev, now.name, 10);
                memset(now.name, 0, 10);
                sprintf(now.name, "third");
                printf("[%d] %s\n", Pworker->_pid, now.name);
            };
        //};
    od
}
