#define MAX 1000000

active [4] proctype worker() {
    int a = 0;
    int b = 1;
    do
        :: (b < MAX) ->
            b = b + 1;
        :: (b >= MAX) ->
            b = 0;
            a = a + 1;
            printf("a = %d\n", a);
        :: (a >= 100) -> 
            break;
    od
}
