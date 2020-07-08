#include "malloc_hook.h"

int main(int argc, char *argv[])
{
    my_init_hook();
    int* ptr;
    char* str;
    int* arr[10];
    int n, i, arr_fail_flag;
    n = 8;
    arr_fail_flag = 0;
    //printf("Start malloc...\n");
    ptr = (int*)malloc(n * sizeof(int));
    str = (char *) malloc (1000);
    for (i = 0; i < 10; i++){
        arr[i] = malloc(sizeof(int));
        if (arr[i] == NULL){
            arr_fail_flag = 1;
        }
        else{
            *arr[i] = i * 20 + 5;
        }
    }
    //printf("HEADER_SIZE is %ld\n", HEADER_SIZE);
    if (ptr == NULL || str == NULL || arr_fail_flag == 1){
        printf("[hook_test]: Malloc allocation failed!\n");
        exit(EXIT_FAILURE);
    }
    else{
        printf("[hook_test]: Malloc allocation is successful!\n");
        for (i = 0; i < n; i++){
            ptr[i] = i * 10 + 1;
        }
        strcpy(str, "randomtext");
        printf("\n");
        for (i = 0; i < n; i++){
            printf("%d, ", ptr[i]);
        }
        printf("\n");
        printf("String is %s\n", str);
        print_block_list();
    }
    free(str);
    free(arr[3]);
    free(arr[4]);
    free(arr[5]);
    free(arr[7]);
    print_block_list();
    return 0;
}