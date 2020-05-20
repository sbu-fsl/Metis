#include<stdio.h>
#include<stdlib.h>
#include<pthread.h>
int n=0;
void *count10(void * arg){
	int * nn = (int *)arg;
	int i=0;
	int temp;
	while(i<10){
		temp=(*nn)+1;
		(*nn)=temp;
		i=i+1;
	}
	printf("Thread exit\n");
}
int main(){
	pthread_t thread_id[2];
	pthread_create(&thread_id[0],NULL,count10,(void *)&n);
	pthread_create(&thread_id[1],NULL,count10,(void *)&n);
	
	pthread_join(thread_id[0],NULL);
	pthread_join(thread_id[1],NULL);
	printf("The count N is %d\n",n);
	
	return 0;
}
