/*
Demonstrates that d-step blocks are atomically executed without interleaving.
*/
#define N 16

byte a[N];
byte b[N];
byte c[N];
byte d[N];

c_code {
	struct timeval tv;
};

active[2] proctype worker() {

	do
		::d_step {	/* step 1 */
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 1;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
			byte i, tmp;
			i = 0;
			do
			:: i < N ->
				tmp = d[i];
				d[i] = c[i];
				c[i] = tmp; i++
			:: else ->
				printf("In pid %d: done with swap\n", _pid);
				break
			od;
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "end\0";
				int step = 1;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
		};

		::d_step {	/* step 2*/
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 2;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
			byte i, tmp;
			i = 0;
			do
			:: i < N ->
				tmp = d[i];
				d[i] = c[i];
				c[i] = tmp; i++
			:: else ->
				break
			od;
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "end\0";
				int step = 2;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
		};

		::d_step {	/* step 3 */
			printf("In process %d", _pid);
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 3;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
			byte i, tmp;
			i = 0;
			do
			:: i < N ->
				tmp = d[i];
				d[i] = c[i];
				c[i] = tmp; i++
			:: else ->
				break
			od;
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "end\0";
				int step = 3;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
		};
	od;
}
