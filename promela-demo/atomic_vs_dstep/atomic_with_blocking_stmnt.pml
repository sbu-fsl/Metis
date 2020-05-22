/* Demonstrates that atomic block can be interrupted if there are
blocking statements. 
*/
#define N 16

byte a[N];
byte b[N];
byte c[N];
byte d[N];

c_code {
	struct timeval tv;
};

int block_execution = 1;

active[2] proctype worker() {
	do
		::atomic {	/* step 1 */
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 1;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
			block_execution = 0;
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "end\0";
				int step = 1;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
		};

		::atomic {	/* step 2*/
			
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 2;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
			if
				:: _pid == 1 ->
					block_execution == 0;
				:: skip;
			fi;
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "end\0";
				int step = 2;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
		};

		::atomic {	/* step 3 */
			printf("In process %d", _pid);
			c_code {
				gettimeofday(&tv,NULL);
				useconds_t u64useconds = (1000000*tv.tv_sec) + tv.tv_usec;
				char action[] = "start\0";
				int step = 3;
				printf("%d\t%d\t%s\t%lu\n", Pworker->_pid, step, action, (unsigned long)u64useconds); 
			};
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
