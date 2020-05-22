/*
Demo program to show how to abstract states in Spin.
Variables tracked using c_track "Matched" are used for state matching.
*/
c_decl {
	#include "abstraction_eg.c"
}

c_track "&test1_created" "sizeof(int)" "Matched"
c_track "&test1_deleted" "sizeof(short)" "Matched"

proctype worker()
{
	do
		:: atomic {
			c_code {
				printf("Entering with state: test1_created %d , test1_deleted %d\n", test1_created, test1_deleted);
			}
			if
				::
					c_code {
						printf("Create called\n");
						test1_created += 1;
					}
				::
					c_code {
						printf("Delete called\n");
						test1_deleted += 1;
					}
			fi;
			c_code {
				doAbstraction();
				printf("Exiting with state: test1_created %d , test1_deleted %d\n", test1_created, test1_deleted);
			}
		}
    od;
}

init {
	c_code {
		test1_deleted = 0;
		test1_created = 0;
	}
	run worker();
}
