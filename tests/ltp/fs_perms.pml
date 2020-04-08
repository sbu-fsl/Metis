/*
 * Reference : https://github.com/linux-test-project/ltp/blob/master/testcases/kernel/fs/fs_perms/fs_perms.c
*/
c_code {
	#include "fs_perms.c"
	char *fperm, *file_name;
	gid_t fgroup_id, group_id;
	uid_t fuser_id, user_id;
	mode_t fmode;
	int exp_res;
	int res1, flag;
}

/* State variable to store the test result.*/
c_track "&res1" "sizeof(int)"

proctype fs_perms_test() {
	c_code{
		FILE *file;
		printf("Testing started...\n");

		// Set the group id.
		if (setgid(group_id))
			printf("Could not setgid to %d.\n", group_id);

		// Set uid.
		if (setuid(user_id))
			printf("Could not setuid to %d.\n", user_id);

		// Try to open the file with specified permission.
		if ((file = fopen(file_name, fperm)) != NULL) {
			fclose(file);
			res1 = 1;
		} else {
			printf("Couldn't open file: %s\n",strerror(errno));
			res1 = 0;
		}
		printf("Testing completed....\n");
		
	}
	/*Ensure that the test result is as expected.*/
	assert(c_expr{exp_res == res1});
}
proctype fs_perms_test_setup() {
	c_code {
		// Permission tested - fs_perms 200 99 99 99 99 w 1
		fmode = str_to_l("200", "file mode", 8);
		// user_id which owns the file.
		fuser_id = str_to_l("1000", "file uid", 10);
		// group_id for the file.
		fgroup_id = str_to_l("1000", "file gid", 10);
		// user_id to test for.
		user_id = str_to_l("1000", "tester uid", 10);
		// group_id to test for.
		group_id = str_to_l("1000", "tester gid", 10);
		// permission to test for.
		fperm = "w";
		// expected result.
		exp_res = str_to_l("1", "expected result", 10);

		file_name = TEST_FILE_NAME1;
		flag = 0;
		// Create the file with the given mode,uid and gid.
		testsetup(TEST_FILE_NAME1, 0, fmode, fuser_id, fgroup_id);
	}
	run fs_perms_test();
}

init {
	run fs_perms_test_setup();	
}

