/*
 * Copyright (c) 2020-2023 Yifei Liu
 * Copyright (c) 2020-2023 Gomathi Ganesan
 * Copyright (c) 2020-2023 Wei Su
 * Copyright (c) 2020-2023 Erez Zadok
 * Copyright (c) 2020-2023 Stony Brook University
 * Copyright (c) 2020-2023 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#define TEST_FILE_NAME1 "./test.file1"
#define TEST_FILE_NAME2 "./test.file2"
void testsetup(const char *file_name, int flag, mode_t mode,int user_id, int group_id);
long str_to_l(const char *str, const char *name, int base);

void testsetup(const char *file_name, int flag, mode_t mode,
		      int user_id, int group_id)
{
	FILE *file;
	file = fopen(file_name, "w");
	if (file == NULL)
		printf("Could not create test file %s.\n", file_name);

	if (fclose(file))
		printf( "Calling fclose failed.");

	if (chmod(file_name, mode))
		printf("Could not chmod test file %s.\n", file_name);

	if (chown(file_name, user_id, group_id))
		printf("Could not chown test file %s.\n", file_name);
	printf("Test setup done....\n");
}


long str_to_l(const char *str, const char *name, int base)
{
	char *end;
	long i = strtol(str, &end, base);
	if (*end != '\0')
		printf("Invalid parameter '%s' passed. (%s)", name, str);
	return i;
}
