#include "abstract_fs.h"
#include "path_utils.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <dirent.h>

#include <fcntl.h>
#include <unistd.h>

struct md5sum {
	uint64_t a;
	uint64_t b;
};

static inline bool is_this_or_parent(const char *path)
{
	return (strncmp(path, ".", PATH_MAX) == 0) || (strncmp(path, "..", PATH_MAX) == 0);
}

static uint64_t hash_file_content(const char *fullpath)
{
	int fd = open(fullpath, O_RDONLY);
	char buffer[4096];
	ssize_t readsize;
	struct md5sum result;
	MD5_CTX md5ctx;
	if (fd < 0) {
		printf("hash error: cannot open '%s' (%d)\n", fullpath, errno);
		return (uint64_t) -1;
	}

	MD5_Init(&md5ctx);
	while ((readsize = read(fd, buffer, 4096)) > 0) {
		MD5_Update(&md5ctx, buffer, readsize);
	}
	if (readsize < 0) {
		printf("hash error: read error on '%s' (%d)\n", fullpath, errno);
		close(fd);
		return (uint64_t) -1;
	}
	MD5_Final((unsigned char *)&result, &md5ctx);
	close(fd);
	return result.a;
}

static int walk(const char *path, vector_t *vec)
{
	char *pathbuf = malloc(PATH_MAX);
	struct absfs_file file;
	struct stat fileinfo;
	size_t pathlen;
	int ret = 0;
	// Avoid '.' or '..'
	if (is_this_or_parent(path)) {
		free(pathbuf);
		return 0;
	}
	strncpy(pathbuf, path, PATH_MAX);

	// Shrink pathbuf to its real length
	pathlen = strnlen(pathbuf, PATH_MAX) + 1;
	pathbuf[pathlen - 1] = 0;
	pathbuf = realloc(pathbuf, pathlen);
	file.fullpath = pathbuf;

	// Stat the current file and add it to vector
	ret = stat(pathbuf, &fileinfo);
	if (ret != 0) {
		printf("Walk error: cannot stat '%s' (%d)\n", pathbuf, errno);
		free(pathbuf);
		return -1;
	}
	file.attrs.mode = fileinfo.st_mode;
	file.attrs.size = fileinfo.st_size;
	file.attrs.nlink = fileinfo.st_nlink;
	file.attrs.uid = fileinfo.st_uid;
	file.attrs.gid = fileinfo.st_gid;
	// Hash the content if it's a regular file
	if (S_ISREG(file.attrs.mode)) {
		file.datahash = hash_file_content(pathbuf);
		if (file.datahash == (uint64_t) -1) {
			printf("Walk: unable to hash '%s'\n", pathbuf);
			// free(pathbuf);
			// return -1;
		}
	} else {
		file.datahash = 0;
	}
	// Add current file to vector
	// printf("Adding %s to vector.\n", pathbuf);
	vector_add(vec, &file);
	// If this is a directory, recursively walk its children
	if (S_ISDIR(file.attrs.mode)) {
		DIR *dir = opendir(pathbuf);
		if (!dir) {
			printf("Walk: unable to opendir '%s'. (%d)\n",
			       pathbuf, errno);
			free(pathbuf);
			return -1;
		}
		struct dirent *child;
		while ((child = readdir(dir)) != NULL) {
			if (is_this_or_parent(child->d_name)) {
				continue;
			}
			char *childpath = malloc(PATH_MAX);
			int newpath_len = tc_path_join(pathbuf, child->d_name,
				childpath, PATH_MAX) + 1;
			childpath[newpath_len - 1] = 0;
			childpath = realloc(childpath, newpath_len);
			ret = walk(childpath, vec);
			if (ret < 0) {
				printf("Error when walking '%s'.\n", childpath);
				free(childpath);
				closedir(dir);
				return -1;
			}
			free(childpath);
		}
		closedir(dir);
	}
	return 0;
}

static int abs_file_compare(const void *f1, const void *f2) {
	const struct absfs_file *file1 = f1;
	const struct absfs_file *file2 = f2;
	return strncmp(file1->fullpath, file2->fullpath, PATH_MAX);
}

int scan_abstract_fs(const char *basepath, vector_t *vec)
{
	int ret = walk(basepath, vec);
	vector_sort(vec, abs_file_compare);
	return ret;
}

uint64_t get_abstract_fs_hash(vector_t *absfs)
{
	MD5_CTX md5ctx;
	struct absfs_file *file;
	struct md5sum result;
	MD5_Init(&md5ctx);

	vector_iter(absfs, struct absfs_file, file) {
		size_t pathlen = strnlen(file->fullpath, PATH_MAX);
		MD5_Update(&md5ctx, file->fullpath, pathlen);
		MD5_Update(&md5ctx, &file->attrs, sizeof(file->attrs));
		MD5_Update(&md5ctx, &file->datahash, sizeof(uint64_t));
	}
	MD5_Final((unsigned char *)&result, &md5ctx);
	return result.a;
}

void destroy_abstract_fs(vector_t *absfs)
{
	struct absfs_file *file;
	vector_iter(absfs, struct absfs_file, file) {
		free(file->fullpath);
	}
	vector_destroy(absfs);
}

#ifdef ABSFS_TEST

int main(int argc, char **argv)
{
	vector_t absfs_vec;
	char *basepath;
	int ret;
	struct absfs_file *file;
	vector_init(&absfs_vec, struct absfs_file);

	if (argc > 1) {
		basepath = argv[1];
	} else {
		basepath = getenv("HOME");
	}

	printf("Iterating directory '%s'...\n", basepath);

	ret = scan_abstract_fs(basepath, &absfs_vec);

	vector_iter(&absfs_vec, struct absfs_file, file) {
		printf("%s, mode=%06o, size=%zu, nlink=%ld, uid=%d, gid=%d\n",
		       file->fullpath, file->attrs.mode, file->attrs.size,
		       file->attrs.nlink, file->attrs.uid, file->attrs.gid);
	}

	if (ret) {
		printf("Error occurred when iterating...\n");
	} else {
		printf("Iteration complete. Abstract FS signature = %#lx\n",
		       get_abstract_fs_hash(&absfs_vec));
	}

	return ret;
}

#endif
