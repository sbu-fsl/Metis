#include "abstract_fs.h"

#include <algorithm>

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

static int walk(const char *path, AbstractFs *fs)
{
  AbstractFile file;
	struct stat fileinfo;
	int ret = 0;
	// Avoid '.' or '..'
	if (is_this_or_parent(path)) {
		return 0;
	}

	file.fullpath = path;

	// Stat the current file and add it to vector
	ret = stat(path, &fileinfo);
	if (ret != 0) {
		printf("Walk error: cannot stat '%s' (%d)\n", path, errno);
		return -1;
	}
	file.attrs.mode = fileinfo.st_mode;
	file.attrs.size = fileinfo.st_size;
	file.attrs.nlink = fileinfo.st_nlink;
	file.attrs.uid = fileinfo.st_uid;
	file.attrs.gid = fileinfo.st_gid;
	// Hash the content if it's a regular file
	if (S_ISREG(file.attrs.mode)) {
		file.datahash = hash_file_content(path);
		if (file.datahash == (uint64_t) -1) {
			printf("Walk: unable to hash '%s'\n", path);
		}
	} else {
		file.datahash = 0;
	}
	// Add current file to vector
	// printf("Adding %s to vector.\n", pathbuf);
  fs->list.push_back(file);
	// If this is a directory, recursively walk its children
	if (S_ISDIR(file.attrs.mode)) {
		DIR *dir = opendir(path);
		if (!dir) {
			printf("Walk: unable to opendir '%s'. (%d)\n",
			       path, errno);
			return -1;
		}
		struct dirent *child;
		while ((child = readdir(dir)) != NULL) {
			if (is_this_or_parent(child->d_name)) {
				continue;
			}
      fs::path childpath = file.fullpath / child->d_name;
			ret = walk(childpath.c_str(), fs);
			if (ret < 0) {
				printf("Error when walking '%s'.\n", childpath.c_str());
				closedir(dir);
				return -1;
			}
		}
		closedir(dir);
	}
	return 0;
}

void init_abstract_fs(absfs_t *absfs) {
  *absfs = (absfs_t) new AbstractFs();
}

bool cmp_abstract_files(const AbstractFile &a, const AbstractFile &b)
{
  return a.fullpath < b.fullpath;
}

int scan_abstract_fs(absfs_t absfs, const char *basepath)
{
  AbstractFs *fs = (AbstractFs *)absfs;
	int ret = walk(basepath, fs);
  std::sort(fs->list.begin(), fs->list.end(), cmp_abstract_files);
	return ret;
}

uint64_t get_abstract_fs_hash(absfs_t absfs)
{
  AbstractFs *fs = (AbstractFs *)absfs;
	MD5_CTX md5ctx;
	struct md5sum result;
	MD5_Init(&md5ctx);

  for (auto it = fs->list.begin(); it != fs->list.end(); ++it) {
		size_t pathlen = strnlen(it->fullpath.c_str(), PATH_MAX);
		MD5_Update(&md5ctx, it->fullpath.c_str(), pathlen);
		MD5_Update(&md5ctx, &it->attrs, sizeof(it->attrs));
		MD5_Update(&md5ctx, &it->datahash, sizeof(uint64_t));
  }
	MD5_Final((unsigned char *)&result, &md5ctx);
	return result.a;
}

void destroy_abstract_fs(absfs_t absfs)
{
  AbstractFs *fs = (AbstractFs *)absfs;
  delete fs;
}

void print_abstract_fs(absfs_t absfs)
{
  AbstractFs *fs = (AbstractFs *)absfs;
  for (auto it = fs->list.begin(); it != fs->list.end(); ++it) {
		printf("%s, mode=%06o, size=%zu, nlink=%ld, uid=%d, gid=%d\n",
		       it->fullpath.c_str(), it->attrs.mode, it->attrs.size,
		       it->attrs.nlink, it->attrs.uid, it->attrs.gid);
  }
}

#ifdef ABSFS_TEST

int main(int argc, char **argv)
{
	absfs_t absfs;
	char *basepath;
	int ret;

	if (argc > 1) {
		basepath = argv[1];
	} else {
		basepath = getenv("HOME");
	}

  init_abstract_fs(&absfs);

	printf("Iterating directory '%s'...\n", basepath);

	ret = scan_abstract_fs(absfs, basepath);

	if (ret) {
		printf("Error occurred when iterating...\n");
	} else {
		printf("Iteration complete. Abstract FS signature = %#lx\n",
		       get_abstract_fs_hash(absfs));
	}

  print_abstract_fs(absfs);

	return ret;
}

#endif
