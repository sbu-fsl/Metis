#include "abstract_fs.h"

#include <algorithm>

#include <dirent.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <fcntl.h>
#include <unistd.h>

struct md5sum {
  uint64_t a;
  uint64_t b;
};

static inline bool is_this_or_parent(const char *name) {
  return (strncmp(name, ".", NAME_MAX) == 0) ||
         (strncmp(name, "..", NAME_MAX) == 0);
}

/**
 * hash_file_content: Feed the file content into MD5 calculator and update
 *   an existing MD5 context object.
 *
 * @param[in] fullpath: Full absolute path to the file being hashed
 * @param[in] md5ctx: Pointer to an initialized MD5_CTX object
 *
 * @return: 0 for success, +1 for MD5_Update failure,
 *          negative number for error status of open() or read()
 */
static int hash_file_content(const char *fullpath, MD5_CTX *md5ctx) {
  int fd = open(fullpath, O_RDONLY);
  char buffer[4096] = {0};
  ssize_t readsize;
  int ret = 0;
  if (fd < 0) {
    fprintf(stderr, "hash error: cannot open '%s' (%d)\n", fullpath, errno);
    ret = -errno;
    goto end;
  }

  while ((readsize = read(fd, buffer, 4096)) > 0) {
    ret = MD5_Update(md5ctx, buffer, readsize);
    memset(buffer, 0, sizeof(buffer));
    /* MD5_Update returns 0 for failure and 1 for success.
     * However, we want 0 for success and other values for error.
     */
    if (ret == 0) {
      /* This is special: If returned value is +1, then it indicates
       * MD5_Update error. Minus number for error in open() and read() */
      ret = 1;
      fprintf(stderr, "MD5_Update failed on file '%s'\n", fullpath);
      goto end;
    } else {
      ret = 0;
    }
  }
  if (readsize < 0) {
    fprintf(stderr, "hash error: read error on '%s' (%d)\n", fullpath, errno);
    ret = -errno;
  }

end:
  close(fd);
  return ret;
}

static int walk(const char *path, const char *abstract_path, absfs_t *fs) {
  AbstractFile file;
  struct stat fileinfo = {0};
  std::vector<std::string> children;
  int ret = 0;
  // Avoid '.' or '..'
  if (is_this_or_parent(path)) {
    return 0;
  }

  file.fullpath = path;
  file.abstract_path = abstract_path;

  /* Stat the current file.
   * Use lstat() because we want to see symbol links as concrete files */
  ret = lstat(path, &fileinfo);
  if (ret != 0) {
    fprintf(stderr, "Walk error: cannot stat '%s' (%d)\n", path, errno);
    return -1;
  }
  memset(&file.attrs, 0, sizeof(file.attrs));
  /* Assemble attributes of our interest */
  file.attrs.mode = fileinfo.st_mode;
  file.attrs.size = fileinfo.st_size;
  file.attrs.nlink = fileinfo.st_nlink;
  file.attrs.uid = fileinfo.st_uid;
  file.attrs.gid = fileinfo.st_gid;

  /* Update the MD5 signature of the abstract file system state */
  file.FeedHasher(&fs->ctx);

  /* If the current file is a directory, read its entries and sort
   * Sorting makes sure that the order of files and directories
   * retrieved is deterministic.*/
  if (S_ISDIR(file.attrs.mode)) {
    DIR *dir = opendir(path);
    if (!dir) {
      fprintf(stderr, "Walk: unable to opendir '%s'. (%d)\n", path, errno);
      return -1;
    }
    struct dirent *child;
    while ((child = readdir(dir)) != NULL) {
      if (is_this_or_parent(child->d_name))
        continue;
      children.push_back(child->d_name);
    }
    closedir(dir);
    std::sort(children.begin(), children.end());
  }

  /* Walk childrens if there is any */
  for (std::string filename : children) {
    fs::path childpath = file.fullpath / filename;
    fs::path child_abstract_path = file.abstract_path / filename;
    ret = walk(childpath.c_str(), child_abstract_path.c_str(), fs);
    if (ret < 0) {
      fprintf(stderr, "Error when walking '%s'.\n", childpath.c_str());
      return -1;
    }
  }
  return 0;
}

/**
 * init_abstract_fs: Initialize the abstract file system state
 *
 * @param[in]: Pointer to an absfs_t object.
 */
void init_abstract_fs(absfs_t *absfs) {
  MD5_Init(&absfs->ctx);
  memset(absfs->state, 0, sizeof(absfs->state));
}

bool cmp_abstract_files(const AbstractFile &a, const AbstractFile &b) {
  return a.abstract_path < b.abstract_path;
}

int scan_abstract_fs(absfs_t absfs, const char *basepath) {
  AbstractFs *fs = (AbstractFs *)absfs;
  int ret = walk(basepath, "/", fs);
  std::sort(fs->list.begin(), fs->list.end(), cmp_abstract_files);
  return ret;
}

uint64_t get_abstract_fs_hash(absfs_t absfs) {
  AbstractFs *fs = (AbstractFs *)absfs;
  MD5_CTX md5ctx;
  struct md5sum result = {0};
  MD5_Init(&md5ctx);

  for (auto it = fs->list.begin(); it != fs->list.end(); ++it) {
    size_t pathlen = strnlen(it->abstract_path.c_str(), PATH_MAX);
    MD5_Update(&md5ctx, it->abstract_path.c_str(), pathlen);
    MD5_Update(&md5ctx, &it->attrs, sizeof(it->attrs));
    MD5_Update(&md5ctx, &it->datahash, sizeof(uint64_t));
  }
  MD5_Final((unsigned char *)&result, &md5ctx);
  return result.a;
}

void destroy_abstract_fs(absfs_t absfs) {
  AbstractFs *fs = (AbstractFs *)absfs;
  delete fs;
}

void print_abstract_fs(absfs_t absfs) {
  AbstractFs *fs = (AbstractFs *)absfs;
  for (auto it = fs->list.begin(); it != fs->list.end(); ++it) {
    printf("%s, mode=%06o, size=%zu, nlink=%ld, uid=%d, gid=%d, datahash=%lx\n",
           it->abstract_path.c_str(), it->attrs.mode, it->attrs.size,
           it->attrs.nlink, it->attrs.uid, it->attrs.gid, it->datahash);
  }
}

#ifdef ABSFS_TEST

int main(int argc, char **argv) {
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
