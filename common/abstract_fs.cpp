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
#include <ftw.h>

#include <gperftools/profiler.h>
#include "errnoname.h"
#include "path_utils.h"

struct md5sum {
  uint64_t a;
  uint64_t b;
};

struct exclude_path {
  std::string parent;
  std::string name;
};

static const struct exclude_path exclusion_list[] = {
  {"/", "lost+found"},
  {"/", ".nilfs"},
  {"/", ".mcfs_dummy"}
};

static inline bool is_excluded(const std::string &parent,
                               const std::string &name) {
  int N = sizeof(exclusion_list) / sizeof(struct exclude_path);
  for (int i = 0; i < N; ++i) {
    if (exclusion_list[i].parent == parent && exclusion_list[i].name == name) {
      return true;
    }
  }
  return false;
}

static inline bool is_this_or_parent(const char *name) {
  return (strncmp(name, ".", NAME_MAX) == 0) ||
         (strncmp(name, "..", NAME_MAX) == 0);
}

/**
 * hash_file_content: Feed the file content into MD5 calculator and update
 *   an existing MD5 context object.
 *
 * @param[in] file:   The file being hashed
 * @param[in] md5ctx: Pointer to an initialized MD5_CTX object
 *
 * @return: 0 for success, +1 for MD5_Update failure,
 *          negative number for error status of open() or read()
 */
static int hash_file_content(AbstractFile *file, MD5_CTX *md5ctx) {
  const char *fullpath = file->fullpath.c_str();
  int fd = file->Open(O_RDONLY);
  char buffer[4096] = {0};
  ssize_t readsize;
  int ret = 0;
  if (fd < 0) {
    file->printer("hash error: cannot open '%s' (%d)\n", fullpath, errno);
    ret = -errno;
    goto end;
  }

  while ((readsize = file->Read(fd, buffer, 4096)) > 0) {
    ret = MD5_Update(md5ctx, buffer, readsize);
    memset(buffer, 0, sizeof(buffer));
    /* MD5_Update returns 0 for failure and 1 for success.
     * However, we want 0 for success and other values for error.
     */
    if (ret == 0) {
      /* This is special: If returned value is +1, then it indicates
       * MD5_Update error. Minus number for error in open() and read() */
      ret = 1;
      file->printer("MD5_Update failed on file '%s'\n", fullpath);
      goto end;
    } else {
      ret = 0;
    }
  }
  if (readsize < 0) {
    file->printer("hash error: read error on '%s' (%d)\n", fullpath, errno);
    ret = -errno;
  }

end:
  close(fd);
  return ret;
}

static const char *walker_basepath;
static size_t basepath_len;
static std::vector<AbstractFile> walker_files;
static printer_t walker_printer;
static const char *get_abstract_path(const char *fullpath) {
  // tc_path_rebase(basepath, fullpath, pathbuf, PATH_MAX);
  const char *res = fullpath + basepath_len;
  if (*res == '\0')
    return "/";
  return res;
}

static int nftw_handler(const char *fpath, const struct stat *finfo,
    int typeflag, struct FTW *ftwbuf) {
  AbstractFile file;
  file.printer = walker_printer;
  file.fullpath = fpath;
  file.abstract_path = get_abstract_path(fpath);
  file.attrs.mode = finfo->st_mode;
  file.attrs.size = finfo->st_size;
  file.attrs.nlink = finfo->st_nlink;
  file.attrs.uid = finfo->st_uid;
  file.attrs.gid = finfo->st_gid;
  file._attrs.blksize = finfo->st_blksize;
  file._attrs.blocks = finfo->st_blocks;
  walker_files.push_back(file);
  return 0;
}

static int do_walk(const char *basepath, printer_t printer) {
  // Initialize
  walker_basepath = basepath;
  basepath_len = strnlen(basepath, PATH_MAX);
  walker_files.clear();
  walker_printer = printer;

  // walk the directory tree
  const int nopenfd = 50;
  int res = nftw(basepath, nftw_handler, nopenfd, FTW_PHYS);
  if (res < 0) {
    printer("nftw() error while walking %s. errno = %d(%s)\n", basepath,
        errno, errnoname(errno));
    return -errno;
  }

  return 0;
}

static int walk(const char *path, const char *abstract_path, absfs_t *fs,
                bool verbose, printer_t verbose_printer) {

  int res = do_walk(path, verbose_printer);

  if (res < 0) {
    verbose_printer("Error when walking directory %s: %d(%s)\n", path, errno,
        errnoname(errno));
    return res;
  }

  // sort the file list
  std::vector<AbstractFile> &files = walker_files;
  auto abspath_cmp = [](const AbstractFile &a, const AbstractFile &b) {
    return a.abstract_path < b.abstract_path;
  };
  std::sort(files.begin(), files.end(), abspath_cmp);

  // iterate the file list and compute the hash
  MD5_CTX md5ctx;
  MD5_Init(&md5ctx);
  for (AbstractFile &file : files) {
    if (verbose) {
      verbose_printer("%s, mode=", file.abstract_path.c_str());
      print_filemode(verbose_printer, file.attrs.mode);
      verbose_printer(", size=%zu", file.attrs.size);
      if (!S_ISREG(file.attrs.mode))
        verbose_printer(" (Ignored), ");
      else
        verbose_printer(", ");
      verbose_printer("nlink=%ld, uid=%d, gid=%d\n", file.attrs.nlink,
          file.attrs.uid, file.attrs.gid);
    }
    file.FeedHasher(&fs->ctx);
    // file.CheckValidity();
  }

  return 0;
}

void AbstractFile::FeedHasher(MD5_CTX *ctx) {
  const char *abspath = abstract_path.c_str();
  size_t pathlen = strnlen(abspath, PATH_MAX);

  /* We only take file sizes of regular files into consideration,
   * because different file systems may have different behavior in
   * reporting special files' sizes (especially directories), which
   * is normal but will cause false discrepancy.
   */
  size_t fsize = attrs.size;
  if (!S_ISREG(attrs.mode)) {
    attrs.size = 0;
    attrs.nlink = 0;
  }

  MD5_Update(ctx, abspath, pathlen);
  MD5_Update(ctx, &attrs, sizeof(attrs));

  if (S_ISREG(attrs.mode))
    hash_file_content(this, ctx);

  /* Assign value back after use */
  attrs.size = fsize;
}

/**
 * CheckValidity: check the validity of attrs
 *
 * NOTE: the criteria used in this function is specific to the parameter
 * spaces define in parameters.py. These could be outdated.
 */
bool AbstractFile::CheckValidity() {
  bool res = true;
  /* The file must be either a regular file or a directory */
  if (!(S_ISREG(attrs.mode) ^ S_ISDIR(attrs.mode))) {
    printer("File %s must be either a regular file or a directory.\n",
            fullpath.c_str());
    res = false;
  }
  /* The file size should not exceed 1M */
  if (attrs.size > 1048576) {
    printer("File %s has size of %zu, which is unlikely in our experiemnt.\n",
            fullpath.c_str());
    res = false;
  }
  /* nlink shouldn't be too large */
  if (attrs.nlink > 5) {
    printer("File %s has %d links, which is unlikely in our experiment.\n",
            fullpath.c_str());
    res = false;
  }
  /* File size should match number of blocks allocated */
  size_t rounded_fsize = round_up(attrs.size, _attrs.blksize);
  size_t allocated = (size_t)_attrs.blksize * _attrs.blocks;
  if (allocated - rounded_fsize > 4096) {
    printer("File %s has the size of %zu, but is allocated %zu bytes.\n",
            fullpath.c_str(), attrs.size, allocated);
    res = false;
  }
  return res;
}

void AbstractFile::retry_warning(std::string funcname, std::string cond,
                                 int retry_count) {
  std::string ordinal;
  switch (retry_count % 10) {
    case 1:
      ordinal = "st";
      break;

    case 2:
      ordinal = "nd";
      break;

    case 3:
      ordinal = "rd";
      break;

    default:
      ordinal = "th";
  }

  printer("Retrying %s for the %d%s time because %s\n", funcname.c_str(),
          retry_count, ordinal.c_str(), cond.c_str());
}

int AbstractFile::Open(int flag) {
  DEFINE_SYSCALL_WITH_RETRY(int, open, fullpath.c_str(), flag);
}

ssize_t AbstractFile::Read(int fd, void *buf, size_t count) {
  DEFINE_SYSCALL_WITH_RETRY(ssize_t, read, fd, buf, count);
}

int AbstractFile::Lstat(struct stat *statbuf) {
  DEFINE_SYSCALL_WITH_RETRY(int, lstat, fullpath.c_str(), statbuf);
}

DIR *AbstractFile::Opendir() {
  if (!S_ISDIR(attrs.mode)) {
    return nullptr;
  }
  DEFINE_SYSCALL_WITH_RETRY(DIR *, opendir, fullpath.c_str());
}

struct dirent *AbstractFile::Readdir(DIR *dirp) {
  DEFINE_SYSCALL_WITH_RETRY(struct dirent *, readdir, dirp);
}

int AbstractFile::Closedir(DIR *dirp) {
  DEFINE_SYSCALL_WITH_RETRY(int, closedir, dirp);
}

/**
 * init_abstract_fs: Initialize the abstract file system state
 *
 * @param[in]: Pointer to an absfs_t object.
 */
void init_abstract_fs(absfs_t *absfs) {
  ProfilerEnable();
  MD5_Init(&absfs->ctx);
  memset(absfs->state, 0, sizeof(absfs->state));
}

/**
 * scan_abstract_fs: Walk the directory tree starting from the given
 *   basepath, and calculate a MD5 hash as the "abstract file system
 *   state".
 *
 * @param[in] absfs: The abstract file system object
 * @param[in] basepath: The path to start traversing
 *
 * @return: 0 for success, and other values for errors.
 */
int scan_abstract_fs(absfs_t *absfs, const char *basepath, bool verbose,
                     printer_t verbose_printer) {
  int ret = walk(basepath, "/", absfs, verbose, verbose_printer);
  MD5_Final(absfs->state, &absfs->ctx);
  return ret;
}

/**
 * print_abstract_fs_state: Print the whole 128-bit abstract file
 *   system state signature
 *
 * @param[in] printer:  The function that we can use to print out the
 *                      characters. It must be in the form of
 *                        int printer_function(const char *fmt, ...);
 * @param[in] state:    The absfs_state_t value
 */
void print_abstract_fs_state(printer_t printer, absfs_state_t state) {
  for (int i = 0; i < 16; ++i)
    printer("%02x", state[i] & 0xff);
}

void print_filemode(printer_t printer, mode_t mode) {
  printer("<");

  /* file type */
  if (S_ISDIR(mode))
    printer("dir ");
  if (S_ISCHR(mode))
    printer("chrdev ");
  if (S_ISBLK(mode))
    printer("blkdev ");
  if (S_ISREG(mode))
    printer("file ");
  if (S_ISLNK(mode))
    printer("symlink ");
  if (S_ISSOCK(mode))
    printer("socket ");
  if (S_ISFIFO(mode))
    printer("fifo ");

  /* permission */
  if (mode & S_ISUID)
    printer("suid ");
  if (mode & S_ISGID)
    printer("sgid ");
  if (mode & S_ISVTX)
    printer("sticky ");
  printer("%03o>", mode & 0777);
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

  ret = scan_abstract_fs(&absfs, basepath, true, printf);

  if (ret) {
    printf("Error occurred when iterating...\n");
  } else {
    printf("Iteration complete. Abstract FS signature = ");
    print_abstract_fs_state(printf, absfs.state);
    printf("\n");
  }

  return ret;
}

#endif
