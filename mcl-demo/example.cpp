#include <cstdio>
#include <cstring>
#include <cstdint>
#include <deque>
#include <string>
#include <experimental/filesystem>
#include <map>
#include <vector>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mount.h>
#include <sys/mman.h>
#include <openssl/md5.h>
#include "mcl.h"

#define nelem(arr)  (sizeof(arr) / sizeof(arr[0]))

struct md5rep {
    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;
};

namespace fs = std::experimental::filesystem;

static fs::path filenames[] = {
  "/test0", "/test1", "/test2"
};

static std::string fsops[] = {
  "open", "write", "read", "close", "unlink"
};

static const std::string fsimg_path = "/dev/ram0";
static const size_t fsimg_size = 1048576;

static int open_rw_options[] = {
  O_RDONLY, O_WRONLY, O_RDWR
};

static int open_opt_options[] = {
  0, O_CREAT
};

static char *buffer[4096];

class AbstractFs {
  public:
    enum class Type { UNKNOWN, REGULAR, DIRECTORY };
    std::map<std::string, AbstractFs *> children;
    std::string name;
    Type type;
    size_t size;

    AbstractFs() {
      name = "/";
      type = Type::DIRECTORY;
      size = 0;
    }
    AbstractFs(std::string &name) : name(name) {
      size = 0;
      type = Type::DIRECTORY;
    }
    AbstractFs(std::string &name, Type type, size_t size) : 
      name(name), type(type), size(size) {}

    virtual ~AbstractFs() {
      for (auto child : children) {
        recursive_free(child.second);
      }
    }

    void add_child(std::string name, Type type, size_t size = 0) {
      if (name[0] != '/') {
        name = '/' + name;
      }
      children.insert({name, new AbstractFs(name, type, size)});
    }

    AbstractFs *get_child(std::string &name) const {
      if (children.find(name) == children.end()) {
        return nullptr;
      }
      return children.find(name)->second;
    }

    bool remove_child(const std::string &name) {
      auto res = children.find(name);
      if (res == children.end()) {
        return false;
      }
      recursive_free(res->second);
      children.erase(name);
    }

    bool update_child(const std::string &name, Type type, size_t size) {
      auto res = children.find(name);
      if (res == children.end()) {
        return false;
      }
      res->second->type = type;
      res->second->size = size;
    }

    size_t hash_tree() const {
      std::hash<std::string> H;
      size_t res = H(name);
      res ^= size;
      res ^= (int)type;
      if (children.size() > 0) {
        for (auto ch : children) {
          res ^= (ch.second->hash_tree() << 1);
        }
      }
      return res;
    }
  private:
    void recursive_free(AbstractFs *ptr) {
      if (ptr->children.size() > 0) {
        for (auto ch : ptr->children) {
          recursive_free(ch.second);
        }
        ptr->children.clear();
      }
      delete ptr;
    }
};

template<> struct std::hash<AbstractFs> {
  std::size_t operator()(AbstractFs const& val) const noexcept
  {
    return val.hash_tree();
  }
};

class FsTest : public TestHarness {
  public:
    int ntrans;
    int fd;
    fs::path basepath;
    void *fsimg;
    int imgfd;
    std::deque<int> fds;
    AbstractFs absfs;

    FsTest() {
      ntrans = 0;
      basepath = "/mnt/test-ext4";
      fd = -1;
      fsimg = nullptr;
    }

    ~FsTest() {
    }
    
    virtual void init(void) {
      printf("Init!\n");
      imgfd = open(fsimg_path.c_str(), O_CREAT | O_TRUNC | O_RDWR);
      if (imgfd < 0) {
          perror(fsimg_path.c_str());
          error("init error", "Cannot create image file.");
      }
          
      /* mmap to fsimg pointer */
      fsimg = mmap(nullptr, fsimg_size, PROT_READ | PROT_WRITE, MAP_SHARED, imgfd, 0);
      if (fsimg == MAP_FAILED) {
          perror("mmap");
          error("init error", "Cannot mmap");
      }
      /* Initialize file system */
      init_state();
    }

    void exit() {
        munmap(fsimg, fsimg_size);
        close(imgfd);
    }

    virtual void init_state(void) {
        // printf("Init state!\n");
        /* Format a clean ext4 file system */
        memset(fsimg, 0, fsimg_size);
        std::string cmd = "mkfs.ext4 -F -O ^has_journal -q " + fsimg_path;
        FILE *cmdfd = popen(cmd.c_str(), "r");
        int ret = pclose(cmdfd);
        if (ret != 0) {
            error("init-state error", "Cannot format ext4 file system.");
        }
    }

    void run_one_transition(void) {
      int op = xe_random(nelem(fsops));
      int openflags, a, b, c, ret;
      fs::path fn;
      printf("selected fsops: %s, ", fsops[op].c_str());
      errno = 0;
      switch(op) {
        case 0:
          a = xe_random(nelem(open_rw_options));
          b = xe_random(nelem(open_opt_options));
          c = xe_random(nelem(filenames));
          openflags = open_rw_options[a] | open_opt_options[b];
          fn = basepath / filenames[c];
          fd = open(fn.c_str(), openflags, 0644);
          if (fd >= 0) {
            fds.push_back(fd);
            absfs.add_child(std::string(fn.c_str()), AbstractFs::Type::REGULAR, 0);
          }
          printf("path = %s, flags = %#x, fd = %d, errno = %d\n", fn.c_str(), openflags, fd, errno);
          break;

        case 1:
          a = 1011 * xe_random(4);
          memset(buffer, 0, a);
          ret = write(fd, buffer, a);
          printf("fd = %d, size = %d, ret = %d, errno = %d\n", fd, a, ret, errno);
          break;

        case 2:
          a = 1011 * xe_random(4);
          ret = read(fd, buffer, a);
          printf("fd = %d, size = %d, ret = %d, errno = %d\n", fd, a, ret, errno);
          break;

        case 3:
          ret = close(fd);
          printf("fd = %d, ret = %d, errno = %d\n", fd, ret, errno);
          break;

        case 4:
          a = xe_random(nelem(filenames));
          fn = basepath / filenames[a];
          ret = unlink(fn.c_str());
          if (ret == 0) {
            absfs.remove_child(fn);
          }
          printf("path = %s, ret = %d, errno = %d\n", fn.c_str(), ret, errno);
          break;
      }
    }

    signature_t get_sig(void) {
        /*
         * // The following code computes MD5 hash of the file system
         * // image. However, this doesn't work out well in practice
         * // because the f/s image contains lots of timestamps which
         * // changes on every format, mount and modification. That will
         * // cause non-converging state space.
         *
         * struct md5rep md5hash = {0};
         * unsigned char *data = (unsigned char *)fsimg;
         * // Clear irrelevant timestamp 
         * uint32_t *s_wtime = (uint32_t *)(data + 0x30);
         * *s_wtime = 0;
         * // Hash 
         * MD5(data, fsimg_size, (unsigned char *)&md5hash);
         * printf("State signature: %#x\n", md5hash.a);
         * return md5hash.a;
         */
        return absfs.hash_tree();
    }

    int should_checkpoint(void) {
        return 0;
    }

    int checkpoint_length(void) {
        return fsimg_size;
    }

    void checkpoint(char *ckpt, int len) {
        memcpy(ckpt, fsimg, len);
    }

    void before_new_transition(void) {
        /* Mount the file system */
        // printf("Pre-new-transtion hook: mount\n");
        const char *mntopt = "";
        int ret = mount(fsimg_path.c_str(), basepath.c_str(), "ext4", MS_SYNCHRONOUS | MS_NOATIME, mntopt);
        if (ret != 0) {
            perror(basepath.c_str());
            error("init-state error", "Unable to mount the file system");
        }
    }

    void after_new_transition(void) {
        // printf("Post-new-transtion hook: unmount\n");
        for (int _fd : fds) {
          close(_fd);
        }
        fds.clear();
        do {
            errno = 0;
            usleep(10 * 1000);
            umount2(basepath.c_str(), MNT_FORCE);
        } while (errno == EBUSY);
    }

};

int main(int argc, char **argv) {
  xe_process_cmd_args(argc, argv);
  xe_check(new FsTest);
}
