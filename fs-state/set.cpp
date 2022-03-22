#include "set.h"
#include "config.h"
#include "init_globals.h"
#include <unordered_set>

static size_t *absfs_len;

struct AbsfsData {
  char* data = new char[sizeof(absfs_state_t) * get_n_fs()];

  AbsfsData() {
    memset(data, 0, *absfs_len);
  }

  AbsfsData(absfs_state_t* values) {
    char *ptr = data;
    for (size_t i = 0; i < get_n_fs(); ++i) {
      memcpy(ptr, values[i], sizeof(absfs_state_t));
      ptr += sizeof(absfs_state_t);
    }
  }

  size_t hash() const {
    // FNV-1a hash: https://en.wikipedia.org/wiki/Fowler–Noll–Vo_hash_function
    const size_t fnv_prime = 0x00000100000001B3;
    const size_t fnv_offset = 0xcbf29ce484222325;
    size_t hashval = fnv_offset;
    for (size_t i = 0; i < *absfs_len; ++i) {
      hashval = hashval ^ data[i];
      hashval = hashval * fnv_prime;
    }
    return hashval;
  }
};

static bool operator==(const AbsfsData &a, const AbsfsData &b) {
  return memcmp(a.data, b.data, *absfs_len) == 0;
}

struct AbsfsStateHasher {
  size_t operator()(AbsfsData const& val) const noexcept {
    return val.hash();
  }
};

struct AbsfsSet {
  std::unordered_set<AbsfsData, AbsfsStateHasher> s;
};

void absfs_set_init(absfs_set_t *set) {
  AbsfsSet *new_set = new AbsfsSet();
  *set = new_set;
}

void absfs_set_destroy(absfs_set_t set) {
  delete set;
}

int absfs_set_add(absfs_set_t set, absfs_state_t* states) {
  auto res = set->s.insert(states);
  return res.second;
}

size_t absfs_set_size(absfs_set_t set) {
  return set->s.size();
}

extern "C" void __attribute__((constructor)) set_init()
{
  absfs_len = (size_t*)calloc(1, sizeof(size_t));
  if (!absfs_len) {
    fprintf(stderr, "memory allocation failed: %s:%d:%s\n", 
            __FILE__, __LINE__, __func__);
    exit(EXIT_FAILURE);
  }
  *absfs_len = get_n_fs() * sizeof(absfs_state_t);
}

extern "C" void __attribute__((destructor)) set_cleanup()
{
  free(absfs_len);
}
