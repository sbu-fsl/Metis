#include <unordered_map>
#include <cstdint>
#include <cerrno>
#include "cr.h"

std::unordered_map<uint64_t, void *> state_pool;

int insert_state(uint64_t key, void *ptr)
{
  auto it = state_pool.find(key);
  if (it != state_pool.end()) {
    return -EEXIST;
  }
  state_pool.insert({key, ptr});
  return 0;
}

void *find_state(uint64_t key)
{
  auto it = state_pool.find(key);
  if (it == state_pool.end()) {
    return nullptr;
  } else {
    return it->second;
  }
}

