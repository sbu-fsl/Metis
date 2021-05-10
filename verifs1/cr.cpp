#include <unordered_map>
#include <cstdint>
#include <cerrno>
#include "cr.h"

std::unordered_map<uint64_t, void *> state_pool;
std::unordered_map<uint64_t, void *>::iterator state_iterator;

extern "C" uint64_t get_checkpointed_states_count() {
  state_iterator = state_pool.begin();
  return state_pool.size();
}

extern "C" uint64_t get_next_key() {
  return (*state_iterator).first;
}

extern "C" void* get_next_data() {
  void* data = (*state_iterator).second;
  state_iterator++;
  return data;
}

extern "C" int insert_state(uint64_t key, void *ptr)
{
  auto it = state_pool.find(key);
  if (it != state_pool.end()) {
    return -EEXIST;
  }
  state_pool.insert({key, ptr});
  return 0;
}

extern "C" void *find_state(uint64_t key)
{
  auto it = state_pool.find(key);
  if (it == state_pool.end()) {
    return nullptr;
  } else {
    return it->second;
  }
}

extern "C" int remove_state(uint64_t key)
{
  auto it = state_pool.find(key);
  if (it == state_pool.end()) {
    return -ENOENT;
  }
  state_pool.erase(it);
  return 0;
}

extern "C" void clear_states() {
	state_pool.clear();
}
