/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <stdbool.h>

#define UNIT_BITS 3

struct node {
  uint64_t value;
  struct node *branches[1 << UNIT_BITS];
};

struct node root;
const uint64_t MASK = ~(UINT64_MAX << UNIT_BITS);

static inline void insert_value(uint64_t val)
{
  struct node *ptr = &root;
  uint64_t unit = 0, val2 = val;
  while (val > 0) {
    unit = val & MASK;
    if (!ptr->branches[unit]) {
      ptr->branches[unit] = (struct node *)calloc(1, sizeof(struct node));
    }
    ptr = ptr->branches[unit];
    val >>= UNIT_BITS;
  }
  ptr->value = val2;
}

static inline bool search(uint64_t val)
{
  struct node *ptr = &root;
  uint64_t unit = 0, val2 = val;
  while (val > 0) {
    unit = val & MASK;
    if (!ptr->branches[unit])
      return false;
    ptr = ptr->branches[unit];
    val >>= UNIT_BITS;
  }
  return (ptr->value == val2);
}

static inline bool seq_contains(uint64_t seq, uint8_t val)
{
  while (seq > 0) {
    if ((seq & MASK) == val) {
      return true;
    }
    seq >>= UNIT_BITS;
  }
  return false;
}
