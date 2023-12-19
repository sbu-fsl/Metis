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

#ifndef _VECTOR_H
#define _VECTOR_H

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>

#define DEFAULT_INITCAP 16

struct vector {
    unsigned char *data;
    size_t unitsize;
    size_t len;
    size_t capacity;
};

typedef struct vector vector_t;

static inline void _vector_init(struct vector *vec, size_t unitsize, size_t initcap) {
    if (initcap < DEFAULT_INITCAP)
        initcap = DEFAULT_INITCAP;
    vec->unitsize = unitsize;
    vec->len = 0;
    vec->capacity = initcap;
    vec->data = (unsigned char *)calloc(initcap, unitsize);
}
#define vector_init_2(vec, type)    _vector_init(vec, sizeof(type), DEFAULT_INITCAP)
#define vector_init_3(vec, type, initcap)   _vector_init(vec, sizeof(type), initcap)
#define vector_init_x(a, b, c, func, ...)   func
/* Macro function with optional arg: vector_init(struct vector *vec, type, [initcap=16]) */
#define vector_init(...)    vector_init_x(__VA_ARGS__,\
                                          vector_init_3(__VA_ARGS__),\
                                          vector_init_2(__VA_ARGS__)\
                                         )

static inline int vector_expand(struct vector *vec) {
    size_t newcap = vec->unitsize * vec->capacity * 2;
    unsigned char *newptr = (unsigned char *)realloc(vec->data, newcap);
    if (newptr == NULL)
        return ENOMEM;
    vec->data = newptr;
    vec->capacity *= 2;
    return 0;
}

static inline int vector_add(struct vector *vec, void *el) {
    int ret;
    if (vec->len >= vec->capacity) {
        if ((ret = vector_expand(vec)) != 0)
            return ret;
    }
    size_t offset = vec->len * vec->unitsize;
    memcpy(vec->data + offset, el, vec->unitsize);
    vec->len++;
    return 0;
}

static inline void *_vector_get(struct vector *vec, size_t index) {
    if (index < 0 || index >= vec->len)
        return NULL;
    return (void *)(vec->data + index * vec->unitsize);
}
#define vector_get(vec, type, index) \
    (type *)_vector_get(vec, index)

static inline void *_vector_peek_top(struct vector *vec) {
    if (vec->len == 0)
        return NULL;
    return (void *)(vec->data + (vec->len - 1) * vec->unitsize);
}
#define vector_peek_top(vec, type) \
    (type *)_vector_peek_top(vec)

static inline void vector_try_shrink(struct vector *vec) {
    if (vec->len >= vec->capacity / 2)
        return;
    if (vec->len <= DEFAULT_INITCAP)
        return;
    size_t newcap = vec->capacity / 2 * vec->unitsize;
    vec->data = (unsigned char *)realloc(vec->data, newcap);
}

static inline void vector_pop_back(struct vector *vec) {
    if (vec->len == 0)
        return;
    vec->len--;
    vector_try_shrink(vec);
}

static inline int vector_set(struct vector *vec, size_t index, void *el) {
    if (index < 0 || index >= vec->len)
        return ERANGE;
    size_t offset = vec->unitsize * index;
    memcpy(vec->data + offset, el, vec->unitsize);
    return 0;
}

static inline int vector_erase(struct vector *vec, size_t index) {
    if (index >= vec->len)
        return ERANGE;
    size_t dest_off = index * vec->unitsize;
    size_t src_off = (index + 1) * vec->unitsize;
    size_t count = (vec->len - index - 1) * vec->unitsize;
    memmove(vec->data + dest_off, vec->data + src_off, count);
    vec->len--;
    vector_try_shrink(vec);
    return 0;
}

static inline void vector_sort(struct vector *vec,
                               int (*comp)(const void *, const void *))
{
    qsort(vec->data, vec->len, vec->unitsize, comp);
}

static inline size_t vector_length(struct vector *vec) {
    return vec->len;
}

static inline size_t vector_memusage(struct vector *vec) {
    return vec->capacity * vec->unitsize;
}

static inline size_t vector_size(struct vector *vec) {
    return vec->len * vec->unitsize;
}

static inline void vector_destroy(struct vector *vec) {
    free(vec->data);
    memset(vec, 0, sizeof(struct vector));
}

#define vector_iter(vec, type, entry) \
    int _i; \
    for (entry = (type *)((vec)->data), _i = 0; _i < (vec)->len; ++_i, ++entry)

#endif
