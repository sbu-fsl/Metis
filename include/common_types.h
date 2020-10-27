/**
 * Copyright (C) Stony Brook University 2016
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 */

#ifndef __TC_UTIL_TYPES_H__
#define __TC_UTIL_TYPES_H__

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
        size_t capacity;
        size_t size;
        char *data;
} buf_t;

typedef struct {
        size_t size;
        const char *data;
} slice_t;

typedef struct {
        size_t size;
        unsigned char bits[0];
} bitset_t;

static inline bitset_t *new_bitset(size_t s) {
        bitset_t *bs = (bitset_t *)calloc(1, sizeof(bitset_t) + ((s + 7) / 8));
        bs->size = s;
        return bs;
}

static inline void del_bitset(bitset_t *bs) { free(bs); }

static inline void bs_set(bitset_t *bs, size_t pos) {
        if (pos < bs->size) {
                bs->bits[pos / 8] |= (1 << (pos % 8));
        }
}

static inline void bs_set_all(bitset_t *bs) {
        memset(bs->bits, 255, (bs->size + 7) / 8);
}

static inline void bs_reset_all(bitset_t *bs) {
        memset(bs->bits, 0, (bs->size + 7) / 8);
}

static inline int bs_ffs(bitset_t *bs) {
        size_t i;
        int res = -1;
        const size_t N = (bs->size + 7) / 8;

        for (i = 0; i < N; ++i) {
                res = ffs(bs->bits[i]);
                if (res > 0) {
                        assert(res <= 8);
                        res += ((i * 8) - 1);
                        return (size_t)(res) < bs->size ? res : -1;
                }
        }

        return -1;
}

static inline bool bs_get(bitset_t *bs, size_t pos) {
        return pos < bs->size ? (bs->bits[pos / 8] & (1 << (pos % 8))) : 0;
}

static inline void bs_reset(bitset_t *bs, size_t pos) {
        if (pos < bs->size) {
                bs->bits[pos / 8] &= ~(1 << (pos % 8));
        }
}

static inline bitset_t *init_bitset(void *buf, size_t s) {
        bitset_t *bs = (bitset_t *)(buf);
        bs->size = s;
        memset(bs->bits, 0, (s + 7) / 8);
        return bs;
}

#define new_auto_bitset(s) \
        init_bitset(alloca(sizeof(bitset_t) + ((s + 7) / 8)), s)

#define BUF_INITIALIZER(b, c) \
        { .capacity = (c), .size = 0ULL, .data = (b), }

static inline buf_t mkbuf(char *b, size_t c) {
        buf_t buf = BUF_INITIALIZER(b, c);
        return buf;
}

static inline buf_t *init_buf(void *rawbuf, size_t c) {
        if (!rawbuf) return NULL;
        buf_t *pbuf = (buf_t *)rawbuf;
        pbuf->capacity = c;
        pbuf->size = 0;
        pbuf->data = ((char *)rawbuf) + sizeof(buf_t);
        return pbuf;
}

static inline buf_t *new_buf(size_t c) {
        return init_buf(malloc(sizeof(buf_t) + c), c);
}

static inline void del_buf(buf_t *pbuf) { free(pbuf); }

/**
 * A buffer allocated on stack and will be freed automatically once out of
 * scope.  Usage:
 *
 *	buf_t *abuf = new_auto_buf(c);
 *
 * Note: "c" must NOT be an expression with side-effects like "++i".
 */
#define new_auto_buf(c) init_buf(alloca((c) + sizeof(buf_t)), (c))

#define new_auto_str(sl) strndupa(sl.data, sl.size)

static inline slice_t mkslice(const char *d, size_t s) {
        slice_t sl;
        sl.data = d;
        sl.size = s;
        return sl;
}

static inline slice_t toslice(const char *d) {
        slice_t sl;
        sl.data = d;
        sl.size = d ? strlen(d) : 0;
        return sl;
}

static inline void fillslice(slice_t *sl, const char *d, size_t s) {
        if (sl) {
                sl->data = d;
                sl->size = s;
        }
}

static inline slice_t *slice_lstrip(slice_t *sl, char c) {
        size_t i;

        for (i = 0; i < sl->size && sl->data[i] == c; ++i)
                ;
        sl->data += i;
        sl->size -= i;
        return sl;
}

static inline slice_t *slice_rstrip(slice_t *sl, char c) {
        while (sl->size > 0 && sl->data[sl->size - 1] == c) sl->size--;
        return sl;
}

static inline ssize_t slice_lindex(slice_t sl, char c) {
        size_t i;
        for (i = 0; i < sl.size && sl.data[i] != c; ++i)
                ;
        return i == sl.size ? -1 : i;
}

static inline ssize_t slice_rindex(slice_t sl, char c) {
        ssize_t i;
        for (i = sl.size - 1; i >= 0 && sl.data[i] != c; --i)
                ;
        return i;
}

static inline slice_t asslice(const buf_t *pbuf) {
        return mkslice(pbuf->data, pbuf->size);
}

static inline int buf_append_slice(buf_t *pbuf, slice_t sl) {
        if (pbuf->size + sl.size > pbuf->capacity) {
                return -1;
        }
        if (pbuf->data + pbuf->size != sl.data)
                memmove(pbuf->data + pbuf->size, sl.data, sl.size);
        pbuf->size += sl.size;
        return sl.size;
}

static inline int buf_append_str(buf_t *pbuf, const char *s) {
        return buf_append_slice(pbuf, toslice(s));
}

static inline int buf_append_buf(buf_t *dst, const buf_t *src) {
        return buf_append_slice(dst, asslice(src));
}

static inline int buf_append_char(buf_t *pbuf, char c) {
        if (pbuf->capacity <= pbuf->size) {
                assert(pbuf->capacity == pbuf->size);
                return -1;
        }
        pbuf->data[pbuf->size++] = c;
        return 1;
}

static inline bool buf_append_null(buf_t *pbuf) {
        int res = buf_append_char(pbuf, 0);
        if (res > 0) {
                // The ending '\0' should not be counted.
                --pbuf->size;
                --res;
        }
        return res >= 0;
}

static inline char *asstr(buf_t *pbuf) {
        return buf_append_null(pbuf) ? pbuf->data : NULL;
}

static inline char *buf_end(buf_t *pbuf) { return pbuf->data + pbuf->size; }

static inline size_t buf_remaining(const buf_t *pbuf) {
        return pbuf->capacity - pbuf->size;
}

static inline buf_t *buf_reset(buf_t *pbuf) {
        pbuf->size = 0;
        return pbuf;
}

static inline int buf_printf(buf_t *pbuf, const char *format, ...) {
        va_list args;

        va_start(args, format);
        pbuf->size = vsnprintf(pbuf->data, pbuf->capacity, format, args);
        va_end(args);

        return pbuf->size;
}

/**
 * Append a string to pbuf, return the number of bytes appended.
 */
static inline int buf_appendf(buf_t *pbuf, const char *format, ...) {
        int n;
        va_list args;

        va_start(args, format);
        n = vsnprintf(buf_end(pbuf), buf_remaining(pbuf), format, args);
        va_end(args);
        if (n < 0) {
                return n;
        } else if ((size_t)n > buf_remaining(pbuf)) {
                return -ENOMEM;
        }

        pbuf->size += n;
        assert(pbuf->size <= pbuf->capacity);

        return n;
}

static inline int cmpslice(slice_t sa, slice_t sb) {
        size_t i;

        for (i = 0; i < sa.size && i < sb.size; ++i) {
                if (sa.data[i] != sb.data[i]) {
                        return sa.data[i] - sb.data[i];
                }
        }
        if (sa.size == sb.size) {
                return 0;
        } else if (sa.size < sb.size) {
                return -1;
        } else {
                return 1;
        }
}

#ifdef __cplusplus
}
#endif

#endif  // __TC_UTIL_TYPES_H__
