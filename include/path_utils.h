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

#ifndef __TC_PATH_UTILS_H__
#define __TC_PATH_UTILS_H__

#include "common_types.h"

#ifdef __cplusplus
extern "C" {
#endif

#include <stdarg.h>

/**
 * Tokenize "path" into "components"; return the number of components inside
 * path on success, or -1 on failure.
 *
 * Caller owns "components" and is responsible for freeing it.
 */
int tc_path_tokenize(const char *path, slice_t **components);
int tc_path_tokenize_s(slice_t path, slice_t **components);

/**
 * Normalize a path and save the result into "buf".  Normalization include
 * removing ".", "..", consecutive "//", and trailing "/".
 * For example:
 *
 * "/" -> "/"
 * "//" -> "/"
 * "/foo/bar/" -> "/foo/bar"
 * "/foo/../bar/" -> "/bar"
 * "/foo/../../../" -> "/"
 *
 * "path" and "buf" may be the same.
 *
 * Returns the size of the normalized path, or -1 in case of error.
 */
int tc_path_normalize(const char *path, char *buf, size_t buf_size);
int tc_path_normalize_s(slice_t path, buf_t *pbuf);

/**
 * Return the depth of the path in the FS tree. "/" is zero; "/foo" is one;
 * "/foo/bar" is two.
 */
int tc_path_depth(const char *path);
int tc_path_depth_s(slice_t path);

/**
 * Return the distance of two nodes in the FS tree. For example, the distance
 * is 1 between between "/" and "/foo", 2 between "/foo" and "/bar".
 *
 * When "dst" is a relative path, "src" is not used and can be NULL.
 * When "dst" is an absolute path, "src" must be an ansolute path.
 */
int tc_path_distance(const char *src, const char *dst);
int tc_path_distance_s(slice_t src, slice_t dst);

/**
 * Convert "path" to relative path based on "base".  The result relative path
 * is stored in "buf".
 *
 * NOTE: "buf" must not overlap with "path"
 *
 * Return the size of the resultant "path".
 */
int tc_path_rebase(const char *base, const char *path, char *buf,
                   size_t buf_size);
int tc_path_rebase_s(slice_t base, slice_t path, buf_t *pbuf);

/**
 * Join "path1" and "path2" to "buf".
 *
 * "buf" and "path1" may be the same.
 *
 * Return the length of the joined path.
 */
int tc_path_join(const char *path1, const char *path2, char *buf,
                 size_t buf_size);
int tc_path_join_s(slice_t path1, slice_t path2, buf_t *pbuf);
int tc_path_append(buf_t *pbuf, slice_t comp);

slice_t tc_path_dirname_s(slice_t path);
slice_t tc_path_basename_s(slice_t path);

/**
 * Break path into dirname and basename.
 *
 * Return if a path separator is found '/'.
 */
bool tc_path_dir_base_s(slice_t path, slice_t *dir, slice_t *base);

static inline slice_t tc_path_dirname(const char *path) {
        return tc_path_dirname_s(toslice(path));
}

static inline slice_t tc_path_basename(const char *path) {
        return tc_path_basename_s(toslice(path));
}

static inline bool tc_path_dir_base(const char *path, slice_t *dir,
                                    slice_t *base) {
        return tc_path_dir_base_s(toslice(path), dir, base);
}

int _tc_path_joinall_impl(char *buf, size_t buf_size, int n, ...);

#define TC_NUMPATHS(...) \
        (sizeof((const char *[]){__VA_ARGS__}) / sizeof(const char *))

#define tc_path_joinall(buf, buf_size, ...)                                \
        _tc_path_joinall_impl((buf), (buf_size), TC_NUMPATHS(__VA_ARGS__), \
                              __VA_ARGS__)

#ifdef __cplusplus
}
#endif

#endif  // __TC_PATH_UTILS_H__
