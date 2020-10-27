// Copyright (c) 2011 The LevelDB Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file. See the AUTHORS file for names of contributors.
//
// Slice is a simple structure containing a pointer into some external
// storage and a size.  The user of a Slice must ensure that the slice
// is not used after the corresponding external storage has been
// deallocated.
//
// Multiple threads can invoke const methods on a Slice without
// external synchronization, but if any of the threads may call a
// non-const method, all threads accessing the same Slice must use
// external synchronization.
//
// Copied from <leveldb>/include/leveldb/slice.h

#pragma once

#include <assert.h>
#include <ostream>  // for ostream& operator<< (ostream& os, const char* s);
#include <stddef.h>
#include <string.h>
#include <string>
/* otherwise infinite loop in
 * std::ostream& operator<<(std::ostream& oss, const Slice& a)
 */
#include "common_types.h"

namespace util {

class Slice {
       public:
        // Create an empty slice.
        Slice() : data_(""), size_(0) {}

        // Create a slice that refers to d[0,n-1].
        Slice(const char* d, size_t n) : data_(d), size_(n) {}

        // Create a slice that refers to the contents of "s"
        // NOLINTNEXTLINE
        Slice(const std::string& s) : data_(s.data()), size_(s.size()) {}

        // NOLINTNEXTLINE
        Slice(const slice_t& s) : data_(s.data), size_(s.size) {}

        // Create a slice that refers to s[0,strlen(s)-1]
        // NOLINTNEXTLINE
        Slice(const char* s) : data_(s), size_(strlen(s)) {}

        // Return a pointer to the beginning of the referenced data
        const char* data() const { return data_; }

        // Return the length (in bytes) of the referenced data
        size_t size() const { return size_; }

        // Return true iff the length of the referenced data is zero
        bool empty() const { return size_ == 0; }

        // Return the ith byte in the referenced data.
        // REQUIRES: n < size()
        char operator[](size_t n) const {
                assert(n < size());
                return data_[n];
        }

        // Change this slice to refer to an empty array
        void clear() {
                data_ = "";
                size_ = 0;
        }

        // Drop the first "n" bytes from this slice.
        void remove_prefix(size_t n) {
                assert(n <= size());
                data_ += n;
                size_ -= n;
        }

        Slice& rtrim(char c) {
                while (size_ > 0 && data_[size_ - 1] == c) --size_;
                return *this;
        }

        Slice& ltrim(char c) {
                size_t n = 0;
                while (n < size_ && data_[n] == c) ++n;
                remove_prefix(n);
                return *this;
        }

        Slice& trim(char c) {
                rtrim(c);
                ltrim(c);
                return *this;
        }

        slice_t toslice() const { return mkslice(data_, size_); }

        // Return a string that contains the copy of the referenced data.
        std::string ToString() const { return std::string(data_, size_); }

        // Three-way comparison.  Returns value:
        //   <  0 iff "*this" <  "b",
        //   == 0 iff "*this" == "b",
        //   >  0 iff "*this" >  "b"
        int compare(const Slice& b) const;

        // Return true iff "x" is a prefix of "*this"
        bool starts_with(const Slice& x) const {
                return ((size_ >= x.size_) &&
                        (memcmp(data_, x.data_, x.size_) == 0));
        }

       private:
        const char* data_;
        size_t size_;

        // Intentionally copyable
};

inline bool operator==(const Slice& x, const Slice& y) {
        return ((x.size() == y.size()) &&
                (memcmp(x.data(), y.data(), x.size()) == 0));
}

inline bool operator!=(const Slice& x, const Slice& y) { return !(x == y); }

inline int Slice::compare(const Slice& b) const {
        const size_t min_len = (size_ < b.size_) ? size_ : b.size_;
        int r = memcmp(data_, b.data_, min_len);
        if (r == 0) {
                if (size_ < b.size_)
                        r = -1;
                else if (size_ > b.size_)
                        r = +1;
        }
        return r;
}

inline std::ostream& operator<<(std::ostream& oss, const Slice& a) {
        oss << a.data();
        return oss;
}

}  // namespace util

// vim:sw=2:ts=2:tw=80:expandtab:cinoptions=>2,(0\:0:
