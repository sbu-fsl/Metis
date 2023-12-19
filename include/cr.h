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

#ifndef _VERIFS_CR_H
#define _VERIFS_CR_H

#ifdef __cplusplus
extern "C" {
#endif
#include <sys/ioctl.h>
#include <stddef.h>

struct verifs_str {
  size_t len;
  char *str;
};

#define VERIFS_IOC_CODE    '1'
#define VERIFS_IOC_NO(x)   (VERIFS_IOC_CODE + (x))
#define VERIFS_IOC(n)      _IO(VERIFS_IOC_CODE, VERIFS_IOC_NO(n))
#define VERIFS_GET_IOC(n, type)  _IOR(VERIFS_IOC_CODE, VERIFS_IOC_NO(n), type)
#define VERIFS_SET_IOC(n, type)  _IOW(VERIFS_IOC_CODE, VERIFS_IOC_NO(n), type)

#define VERIFS_CHECKPOINT  VERIFS_IOC(1)
#define VERIFS_RESTORE     VERIFS_IOC(2)

// the PICKLE and LOAD should receive a parameter of `struct verifs_str` which
// contains the path to the output / input file.
#define VERIFS_PICKLE      VERIFS_SET_IOC(3, struct verifs_str)
#define VERIFS_LOAD        VERIFS_SET_IOC(4, struct verifs_str)

#ifdef __cplusplus
}
#endif

#endif // _VERIFS_CR_H
