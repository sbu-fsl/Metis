#ifndef _CR_IOCTL_H
#define _CR_IOCTL_H

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

#endif // _CR_IOCTL_H
