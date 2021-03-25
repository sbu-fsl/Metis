#ifndef _VERIFS_CR_H
#define _VERIFS_CR_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/ioctl.h>

#define VERIFS_IOC_CODE    '1'
#define VERIFS_IOC_NO(x)   (VERIFS_IOC_CODE + (x))
#define VERIFS_IOC(n)      _IO(VERIFS_IOC_CODE, VERIFS_IOC_NO(n))
#define VERIFS_GET_IOC(n, type)  _IOR(VERIFS_IOC_CODE, VERIFS_IOC_NO(n), type)
#define VERIFS_SET_IOC(n, type)  _IOW(VERIFS_IOC_CODE, VERIFS_IOC_NO(n), type)

#define VERIFS_CHECKPOINT  VERIFS_IOC(1)
#define VERIFS_RESTORE     VERIFS_IOC(2)

int insert_state(uint64_t key, void *ptr);
void *find_state(uint64_t key);
int remove_state(uint64_t key);

#ifdef __cplusplus
}
#endif

#endif // _VERIFS_CR_H 
