#ifndef _CRMFS_CR_H
#define _CRMFS_CR_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/ioctl.h>

#define CRMFS_IOC_CODE    '1'
#define CRMFS_IOC_NO(x)   (CRMFS_IOC_CODE + (x))
#define CRMFS_IOC(n)      _IO(CRMFS_IOC_CODE, CRMFS_IOC_NO(n))
#define CRMFS_GET_IOC(n, type)  _IOR(CRMFS_IOC_CODE, CRMFS_IOC_NO(n), type)
#define CRMFS_SET_IOC(n, type)  _IOW(CRMFS_IOC_CODE, CRMFS_IOC_NO(n), type)

#define CRMFS_CHECKPOINT  CRMFS_IOC(1)
#define CRMFS_RESTORE     CRMFS_IOC(2)

int insert_state(uint64_t key, void *ptr);
void *find_state(uint64_t key);
int remove_state(uint64_t key);

#ifdef __cplusplus
}
#endif

#endif // _CRMFS_CR_H 
