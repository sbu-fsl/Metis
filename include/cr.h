#ifndef _VERIFS_CR_H
#define _VERIFS_CR_H
#define MAX_FILE_LEN 100

#ifdef __cplusplus
extern "C" {
#endif
#include <sys/ioctl.h>
#include <openssl/sha.h>


struct verifs_str {
  size_t len;
  char str[MAX_FILE_LEN];
};

struct state_file_header {
    size_t fsize;
    unsigned char hash[SHA256_DIGEST_LENGTH];
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
#define VERIFS_PICKLE       VERIFS_IOC(3)
#define VERIFS_LOAD         VERIFS_IOC(4)
#define VERIFS_PICKLE_CFG  "/tmp/pickle.cfg"
#define VERIFS_LOAD_CFG    "/tmp/pickle.cfg"

#ifdef __cplusplus
}
#endif

#endif // _VERIFS_CR_H
