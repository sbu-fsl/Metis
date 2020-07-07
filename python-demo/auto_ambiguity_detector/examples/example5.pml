/* NFS_READ simplified client/server example */

/*
* @Author: Missing
* Revised by Haolin 6/20/2020
*/

/* NFS status/error codes */
mtype:nfsstat = {
    NFS4_OK,
    NFS4ERR_STALE,
    NFS4ERR_INVAL,
    NFS4ERR_ISDIR,
    NFS4ERR_PERM,
    NFS4ERR_NOENT
}
/* file type: regular, directory, etc. */
mtype:filetype = {
    NF4REG,
    NF4DIR,
    NF4INVAL
}

/* file handler */
typedef FH {
    byte fh[3];
}

/* data read */
typedef DATA {
    int d[3];
}

/* global channels (implementation omitted) */
chan qcfh_check = [1] of {bool}; /* check current file handle validity */
chan qcfh_type = [1] of {mtype:filetype}; /* get type of current file handle */
chan quser_perm = [1] of {bool}; /* check if user has permission to file */
chan qfile_len = [1] of {int}; /* get file length in bytes (-1 == ENOENT) */
/* proctypes omitted: CFH_CHECK, CFH_TYPE, USER_PERM, FILE_LEN */
/* proctypes omitted: FILE_BYTES (reading file bytes from Ext4) */

proctype CFH_CHECK(FH chf; chan reply) {
    // check omitted
    if 
        ::reply!true;
        ::reply!false;
    fi
}

proctype CFH_TYPE(FH chf; chan reply) {
    // check omitted
    if 
        ::reply!NF4REG;
        ::reply!NF4DIR;
        ::reply!NF4INVAL;
    fi
}

proctype USER_PERM(FH chf; chan reply) {
    // check omitted
    if
        ::reply!true;
        ::reply!false;
    fi
}

proctype FILE_LEN(FH chf; chan reply) {
    // check omitted
    if
        ::reply!-1;
        ::reply!20;
    fi
}

proctype FILE_BYTES(chan reply; FH chf; bool eof; int offset; int count) {
    // read omitted
    DATA data;
    if
        ::(eof == false) -> {
            data.d[0] = 5;
            data.d[1] = 3;
            data.d[2] = 2;
            reply ! NFS4_OK, false, count, data;
        }
        ::(eof == true) -> {
            data.d[0] = 5;
            data.d[1] = 3;
            count = 2;
            reply ! NFS4_OK, false, count, data;
        }
    fi
}

proctype NFS_CLIENT(chan qrequest; chan qreply) {
    /* assume translated from read(2) fd */
    FH cfh;
    cfh.fh[0] = 0;
    cfh.fh[1] = 1;
    cfh.fh[2] = 2;
    /* assume inputs from read((2) syscall */
    /* generate random offset, and count */
    int offset = 0;
    if
        ::offset = 0;
        ::offset = 5;
        ::offset = 18;
        ::offset = 50;
        ::offset = 100;
    fi
    int count = 3;
    mtype:nfsstat retval;
    bool eof;
    int data_len;
    DATA data;
    qrequest ! cfh, offset, count; /* send request to server */
    qreply ? retval, eof, data_len, data; /* get status from server */
    if
        ::(retval != NFS4_OK) -> printf("read request failed with code %d\n", retval)
        ::(retval == NFS4_OK) -> {
            /* receive actual data on success */
            printf("read request succeeded: eof=%d, data=\"%d%d%d\"\n", eof, data.d[0], data.d[1], data.d[2])
        }
    fi
}

proctype NFS_SERVER(chan qrequest; chan qreply) {
    bool is_valid_cfh, is_permission;
    FH cfh;
    DATA nondata;
    mtype:filetype cfh_type;
    int file_len;
    int offset, count;
    qrequest ? cfh, offset, count; /* get request request parameters from client */
    /* validate cfh */
    run CFH_CHECK(cfh, qcfh_check);
    qcfh_check ? is_valid_cfh;
    printf("Is valid: %d\n", is_valid_cfh);
    if
        ::(is_valid_cfh != true) -> {
            qreply ! NFS4ERR_STALE, false, -1, nondata;
            goto read_failed
        }
        :: else -> skip;
    fi
    /* check file type */
    run CFH_TYPE(cfh, qcfh_type);
    qcfh_type ? cfh_type;
    printf("File type: %d\n", cfh_type);
    if
        ::(cfh_type == NF4DIR) -> {
            printf("Read dir, read failed.\n");
            qreply ! NFS4ERR_ISDIR, false, -1, nondata;
            goto read_failed
        }
        ::(cfh_type != NF4DIR && cfh_type != NF4REG) -> {
            qreply ! NFS4ERR_INVAL, false, -1, nondata;
            goto read_failed
        }
        ::else -> skip;
    fi
    /* check that user has permission to read file */
    run USER_PERM(cfh, quser_perm);
    quser_perm ? is_permission;
    printf("User permission: %d\n", is_permission);
    if
        ::(is_permission != true) -> {
            qreply ! NFS4ERR_PERM, false, -1, nondata;
            goto read_failed
        }
        ::else -> skip;
    fi
    run FILE_LEN(cfh, qfile_len);
    qfile_len ? file_len;
    printf("File len: %d\n", file_len);
    if
        ::(file_len < 0) -> {
            qreply ! NFS4ERR_NOENT, false, -1, nondata;
            goto read_failed
        }
        ::else -> skip;
    fi
    if 
        ::(offset >= file_len) -> {
            printf("Case 2: offset over file len, skip reading\n")
            qreply ! NFS4_OK, true, 0, nondata;
            goto read_success
            }
        ::(offset + count < file_len) -> {
            printf("Case 3: legit reading, full reading, process the request\n")
            /* full read: read count bytes at cfh offset and send to qreply */
            run FILE_BYTES(qreply, cfh, false, offset, count);
            goto read_success
        }
        /* AMBIGUITY 2: need "offset < file_len" check */
        ::(offset + count >= file_len) -> {
            printf("Case 4: legit reading, partial reading, processs the request\n");
            /* partial read: read actual bytes at cfh offset and send to qreply */
            run FILE_BYTES(qreply, cfh, true, offset, file_len - offset + count);
            goto read_success
        }
    fi

read_failed: /* exit with error status */
    skip;
read_success: /* exit with success status */
    skip
}

init {
    /* client sends, server gets: cfh, offset, count */
    chan qrequest = [3] of {FH, int, int};

    /* server returns to client: retval*/
    chan qreply = [4] of {mtype: nfsstat, bool, int, DATA};

    run NFS_CLIENT(qrequest, qreply);
    run NFS_SERVER(qrequest, qreply);
}