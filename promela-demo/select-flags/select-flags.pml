#define O_RDONLY    0
#define O_WRONLY    1
#define O_RDWR      2
#define O_CREAT     64      /* 0100 */
#define O_EXCL      128     /* 0200 */
#define O_TRUNC     512     /* 01000 */
#define O_APPEND    1024    /* 02000 */

int flags;

inline assign_flag(flags) {
    /* O_RDONLY */
    if
        :: flags = flags | O_RDONLY;
        :: skip;
    fi
    /* O_WRONLY */
    if
        :: flags = flags | O_WRONLY;
        :: skip;
    fi
    /* O_RDWR */
    if
        :: flags = flags | O_RDWR;
        :: skip;
    fi
    /* O_CREAT */
    if
        :: flags = flags | O_CREAT;
        :: skip;
    fi
    /* O_EXCL */
    if
        :: flags = flags | O_EXCL;
        :: skip;
    fi
    /* O_TRUNC */
    if
        :: flags = flags | O_TRUNC;
        :: skip;
    fi
    /* O_APPEND */
    if
        :: flags = flags | O_APPEND;
        :: skip;
    fi
}

init {
    do ::
        flags = 0;
        assign_flag(flags);
        printf("Flags: octet: 0%04o,\thex: 0x%x\n", flags, flags);
    od
}
