#!/usr/bin/env python3
# -*- coding: utf-8 -*-

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

from parameter_util import SpecialParameters, RangeParameters, BitshiftParameters, NearboundaryParameters, NearvalueParameters, make_params_pml
import sys

"""
octal 101 (dec. 65): O_CREAT|O_WRONLY
octal 301 (dec. 193): O_CREAT|O_WRONLY|O_EXCL
octal 1101 (dec. 577) (creat syscall & create_file): O_CREAT|O_WRONLY|O_TRUNC
octal 40101 (dec. 16449): O_CREAT|O_WRONLY|O_DIRECT
Note: JFFS2 does not support O_DIRECT, delete 0o40101 while testing JFFS2.
"""
create_open_flag = make_params_pml('create_open_flag',
        SpecialParameters(0o101, 0o301, 0o1101, 0o40101))

"""
octal 600 (dec. 384): only the owner of the file has full read and write access to it.
octal 640 (dec. 416): owner can read/write, group can read, others cannot read
octal 644 (dec. 420): owner can read/write, group/others can read only.
octal 755 (dec. 493): owner can read/write/execute, group/others can read/execute.
octal 777 (dec. 511): all can read/write/execute (full access).
"""
create_open_mode = make_params_pml('create_open_mode',
        SpecialParameters(0o600, 0o640, 0o644, 0o755, 0o777))

"""
octal 2 (dec. 2): O_RDWR (write_file)
octal 2002 (dec. 1026): O_RDWR|O_APPEND
octal 4010002 (dec. 1052674): O_RDWR|O_SYNC
"""
write_open_flag = make_params_pml('write_open_flag',
        SpecialParameters(0o2, 0o2002, 0o4010002))

# write_offset = make_params_pml('write_offset',
#         SpecialParameters(1, 123, 511, 1025, 4101, 16399, 65501),
#         RangeParameters(0, 65536, 4096),
#         RangeParameters(11, 11111, 3333))

write_offset = make_params_pml('write_offset',
        BitshiftParameters(1, 65536),
        NearboundaryParameters(1, 65536))

# write_size = make_params_pml('write_size',
#         SpecialParameters(3, 555, 1021, 4001, 16355, 64409),
#         RangeParameters(0, 32768, 6144),
#         RangeParameters(13, 33333, 7777))

# 4294967296: 2^32
# 17592186044416: 2^44 16 TiB (ext4 max file size)
write_size = make_params_pml('write_size',
        BitshiftParameters(1, 65536),
        NearboundaryParameters(1, 65536))

# write_byte = make_params_pml('write_byte',
#         RangeParameters(0, 255, 1))

"""
Pick Special Write Bytes:
0x00 == 0 (all 0s)
0xFF == 255 (all 1s)
0x55 == 85 (alt 0s and 1s)
0xAA == 170
0xF0 == 240
0x0F == 15
0x01 == 1 (LSB)
0x80 == 128 (MSB)
"""
write_byte = make_params_pml('write_byte',
        SpecialParameters(0, 255, 85))

# truncate_len = make_params_pml('truncate_len',
#         SpecialParameters(47, 995, 4111, 131001, 151111),
#         RangeParameters(0, 262144, 32768),
#         RangeParameters(0, 260000, 29876))

truncate_len = make_params_pml('truncate_len',
        BitshiftParameters(1, 65536),
        NearboundaryParameters(1, 65536))
        

"""
600 (dec. 384): only the owner of the file has full read and write access to it.
640 (dec. 416): owner can read/write, group can read, others cannot read
644 (dec. 420): owner can read/write, group/others can read only.
755 (dec. 493): owner can read/write/execute, group/others can read/execute.
777 (dec. 511): all can read/write/execute (full access).
"""
chmod_mode = make_params_pml('chmod_mode',
        SpecialParameters(384, 416, 420, 493, 511))

"""
uid=0(root) gid=0(root)
uid=1000(ubuntu) gid=1000(ubuntu)
"""
chown_owner = make_params_pml('chown_owner',
        SpecialParameters(0, 1000))

chown_group = make_params_pml('chown_group',
        SpecialParameters(0, 1000))

if __name__ == '__main__':
    symbols = dict(globals())
    f = open('parameters.pml', 'w')
    for k, v in symbols.items():
        if k == type(v).__name__:
            f.write(v())

    f.close()

