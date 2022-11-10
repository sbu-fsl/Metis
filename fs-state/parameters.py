#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from parameter_util import SpecialParameters, RangeParameters, make_params_pml
import sys

"""
O_CREAT|O_WRONLY: 65
O_CREAT|O_WRONLY|O_EXCL: 193
O_CREAT|O_WRONLY|O_TRUNC: 577 (creat)
O_CREAT|O_WRONLY|O_DIRECT: 16449
"""
create_open_flag = make_params_pml('create_open_flag',
        SpecialParameters(65, 193, 577, 16449))

"""
600 (dec. 384): only the owner of the file has full read and write access to it.
644 (dec. 420): owner can read/write, group/others can read only.
755 (dec. 493): owner can read/write/execute, group/others can read/execute.
777 (dec. 511): all can read/write/execute (full access).
"""
create_open_mode = make_params_pml('create_open_mode',
        SpecialParameters(384, 420, 493, 511))

"""
O_RDWR: 2 (write_file)
O_RDWR|O_APPEND: 1026
O_RDWR|O_SYNC: 1052674
"""
write_open_flag = make_params_pml('write_open_flag',
        SpecialParameters(2, 1026, 1052674))

write_offset = make_params_pml('write_offset',
        SpecialParameters(1, 123, 511, 1025, 4101, 16399, 65501),
        RangeParameters(0, 65536, 4096),
        RangeParameters(11, 11111, 3333))

write_size = make_params_pml('write_size',
        SpecialParameters(3, 555, 1021, 4001, 16355, 64409),
        RangeParameters(0, 32768, 6144),
        RangeParameters(13, 33333, 7777))

write_byte = make_params_pml('write_byte',
        RangeParameters(0, 255, 1))

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
write_special_byte = make_params_pml('write_special_byte',
        SpecialParameters(0, 255, 85, 170, 240, 15, 1, 128))

truncate_len = make_params_pml('truncate_len',
        SpecialParameters(47, 995, 4111, 131001, 151111),
        RangeParameters(0, 262144, 32768),
        RangeParameters(0, 260000, 29876))

if __name__ == '__main__':
    symbols = dict(globals())
    f = open('parameters.pml', 'w')
    for k, v in symbols.items():
        if k == type(v).__name__:
            f.write(v())

    f.close()

