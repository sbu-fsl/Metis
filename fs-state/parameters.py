#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from parameter_util import SpecialParameters, RangeParameters, make_params_pml
import sys

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

