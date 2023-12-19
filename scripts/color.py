#!/usr/bin/env python3

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

# Color output in Unix terminal

from enum import Enum
import os, re
from sys import argv

ESC = '\033'
BEGIN_CHR = '@'
END_CHR = '$'
class BasicColors(Enum):
    BLACK = 0
    BLK = 0
    RED = 1
    GREEN = 2
    GRN = 2
    YELLOW = 3
    YEL = 3
    BLUE = 4
    BLU = 4
    MAGENTA = 5
    MAG = 5
    CYAN = 6
    CYA = 6
    WHITE = 7
    WHI = 7


def reset_code():
    return '%c[0m' % ESC


def check_color_code(code, scheme):
    if code is None:
        return BasicColors['BLACK'].value
    try:
        code = int(code)
    except Exception:
        pass
    if isinstance(code, int):
        if code >= scheme or code < 0:
            raise ValueError('Out of color range (%d)' % scheme)
        return code
    elif isinstance(code, str):
        try:
            return BasicColors[code.upper()].value
        except KeyError:
            raise ValueError('Invalid color name')
    else:
        raise TypeError('Color code shall be integer or string, but got %s' % str(type(code)))



def generate_xterm_color_code(fg=7, bg=0, light=False):
    fcode = 30 + check_color_code(fg, 8)
    bcode = 40 + check_color_code(bg, 8)
    if light:
        return '%c[%d;%d;1m' % (ESC, fcode, bcode)
    else:
        return '%c[%d;%dm' % (ESC, fcode, bcode)


def generate_xterm_256_code(fg=7, bg=0, light=False):
    fcode = check_color_code(fg, 256)
    bcode = check_color_code(bg, 256)
    if light and fcode < 7 and fcode >= 0:
        fcode += 8
    return '%c[38;5;%dm%c[48;5;%dm' % (ESC, fcode, ESC, bcode)


def color_fallback(code):
    if isinstance(code, str):
        return code
    if isinstance(code, int):
        if code >= 232:
            return 0 if code <= 243 else 7
        if code > 7:
            # Retrive R,G,B of the color value
            code -= 16
            r = 1 if code // 36 >= 3 else 0
            g = 1 if (code % 36) // 6 >= 3 else 0
            b = 1 if (code % 36) % 6 >= 3 else 0
            return b * 4 + g * 2 + r * 1


def get_color_cstr(foreground='BLK', background='WHI', light=False):
    term = os.getenv('TERM')
    if term == 'xterm-256color':
        return generate_xterm_256_code(foreground, background, light)
    else:
        foreground = color_fallback(foreground)
        background = color_fallback(background)
        return generate_xterm_color_code(foreground, background, light)


def matcher(matchobj):
    exp = matchobj.group(1)
    light = False
    # Need to have '@...$' in text: Use '@@...$'
    if exp == '!' or exp == 'end':
        return reset_code()
    if exp.startswith('@'):
        return exp + '$'
    exp = exp.replace('#', '')
    parameters = exp.split(',')
    if len(parameters) == 2:
        fore, back = parameters
    elif len(parameters) == 3:
        fore = parameters[0]
        back = parameters[1]
        light = True if parameters[2].lower() == 'true' else False
    else:
        fore = parameters[0]
        back = BasicColors.BLACK.value
    return get_color_cstr(fore, back, light)


def format_color_scheme(input_str):
    pattern = r'@{1}(.*?)\${1}'
    return re.sub(pattern, matcher, input_str)


def cprint(input_str, legacy=False, **kwargs):
    return print(format_color_scheme(input_str), **kwargs)


def cprints(input_str, legacy=False):
    return format_color_scheme(input_str)

if __name__ == '__main__':
    cprint(' '.join(argv[1:]))

