#!/usr/bin/env python3
# -*- coding: utf-8 -*-

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

import math

class SpecialParameters():

    def __init__(self, *args):
        self.params = args

    def __len__(self):
        return len(self.params)

    def __call__(self):
        return self.params

    def __str__(self):
        return str(self.params)


class RangeParameters():

    def __init__(self, start, end, step, closed_range=True):
        self.start = start
        self.end = end
        self.step = step
        if closed_range:
            self.end += 1

    def __len__(self):
        return len(range(self.start, self.end, self.step))

    def gen(self):
        if not hasattr(self, 'params'):
            self.params = [x for x in range(self.start, self.end, self.step)]
        return self.params

    def __call__(self):
        return self.gen()

    def __str__(self):
        return str(self.gen())


# start > 0
# end is closed range
class BitshiftParameters():

    def __init__(self, start, end):
        self.start = start
        self.end = end

    def gen(self):
        if not hasattr(self, 'params'):
            self.params = [2**i for i in range(int(math.log2(self.start)), int(math.log2(self.end))+1)]
        return self.params

    def __len__(self):
        return len(self.gen())

    def __call__(self):
        return self.gen()

    def __str__(self):
        return str(self.gen())


# Close to boundary parameters (powers of 2 numbers)
# +1 -1 for all the boundaries
class NearboundaryParameters():

    def __init__(self, start, end):
        self.start = start
        self.end = end

    def gen(self):
        if not hasattr(self, 'params'):
            self.bdry = [2**i for i in range(int(math.log2(self.start)), int(math.log2(self.end))+1)]
            self.params = list(set([num + 1 for num in self.bdry] + [num - 1 for num in self.bdry]))
        return self.params

    def __len__(self):
        return len(self.gen())

    def __call__(self):
        return self.gen()

    def __str__(self):
        return str(self.gen())


# +1 -1 for all the specified values
class NearvalueParameters():
    def __init__(self, *args):
        self.params = list(set([num + 1 for num in args] + [num - 1 for num in args]))

    def __len__(self):
        return len(self.params)

    def __call__(self):
        return self.params

    def __str__(self):
        return str(self.params)    


def generate_params_pml(obj):
    params = list(obj.param_set)
    params.sort()
    inline_name = 'pick_' + type(obj).__name__
    result = 'inline %s(value) {\n' % inline_name
    result += '\tif\n'
    for p in params:
        result += '\t\t:: value = %d;\n' % p
    result += '\tfi\n'
    result += '}\n'
    return result


def init_params_pml(obj, *param_generators):
    obj.param_set = set()
    for pg in param_generators:
        for p in pg():
            obj.param_set.add(p)


def make_params_pml(name, *param_generators):
    cls = type(name, (), {
        '__init__': init_params_pml,
        '__str__': generate_params_pml,
        '__call__': generate_params_pml,
        '__len__': lambda obj: len(obj.param_set),
        'get_params': lambda obj: obj.param_set,
        'generate': generate_params_pml
    })
    return cls(*param_generators)

