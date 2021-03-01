#!/usr/bin/env python3
# -*- coding: utf-8 -*-

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

