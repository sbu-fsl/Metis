#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Haolin Yu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

import pulp as pl
model = pl.LpProblem("Example", pl.LpMinimize)
# Assign variables
offset = pl.LpVariable('offset', lowBound=0, cat='Integer')
file_len = pl.LpVariable('file_len', lowBound=1, cat='Integer')
count = pl.LpVariable('count', lowBound=0, cat='Integer')

# Objective fxn
model += offset + file_len + count, 'Z'
# Constraints
model += offset >= file_len
# model += offset + count <= file_len - 1
model += offset + count >= file_len

print(model)

# Solve the model
model.solve()
print(pl.LpStatus[model.status])

# Print out the solution
for variable in model.variables():
    print ("{} = {}".format(variable.name, variable.varValue))