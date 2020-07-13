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