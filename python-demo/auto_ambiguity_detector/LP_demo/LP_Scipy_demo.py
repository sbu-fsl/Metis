from scipy.optimize import linprog
import numpy as np

# A_ineq X <= B_ineq
# A_eq X = B_eq
# min(C^T)

# Equations to solve
# offset >= file_len
# offset + count < file_len
# offset + count >= file_len
# Minimize (offset + count + file_len) -> we don't have a upper limit. Most variables are from 0. It's better to find the minimum.

# trans it to A_ineq <= B_ineq
# 
# file_len - offset <= 0
# offset + count - file_len < 0
# file_len - offset - count <= 0

# # X matrix
# var_list = ['count', 'file_len', 'offset']

# # Inequality equations, LHS
# A_ineq = [[0, 1, -1], [1, -1, 1], [-1, 1, -1]]

# # Inequality equations, RHS
# B_ineq = [0, 0, 0]

# # Equality equations, LHS
# # A_eq = [[1, 1, 1]]

# # Equality equations, RHS
# # B_eq = [0]

# # Cost a cost function
# c = [1, 1, 1]


# res_no_bounds = linprog(c, A_ub=A_ineq, b_ub=B_ineq, method='interior-point')
# # res_no_bounds = linprog(c, A_ub=A_ineq, b_ub=B_ineq, A_eq=A_eq, b_eq=B_eq, method='interior-point')
# print(res_no_bounds)

print('Demo: Use linear optimization tech to find the solutions')
print('3C2, we have 3 different combinations')
print('offset >= file_len; offset + count < file_len')
var_list = ['count', 'file_len', 'offset']
A_ineq = [[0, 1, -1], [1, -1, 1]]
B_ineq = [0, 0]
c = [1, 1, 1]
res_no_bounds = linprog(c, A_ub=A_ineq, b_ub=B_ineq, method='interior-point')
print(res_no_bounds)
print('--------------------')

print('offset >= file_len; offset + count >= file_len')
var_list = ['count, file_len', 'offset']
A_ineq = [[0, 1, -1], [-1, 1, -1]]
B_ineq = [0, 0]
c = [1, 1, 1]
res_no_bounds = linprog(c, A_ub=A_ineq, b_ub=B_ineq, method='interior-point')
print(res_no_bounds)
print('--------------------')

print('offset + count < file_len; offset + count >= file_len')
var_list = ['count, file_len', 'offset']
A_ineq = [[1, -1, 1], [-1, 1, -1]]
B_ineq = [0, 0]
c = [1, 1, 1]
res_no_bounds = linprog(c, A_ub=A_ineq, b_ub=B_ineq, method='interior-point')
print(res_no_bounds)
print('--------------------')