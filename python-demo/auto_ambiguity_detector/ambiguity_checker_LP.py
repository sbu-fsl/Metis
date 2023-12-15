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

# @author: Haolin
# nfs4mc ambiguity detector linear programming

import re
import sys
import pulp as pl
from promela_parser import PromelaParser

if __name__ == '__main__':
    # input check
    if len(sys.argv) != 2:
        print('No file path given. Exit...')
        exit(0)

    # load the Spin model
    try:
        with open(sys.argv[1], 'r') as f:
            text = f.read().replace(' ', '').replace('\n', '#')
    except(FileNotFoundError):
        print("File not found.\nExit...")

    log = open('report.txt', 'w')

    # extract if-fi statements from the model
    parser = PromelaParser(text)
    
    # add all LpVariable(s) in the file
    # use exec(), bad but don't know how to improve it
    var_list = parser.get_all_vars()
    for var in var_list:
        exec(var + ' = pl.LpVariable(' + '\'' + var + '\'' + ', lowBound=0, cat=\'Integer\')')

    # traverse all if-fi statements
    for i in range(parser.get_if_statements_len()):
        print('################', file=log)
        print('if-statements:\n' + parser.get_if_statements()[i], file=log)
        print('---------------------', file=log)
        # init the linear programming model
        model = pl.LpProblem('NFS' + str(i), pl.LpMinimize)
        # get conditions
        conditions = parser.get_if_conditions(i)
        num_conditions = len(conditions)
        # choose 2 from n
        for m in range(num_conditions):
            for n in range(m + 1, num_conditions):
                var_list1 = parser.get_if_conditions_vars(i, m)
                var_list2 = parser.get_if_conditions_vars(i, n)
                # only use unique ones
                var_list = set(var_list1 + var_list2)
                exec('model += ' + '+'.join(var_list) + ', \'Z\'')
                exec('model += ' + conditions[m])
                exec('model += ' + conditions[n])
                # solve the model
                model.solve()
                if(pl.LpStatus[model.status] == 'Optimal'):
                    print('Found a solution\n', file=log)
                    print('Conditions: ' + conditions[m] + ' & ' + conditions[n], file=log)
                    # Print out the solution
                    for variable in model.variables():
                        print ("{} = {}".format(variable.name, variable.varValue), file=log)
                    print('---------------------', file=log)
    log.close()
