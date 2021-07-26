# @author: Haolin Yu
# nfs4mc ambiguity test script generator
# version 0.1.4

import sys
import re
import os
import glob

script_head = '''import random as rd

def getRandom():
    return rd.randrange(10000)

record = {}

if __name__ == "__main__":
    for i in range(10000):
        if_count = 0
        cond_set = []
        var_set = []
        value_set = []

'''

script_tail = '''
    for key in record.keys():
        print('--------------')
        print('condition:')
        print(key)
        r = record[key]
        print('vars:')
        print(r[0])
        print('values:')
        print(r[1])
    print('--------------')
    
'''

whole_var_list = []
whole_condition_list = []
tab = '    '

if __name__ == "__main__":
    # remove all test scripts generated last time
    print('Removing test scripts generated last time.')
    files = glob.glob('test_scripts/*')
    for f in files:
        os.remove(f)
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
    # extract if-fi statements from the model
    if_pattern = r'\bif.*?fi\b'
    if_regex = re.compile(if_pattern)
    if_statements = re.findall(if_regex, text)
    # extract conditions from the model
    condition_pattern = r'::\(.*?\)->'
    condition_regex = re.compile(condition_pattern)
    for statment in if_statements:
        # store each condition seperately
        condition_list = []
        # store each if-fi statment seperately
        var_list = []
        conditions = re.findall(condition_regex, statment)
        # extract variables from the model
        var_pattern = r'(?!\bif\b|\belse\b|\bfi\b|\bskip\b)([a-zA-Z][a-zA-Z0-9_]*)'
        var_regex = re.compile(var_pattern)
        for condition in conditions:
            condition_list.append(condition.replace('::', '').replace('->', ''))
            variables = re.findall(var_regex, condition)
            # add variables to the var list, keep only one copy of each variable
            for var in variables:
                if var not in var_list:
                    var_list.append(var)
        whole_var_list.append(var_list)
        whole_condition_list.append(condition_list)
    # generate test scripts
    print('Found %d if-fi statements' % (len(whole_condition_list)))
    # remove empty list
    print('Removing illegal cases...')
    whole_condition_list = [x for x in whole_condition_list if x != []]
    whole_var_list = [x for x in whole_var_list if x != []]
    print('Get %d after removal' % (len(whole_condition_list)))
    print('Generating scripts...')
    for size in range(len(whole_condition_list)):
        condition_list = whole_condition_list[size]
        var_list = whole_var_list[size]
        # remove redundant var
        var_set = set(var_list)
        script = script_head
        assign_random_value_text = ''
        if_statement_text = ''
        for var in var_set:
            assign_random_value_text += 2*tab + var + ' = ' + 'getRandom()\n'
            assign_random_value_text += 2*tab + 'var_set.append(\'' + var +'\')\n'
            assign_random_value_text += 2*tab + 'value_set.append(' + var + ')\n'
        for condition in condition_list:
            if_statement_text += 2*tab + 'if' + condition + ':\n' + 3*tab + 'if_count += 1\n' \
                + 3*tab + 'cond_set.append(\'' + condition + '\')\n'
        # combine the text segements.
        script += assign_random_value_text + '\n' + if_statement_text
        # find if_count > 1, add the combination to the combination dict
        script += 2*tab + 'if(if_count > 1):\n' + 3*tab + 'record[tuple(cond_set)] = (tuple(var_set), tuple(value_set))\n'
        # fix && ||
        script = script.replace('&&', ' and ')
        script = script.replace('&', ' and ')
        script = script.replace('||', ' or ')
        script = script.replace('|', ' or ')
        script += script_tail
        script_name = 'test_scripts/test_script%d.py' %(size)
        with open(script_name, 'w') as sc:
            sc.write(script)
