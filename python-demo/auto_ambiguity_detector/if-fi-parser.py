# @author: Haolin Yu
# nfs4mc ambiguity test script generator
# version 0.1

import sys
import re

# it turns out that no parser needed, regex performes better.

# import ply.lex as lex
# import ply.yacc as yacc

# var_list = {}

# # token names

# tokens = (
#     'IF', 'FI',
#     'DOUBLE_COLON',
#     'RIGHT_ARROW',
#     'LPAREN', 'RPAREN',
#     'LCURLY', 'RCURLY',
#     'ADD', 'SUB', 'MULTI', 'DIV',
#     'LT', 'LET', 'EQ', 'NOTEQ', 'GET', 'GT',
# )

# t_IF = r'if'
# t_FI = r'fi'
# t_DOUBLE_COLON = r'::'
# t_LPAREN = r'('
# t_RPAREN = r')'
# t_LCURLY = r'{'
# t_RCURLY = r'}'
# t_ADD = r'\+'
# t_SUB = r'\-'
# t_MULTI = r'\*'
# t_DIV = r'/'
# t_LET = r'<='
# t_LT = r'<'
# t_EQ = r'=='
# t_NOTEQ = r'!='
# t_GET = r'>='
# t_GT = r'>'

# def t_REAL(t):
#     r'(((\d+\.\d*)|(\.\d+))([eE][+-]?\d+)?)|(\d+[eE][+-]?\d+)'
#     t.value = float(t.value)
#     return 
    
# def t_INT(t):
#     r'([1-9]\d*)|([0-9])'
#     t.value = int(t.value)
#     return t

# def t_VAR(t):
#     r'(?!if|fi)([a-zA-Z][a-zA-Z0-9_]*)'
#     t.value = str(t.value)
#     return t

# # GRAMMAR for Parsing

# def p_expr_value(p):
#     '''expr : INT
#         | REAL
#         | VAR'''
#     var_list.append

script_head = '''import random as rd
def getRandom():
    return rd.randrange(10000)
if __name__ == "__main__":
    for i in range(20):
        if_count = 0

'''

whole_var_list = []
whole_condition_list = []

if __name__ == "__main__":
    # load the Spin model
    with open('sample4.pml', 'r') as f:
        text = f.read().replace(' ', '').replace('\n', '#')
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
        var_pattern = r'(?!\bif\b|\belse\b|\bfi\b)([a-zA-Z][a-zA-Z0-9_]*)'
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
    print('Removing ilegal cases...')
    whole_condition_list = [x for x in whole_condition_list if x != []]
    whole_var_list = [x for x in whole_var_list if x != []]
    print('Get %d after removal' % (len(whole_condition_list)))
    print('Generating scripts...')
    for index in range(len(whole_condition_list)):
        condition_list = whole_condition_list[index]
        var_list = whole_var_list[index]
        # remove redundant var
        var_set = set(var_list)
        script = script_head
        assign_random_value_text = ''
        if_statement_text = ''
        message = '\'Ambiguity found with \''
        for var in var_set:
            assign_random_value_text += '\t' + var + ' = ' + 'getRandom()\n'
            message += ', \'%s\', %s' % (var, var)
        for condition in condition_list:
            if_statement_text += '\t' + 'if' + condition + ':\n\t    if_count += 1\n'
        # combine the text segements.
        script += assign_random_value_text + '\n' + if_statement_text
        script += '\tif(if_count > 1):\n\t    print(' + message +')\n' + '\t    break'
        # fix && ||
        script = script.replace('&&', ' and ')
        script = script.replace('&', ' and ')
        script = script.replace('||', ' or ')
        script = script.replace('|', ' or ')
        script_name = 'test_script%d.py' %(index)
        with open(script_name, 'w') as sc:
            sc.write(script)
