# @author: Haolin Yu
# nfs4mc ambiguity test script generator
# version 0.1.0

import sys
import ply.lex as lex
import ply.yacc as yacc

var_list = {}

# token names

tokens = (
    'IF', 'FI',
    'RIGHT_ARROW', 'DOUBLE_COLON',
    'SEMICOLON', 'LCURLY', 'RCURLY',
)

t_IF = r'if'
t_FI = r'fi'
t_RIGHT_ARROW = r'->'
t_DOUBLE_COLON = r'::'
t_SEMICOLON = r';'
t_LCURLY = r'{'
t_RCURLY = r'}'

# GRAMMAR for Parsing
def p_statement_if(p):
    ''''''

if __name__ == "__main__":
    # load the Spin model
    with open(sys.argv[1], 'r') as f:
        text = f.read().replace(' ', '').replace('\n', '#')
    lexer = lex.lex()
    parser = yacc.yacc()
    try:
        with open(sys.argv[1], 'r') as f:
            data = f.read().replace('\n', '')
            lex.input(data)
            while True:
                token = lex.token()
                if not token: break
            result = parser.parse(data)
    except(FileNotFoundError):
        print("File not found.\nSBML exits...")