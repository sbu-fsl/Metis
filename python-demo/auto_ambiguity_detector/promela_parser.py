# @author: Haolin
import re

class PromelaParser:
    def __init__(self, text):
        # the text to analyze
        self._text = self._preprocess_text(text)
        self._if_statements_list = self._preprocess_if()
        self._if_statements_num = len(self._if_statements_list)

    def _preprocess_text(self, text : str):
        # remove space ' ' and replace '\n' with #
        return text.replace(' ', '').replace('\n', '#')
    
    def _preprocess_if(self):
        # searching for if ... fi structure
        if_pattern = r'\bif.*?fi\b'
        if_regex = re.compile(if_pattern)
        if_statements = re.findall(if_regex, self._text)
        return if_statements

    def get_if_statements_len(self):
        return self._if_statements_num

    def get_if_statements(self):
        return self._if_statements_list

    def get_if_conditions(self, index : int):
        # searching for ::(condition) -> {statements} structure
        condition_pattern = r'::\(.*?\)->'
        condition_regex = re.compile(condition_pattern)
        if(index >= self._if_statements_num or index < 0):
            # wrong index
            return None
        statement = self._if_statements_list[index]
        conditions = re.findall(condition_regex, statement)
        return list(map(lambda c : c.replace('::', '').replace('->', ''), conditions))

    def get_if_conditions_vars(self, s_index : int, c_index: int):
        # only return the vars in a given condition
        # s_index -> the index of statements
        # c_index -> the index of conditions
        # extract variables from the model
        condition = self.get_if_conditions(s_index)[c_index]
        var_pattern = r'(?!\bif\b|\belse\b|\bfi\b|\bskip\b)([a-zA-Z][a-zA-Z0-9_]*)'
        var_regex = re.compile(var_pattern)
        return list(set(re.findall(var_regex, condition)))

    def get_if_statements_vars(self, index : int):
        conditions = self.get_if_conditions(index)
        var_list = []
        # extract variables from the model
        var_pattern = r'(?!\bif\b|\belse\b|\bfi\b|\bskip\b)([a-zA-Z][a-zA-Z0-9_]*)'
        var_regex = re.compile(var_pattern)
        for c in conditions:
            var = re.findall(var_regex, c)
            var_list = list(set(var_list + var))
        return var_list

    def get_all_vars(self):
        var_list = []
        for i in range(self._if_statements_num):
            var_list = list(set(var_list + self.get_if_statements_vars(i)))
        return var_list


if __name__ == '__main__':
    # test section
    with open('examples/example2.pml', 'r') as f:
        text = f.read()
    parser = PromelaParser(text)
    print(parser._if_statements_list)
    print(parser.get_if_conditions(0))
    print(parser.get_if_vars(0))

    print('------------')
    print(parser.get_if_conditions(1))
    print(parser.get_if_vars(1))