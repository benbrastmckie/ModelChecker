import doctest
from z3 import *
from definitions import *
'''
OVERVIEW
All sentence letters are capital letters.
All commands must be strictly in lowercase; they can have double backslash, a forward slash, or nothing (nothing so long as the first letter is lowercase).
The unary operators are defined in a separate set for clarity in the code.
'''


# sentence_stuff = {'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','Z','W','Y','Z'}
# operator_stuff = {'\\','/','a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'}
unary_operators = {'\\neg', '/neg', 'neg'}
def tokenize(str_exp):
    """
    >>> tokenize("(A /wedge (B /vee C))")
    ['(', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize("(/neg A /wedge (B /vee C))")
    ['(', '/neg', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize('((A /operator ((C /operator D) /operator F)) /operator E)')
    ['(', '(', 'A', '/operator', '(', '(', 'C', '/operator', 'D', ')', '/operator', 'F', ')', ')', '/operator', 'E', ')']

    >>> tokenize('/neg A')
    ['/neg', 'A']
    """
    split_str = str_exp.split()  # small issue here with doctest cases and backslashes

    def tokenize_improved_input(split_str):
        if len(split_str) == 1:
            # split_str is a list with one elem (has been called recursively or is last elem)
            base_string = split_str[0]  # base_string is a string
            if "(" in base_string:  # left parentheses in base_string
                tokenized_l = ["("]
                tokenized_l.extend(tokenize_improved_input([base_string[1:]]))
                return tokenized_l
            elif ")" in base_string:  # right parentheses in base_string
                tokenized_l = tokenize_improved_input([base_string[:-1]])
                tokenized_l.append(")")
                return tokenized_l
            return split_str # else case: covers sentence letter case and latex operator case
        tokenized_l = tokenize_improved_input([split_str[0]])
        tokenized_l.extend(tokenize_improved_input(split_str[1:]))
        return tokenized_l

    return tokenize_improved_input(split_str)


def binary_comp(tokenized_expression):
    """
    finds complexity, defined by number of operators, in a tokenized_expression.
    In reality, it counts left parentheses. But it can easily be shown by induction
    that this number and that of operators is equal.

    >>> binary_comp(tokenize('(A /wedge (B /vee C))'))
    2

    >>> binary_comp(tokenize('/neg (A /wedge (B /vee C))'))
    2
    """
    return len([char for char in tokenized_expression if char == "("])


def main_op_index(tokenized_expression):
    """
    given an expression with complexity > 0, finds the index of the main operator.
    Starting after the expression's initial parenthesis, the point
    at which the number of left parentheses equals the number of right is the
    first expression (as it is closed there)
    ASSUMES FIRST CHAR IS LEFT PARENTH. IF NOT CASE, EQN PROLLY SHOULDN'T BE HERE
    >>> main_op_index(tokenize('(A /wedge (B /vee C))'))
    2

    >>> main_op_index(tokenize('((A /vee B) /wedge C)'))
    6

    >>> main_op_index(tokenize('((A /operator ((C /operator D) /operator F)) /operator E)'))
    14

    >>> main_op_index(tokenize('((/neg A /vee B) /wedge C)'))
    7

    >>> main_op_index(tokenize('((A \\op (B \\op C)) \\op (D \\op E))'))
    10
    """
    left_parentheses = 0
    right_parentheses = 0
    if tokenized_expression[0] != '(':
        raise ValueError(tokenized_expression, 'this case probably shouldnt be being raised by this function')
    for i, token in enumerate(tokenized_expression[1:]): # [1:] to exclude the left parenth (thus complexity) of the main operator
        if token == "(":
            left_parentheses += 1
        elif token == ")":
            right_parentheses += 1
        elif token in unary_operators: # ignore this case since we care about binary complexity
            continue
        if left_parentheses == right_parentheses:
            return i + 2 # +1 bc list is [1:] and we want original index, and +1 bc it's next elem where the main op is


def parse(tokens):
    """
    >>> parse(tokenize("(A /wedge (B /lor C))"))
    ['/wedge', ['A'], ['/lor', ['B'], ['C']]]

    >>> parse(tokenize("/neg A"))
    ['/neg', ['A']]
    
    >>> parse(tokenize("A")) # note: atomic sentence should return a single element list
    ['A']

    >>> parse(tokenize('((A /op (B /op C)) /op (D /op E))'))
    ['/op', ['/op', ['A'], ['/op', ['B'], ['C']]], ['/op', ['D'], ['E']]]
    """
    bin_comp_tokens = binary_comp(tokens)
    if tokens[0] in unary_operators:
        return [tokens[0], parse(tokens[1:])]
    if bin_comp_tokens == 0:
        token = tokens[0]
        return [Const(token, AtomSort)]
    main_operator_index = main_op_index(tokens)
    op_str = tokens[main_operator_index]  # determines how far the operation is
    left_expression = tokens[1 : main_operator_index]  # start 1 (exclude first parenthesis), stop at same pos of above (exclusive)
    right_expression = tokens[main_operator_index + 1 : -1]  # from pos of op plus 1 to the penultimate, thus excluding the last parentheses, which belongs to the main expression
    return [op_str, parse(left_expression), parse(right_expression)]


def Prefix(A):
    """takes a sentence in Infix notation and translates it to Prefix notation"""
    return parse(tokenize(A))


def Infix(A):
    """takes a sentence in Prefix notation and translates it to infix notation"""
    pass


# doctest.testmod()
# print(tokenize("(A \\wedge (B \\vee C))")) # the doctests fail, but this works. Need to do double backslash for abfnrtv.
# print(Prefix("(A \\wedge (B \\vee \\neg C))")) # ['\\wedge', ['A'], ['\\vee', ['B'], ['\\neg', ['C']]]]
# print(Prefix("A")) 
# print(Prefix('((A \\op (B \\op C)) \\op (D \\op E))')) # ['\\op', ['\\op', ['A'], ['\\op', ['B'], ['C']]], ['\\op', ['D'], ['E']]]

def sentence_letters_in_compound(input_sentence):
    '''finds all the sentence letters in ONE input sentence. returns a list. WILL HAVE REPEATS'''
    if len(input_sentence) == 1: # base case: atomic sentence
        return input_sentence
    # recursive case: complex sentence as input. Should have max 3 elems (binary operator) in this list, but figured eh why not not check, above code should ensure that never happens
    return_list = []
    for part in input_sentence[1:]:
        return_list.extend(sentence_letters_in_compound(part))
    return return_list

def all_sentence_letters(input_sentences):
    '''finds all the sentence letters in a list of input sentences. returns as a list with no repeats (sorted for consistency)'''
    sentence_letters = set()
    for input in input_sentences:
        sentence_letters_in_input = sentence_letters_in_compound(input)
        for sentence_letter in sentence_letters_in_input:
            sentence_letters.add(sentence_letter)
    return list(sentence_letters) # sort just to make every output the same, given sets aren't hashable

sentences = [Prefix("(A \\wedge (B \\vee \\neg C))"), Prefix("A"), Prefix('((A \\op (B \\op Z)) \\op (D \\op E))')]
# print(all_sentence_letters(sentences)) # correctly prints ['A', 'B', 'C', 'D', 'E', 'Z']
# print(Prefix("\\neg (A \\boxright B)"))
print(all_sentence_letters([Prefix("\\neg (A \\boxright B)")]))