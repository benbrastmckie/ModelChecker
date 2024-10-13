
from hidden_helpers import remove_repeats


class Sentence:
    """Class with an instance for each sentence."""

    def __init__(self, infix_sentence):
        self.name = infix_sentence
        # print("SENTENCE TEST INFIX", self.name)
        self.prefix_sentence = self.prefix(infix_sentence)
        # print("SENTENCE TEST PREFIX", self.prefix_sentence)
        letters, ops, subs, complexity = self.constituents_of(self.prefix_sentence)
        self.sentence_letters = letters
        self.operators = ops
        self.subsentences = subs
        self.complexity = complexity

    # def get_values(self):
    #     """Returns components of the Sentence instance as a dictionary."""
    #     return {
    #         'name': self.name,
    #         'prefix_sentence': self.prefix_sentence,
    #         'sentence_letters': self.sentence_letters,
    #         'operators': self.operators,
    #         'subsentences': self.subsentences,
    #         'complexity': self.complexity
    #     }
        
    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        return self.parse_expression(tokens)

    def balanced_parentheses(self, tokens):
        """Check if parentheses are balanced in the argument."""
        stack = []
        for token in tokens:
            if token == "(":
                stack.append(token)
            elif token == ")":
                if not stack:
                    return False
                stack.pop()
        return len(stack) == 0

    def op_left_right(self, tokens):
        """Divides whatever is inside a pair of parentheses into the left argument,
        right argument, and the operator."""

        def check_right(tokens, operator):
            if not tokens:
                raise ValueError(f"Expected an argument after the operator {operator}")
            if not self.balanced_parentheses(tokens):
                raise ValueError("Unbalanced parentheses")
            return tokens  # Remaining tokens are the right argument

        def cut_parentheses(left, tokens):
            count = 1  # To track nested parentheses
            while tokens:
                token = tokens.pop(0)
                if token == "(":
                    count += 1
                    left.append(token)
                elif token == ")":
                    count -= 1
                    left.append(token)
                elif count > 0:
                    left.append(token)
                elif not tokens:
                    raise ValueError(f"Extra parentheses in {tokens}.")
                else:
                    operator = token
                    right = check_right(tokens, operator)
                    return operator, left, right
            raise ValueError(f"The expression {tokens} is incomplete.")

        def process_operator(tokens):
            if tokens:
                return tokens.pop(0)
            raise ValueError("Operator missing after operand")
        
        def extract_arguments(tokens):
            """Extracts the left argument and right argument from tokens."""
            left = []
            while tokens:
                token = tokens.pop(0)
                if token == "(":
                    left.append(token)
                    return cut_parentheses(left, tokens)
                elif token.isalnum() or token in {"\\top", "\\bot"}:
                    left.append(token)
                    operator = process_operator(tokens)
                    right = check_right(tokens, operator)
                    return operator, left, right
                else:
                    left.append(token)
            raise ValueError("Invalid expression or unmatched parentheses")
        
        result = extract_arguments(tokens)
        if result is None:
            raise ValueError("Failed to extract arguments")
        return result

    def parse_expression(self, tokens):
        """Parses a list of tokens representing a propositional expression and returns
        the expression in prefix notation."""
        if not tokens:  # Check if tokens are empty before processing
            raise ValueError("Empty token list")
        token = tokens.pop(0)  # Get the next token
        if token == "(":  # Handle binary operator case (indicated by parentheses)
            closing_parentheses = tokens.pop()  # Remove the closing parenthesis
            if closing_parentheses != ")":
                raise SyntaxError(
                    f"The sentence {tokens} is missing a closing parenthesis."
                )
            operator, left, right = self.op_left_right(tokens)
            left_arg = self.parse_expression(left)  # Parse the left argument
            right_arg = self.parse_expression(right)  # Parse the right argument
            return [operator, left_arg, right_arg]
        if token.isalnum():  # Handle atomic sentences
            return [token]
        elif token in {"\\top", "\\bot"}:  # Handle extremal operators
            return [token]
        return [  # Unary operators
            token,
            self.parse_expression(tokens),
        ]

    # def remove_repeats(self, prefix_sentences):
    #     """Takes a list and removes the repeats in it.
    #     Used in find_all_constraints."""
    #     seen = [] # NOTE: sentences are unhashable so can't use set()
    #     for obj in prefix_sentences:
    #         if obj not in seen:
    #             seen.append(obj)
    #     return seen

    def constituents_of(self, prefix_sentence):
        """take a prefix sentence and return a set of subsentences"""
        sentence_letters = []
        operators = []
        subsentences = [prefix_sentence]
        complexity = 0
        if len(prefix_sentence) == 1:
            if '\\' in prefix_sentence[0]:
                operators.append(prefix_sentence)
                return sentence_letters, operators, subsentences, complexity
            if prefix_sentence[0].isalnum():
                # B: would it be better to have lists of length 1 here?
                sentence_letters.append(prefix_sentence[0])
                return sentence_letters, operators, subsentences, complexity
            raise ValueError(f"The sentence {prefix_sentence} is not well-formed.")
        # B: this is instead of above to exclude sentence letters; not sure if this is better
        # subsentences.append(prefix_sentence)
        main_operator = prefix_sentence[0]
        operators.append(main_operator)
        arguments = prefix_sentence[1:]
        complexity += 1
        for arg in arguments:
            arg_sent_lets, arg_ops, arg_subs, arg_comp = self.constituents_of(arg)
            sentence_letters.extend(arg_sent_lets)
            operators.extend(arg_ops)
            subsentences.extend(arg_subs)
            complexity += arg_comp
        sorted_sent_lets = sorted(remove_repeats(sentence_letters))
        sorted_ops = sorted(remove_repeats(operators))
        sorted_subs = sorted(remove_repeats(subsentences))
        return sorted_sent_lets, sorted_ops, sorted_subs, complexity

