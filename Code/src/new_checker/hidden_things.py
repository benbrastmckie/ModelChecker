from z3 import (
    sat,
    Solver,
)
import time

# B: these are (or should be) purely syntactic functions and so may be best to include as methods
# here or else in a syntax module
# from src.model_checker.model_definitions import find_subsentences
# from src.model_checker.semantics import all_sentence_letters

class ModelSetup:

    def __init__(
            self,
            infix_premises,
            infix_conclusions,
            semantics,
            max_time,
            contingent,
            non_null,
            disjoint,
            operators_list
        ):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.operators = operators_list
        self.max_time = max_time
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint

        self.prefix_premises = [self.prefix(prem) for prem in infix_premises]
        self.prefix_conclusions = [self.prefix(con) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = self.find_subsentences(prefix_sentences)
        self.all_sentence_letters = self.find_sentence_letters(prefix_sentences)
        
        self.frame_constraints = semantics.frame_constraints
        self.model_constraints = [
            semantics.find_model_constraints(sl)
            for sl in self.all_sentence_letters
        ]
        self.premise_constraints = [
            semantics.premise_behavior(prem, semantics.w)
            for prem in self.prefix_premises
        ]
        self.conclusion_constraints = [
            semantics.conclusion_behavior(conc, semantics.w)
            for conc in self.prefix_conclusions
        ]
        self.all_constraints = (self.frame_constraints + self.model_constraints + 
                                self.premise_constraints + self.conclusion_constraints)

    # B: is there any reason not to include all helper functions as methods of the class?
    # if so, we can move these to the syntax file which currently is not imported.

    def sentence_letters_in_compound(self, prefix_input_sentence):
        """finds all the sentence letters in ONE input sentence. returns a list. WILL HAVE REPEATS
        returns a list of AtomSorts. CRUCIAL: IN THAT SENSE DOES NOT FOLLOW SYNTAX OF PREFIX SENTS.
        But that's ok, just relevant to know
        used in find_sentence_letters
        """
        if len(prefix_input_sentence) == 1:  # base case: atomic sentence
            return [prefix_input_sentence[0]] # redundant but conceptually clear
        return_list = []
        for part in prefix_input_sentence[1:]:
            return_list.extend(self.sentence_letters_in_compound(part))
        return return_list

    def find_sentence_letters(self, prefix_sentences):
        """finds all the sentence letters in a list of input sentences, in prefix form.
        returns as a list of AtomSorts with no repeats (sorted for consistency)
        used in find_all_constraints (feeds into find_prop_constraints) and StateSpace __init__"""
        sentence_letters = set()
        for prefix_input in prefix_sentences:
            sentence_letters_in_input = self.sentence_letters_in_compound(prefix_input)
            for sentence_letter in sentence_letters_in_input:
                sentence_letters.add(sentence_letter)
        return sorted(sentence_letters)

    def repeats_removed(self, sentences):
        '''takes a list and removes the repeats in it.
        used in find_all_constraints'''
        seen = []
        for obj in sentences:
            if obj not in seen:
                seen.append(obj)
        return seen

    def subsentences_of(self, prefix_sentence):
        '''finds all the subsentence of a prefix sentence
        returns these as a set
        used in find_extensional_subsentences'''
        progress = []
        progress.append(prefix_sentence)
        if len(prefix_sentence) == 2:
            sub_sentsentences = self.subsentences_of(prefix_sentence[1])
            return progress + sub_sentsentences
        if len(prefix_sentence) == 3:
            left_subsentences = self.subsentences_of(prefix_sentence[1])
            right_subsentences = self.subsentences_of(prefix_sentence[2])
            all_subsentences = left_subsentences + right_subsentences + progress
            return self.repeats_removed(all_subsentences)
        return progress

    def find_subsentences(self, prefix_sentences):
        """take a set of prefix sentences and returns a set of all subsentences"""
        all_subsentences = []
        for prefix_sent in prefix_sentences:
            all_prefix_subs = self.subsentences_of(prefix_sent)
            all_subsentences.extend(all_prefix_subs)
        return self.repeats_removed(all_subsentences)

    def left_op_right(self, tokens):
        """Divides whatever is inside a pair of parentheses into the left argument,
        right argument, and the operator."""
        
        tokens = tokens[:]
        count = 0  # To track nested parentheses
        left = []
        
        while tokens:
            token = tokens.pop(0)
            
            if token == '(':
                count += 1
                left.append(token)
                continue
            if token == ')':
                count -= 1
                left.append(token)
                if count < 0:
                    raise ValueError("Unbalanced parentheses")
                continue
            if count > 0:  # Inside parentheses, add to the left argument
                left.append(token)
                continue
            
            # Handle sentence letters and the zero-place extremal operators
            if token.isalnum() or token in {'\\top', '\\bot'}:
                left.append(token)
                if not tokens:
                    raise ValueError(f"Expected an operator following {token}")
                operator = tokens.pop(0)
                if not tokens:
                    raise ValueError(f"Expected an argument after the operator {operator}")
                right = tokens  # The remaining tokens are the right argument
                return operator, left, right
            
            # Otherwise, assume token is an operator and handle binary expression
            operator = token
            right = tokens
            return operator, left, right

        raise ValueError("Invalid expression or unmatched parentheses")

    def parse_expression(self, tokens):
        """Parses a list of tokens representing a propositional expression and returns
        the expression in prefix notation."""
        
        if not isinstance(tokens, list):
            # B: should this go here instead?
            # return [Const(token, AtomSort)]
            return tokens

        token = tokens.pop(0) # Get the next token
        
        # Handle binary operator case (indicated by parentheses)
        if token == '(':  
            # Ensure that the closing parenthesis is present
            final = tokens.pop()  # Remove the closing parenthesis
            if final != ')':
                raise SyntaxError(f"The sentence {tokens} is missing closing parenthesis.")

            # Extract operator and arguments
            operator, left, right = self.left_op_right(tokens)
            left_arg = self.parse_expression(left)  # Parse the left argument
            right_arg = self.parse_expression(right)  # Parse the right argument
            return [operator, left_arg, right_arg]

        # Handle atomic sentences and zero-place extremal operators
        if token.isalnum() or token in {'\\top', '\\bot'}:
            return token  # Return atomic sentence

        # Handle unary operators which don't need parentheses
        return [token, self.parse_expression(tokens)]  # Recursively parse the argument for unary operators

    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace('(', ' ( ').replace(')', ' ) ').split()
        return self.parse_expression(tokens)

    def infix(self, prefix_sent):
        """takes a sentence in prefix notation and translates it to infix notation"""
        if len(prefix_sent) == 1:
            return str(prefix_sent[0])
        op = prefix_sent[0]
        if len(prefix_sent) == 2:
            return f"{op} {self.infix(prefix_sent[1])}"
        left_expr = prefix_sent[1]
        right_expr = prefix_sent[2]
        return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"


    def solve(self):
        solver = Solver()
        solver.add(self.all_constraints)
        solver.set("timeout", int(self.max_time * 1000)) # in milliseconds
        try:
            model_start = time.time()  # start benchmark timer
            result = solver.check()
            model_end = time.time()
            model_runtime = round(model_end - model_start, 4)
            if result == sat:
                return False, True, solver.model(), model_runtime
            if solver.reason_unknown() == "timeout":
                return True, False, None, model_runtime
            return False, False, solver.unsat_core(), model_runtime
        except RuntimeError as e:
            # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, False, None, None

    def __str__(self):
        '''useful for using model-checker in a python file'''
        return f'ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions}'

class ModelStructure:
    pass
