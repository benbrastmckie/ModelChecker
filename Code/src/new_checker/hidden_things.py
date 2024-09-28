from z3 import (
    sat,
    Solver,
    BoolRef,
    simplify,
    Const,


)
import time

# this import will ultimately be a problem
from exposed_things import (Proposition,
                                )

from syntax import (prefix, AtomSort,
                    find_operator,
                    )

from old_semantics_helpers import (all_sentence_letters, 
                                   find_all_bits)

# B: these are (or should be) purely syntactic functions and so may be best to include as methods
# here or else in a syntax module
# from src.model_checker.model_definitions import find_subsentences
# from src.model_checker.semantics import all_sentence_letters

class OperatorCollection:
    def __init__(self, *input):
        self.operator_classes_dict = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_classes_dict

    def items(self):
        yield from self.operator_classes_dict.items()

    def add_operator(self, input):
        '''
        input is either an operator class (of type 'type') or a list of operator classes
        '''
        if isinstance(input, list) or isinstance(input, tuple) or isinstance(input, set):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            self.operator_classes_dict[input.name] = input
            # line above is why name attributes were moved out of __init__ for operator classes
            # above we are accessing a class's attribute without making an instance of the class
    
    def __getitem__(self, value):
        return self.operator_classes_dict[value]
        # right now this method isn't needed, but I added it in case

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
            operator_collection
        ):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.operators = {op_name:op_class(semantics) for (op_name, op_class) in operator_collection.items()}
        self.max_time = max_time
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint

        self.prefix_premises = [prefix(prem, self) for prem in infix_premises]
        self.prefix_conclusions = [prefix(con, self) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = self.find_subsentences(prefix_sentences)
        self.all_sentence_letters = self.find_sentence_letters(prefix_sentences)
        
        # self.function_constraints = semantics.function_constraints
        self.frame_constraints = semantics.frame_constraints
        self.model_constraints = []
        for sl in self.all_sentence_letters:
            self.model_constraints.extend(semantics.find_model_constraints(sl))
        self.premise_constraints = [
            semantics.premise_behavior(prem, semantics.main_world)
            for prem in self.prefix_premises
        ]
        self.conclusion_constraints = [
            semantics.conclusion_behavior(conc, semantics.main_world)
            for conc in self.prefix_conclusions
        ]
        self.all_constraints = (
                                # self.function_constraints + 
                                self.frame_constraints + 
                                self.model_constraints + 
                                self.premise_constraints + self.conclusion_constraints)
        print([type(i) for i in self.all_constraints])

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
        print(sentence_letters)
        print([type(sentence_letter) for sentence_letter in sentence_letters])
        return list(sentence_letters)

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

        print(tokens)
        token = tokens.pop(0) # Get the next token
        
        # Handle binary operator case (indicated by parentheses)
        if token == '(':  
            # Ensure that the closing parenthesis is present
            final = tokens.pop()  # Remove the closing parenthesis
            if final != ')':
                raise SyntaxError(f"The sentence {tokens} is missing closing parenthesis.")

            # Extract operator and arguments
            operator, left, right = self.left_op_right(tokens)
            print(operator, left, right)
            left_arg = self.parse_expression(left)  # Parse the left argument
            right_arg = self.parse_expression(right)  # Parse the right argument
            return [find_operator(operator, self), left_arg, right_arg]

        # M: made a slight change here to match up with old prefix notation syntax
        # Handle atomic sentences and zero-place extremal operators
        if token.isalnum():
            return [Const(token, AtomSort)]
        elif token in {'\\top', '\\bot'}:
            return [find_operator(token, self)]

        # Handle unary operators which don't need parentheses
        return [find_operator(token, self), self.parse_expression(tokens)]  # Recursively parse the argument for unary operators

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
                print("FOUND MODEL")
                return self, False, True, solver.model(), model_runtime
            if solver.reason_unknown() == "timeout":
                return True, False, None, model_runtime
            print("NO MODEL")
            return self, False, False, solver.unsat_core(), model_runtime
        except RuntimeError as e:
            # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return self, True, False, None, None

    def __str__(self):
        '''useful for using model-checker in a python file'''
        return f'ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions}'

class ModelStructure:
    def __init__(self, model_setup, timeout, z3_model_status, z3_model, z3_model_runtime):
        semantics = model_setup.semantics
        self.model_setup = model_setup
        self.z3_model = z3_model
        self.model_status = z3_model_status
        self.model_runtime = z3_model_runtime

        self.N = model_setup.semantics.N
        self.all_subsentences = model_setup.all_subsentences
        prefix_sentences = model_setup.prefix_premises + model_setup.prefix_conclusions
        print("\n\n")
        print(prefix_sentences)
        print("\n\n")
        self.sentence_letters = all_sentence_letters(prefix_sentences)

        self.all_bits = find_all_bits(self.N) # M: can be kept
        self.poss_bits = [bit for bit in self.all_bits if self.z3_model.evaluate(semantics.possible(bit))]
        self.world_bits = [bit for bit in self.poss_bits if self.z3_model.evaluate(semantics.is_world(bit))]
        self.main_world = self.z3_model[semantics.main_world]
        self.all_propositions = set() # these will be automatically added when the two below are called
        # right now it adds all subpropositions
        self.premise_propositions = [Proposition(prefix_sent, self)
                                    for prefix_sent in model_setup.prefix_premises]
        self.conclusion_propositions = [Proposition(prefix_sent, self)
                                    for prefix_sent in model_setup.prefix_conclusions]


    def evaluate(self, z3_expr):
        '''
        This will get rid of need for all the bit_ functions. 
        However, it does not get rid of e.g. find_compatible_parts.
        '''
        if isinstance(z3_expr, BoolRef):
            return bool(simplify(z3_expr))
        return simplify(z3_expr)
    
    # for printing methods: 
    # we can keep the beginning—printing out the premises, conclusions, and whether there
    # is an N-model of the premises and conclusions. 
    # the state space also seems easy to print, but we need to add what a user wants printed
    # and annotated (eg currently ony possible states are printed, and world states are annotated).
    # The evaluation world can also be included (it's just the main world, which there always
    # is (...?))
    # B: printing premises, conclusions, state space, and evaluation world can be fixed for all
    # users, though this will change slightly depend on whether the user wants impossible states
    # to be printed. so somewhere this will have to check what the settings are for this.

    # there needs to be a general formula for what an interpretation is.
        # looking at find_complex_proposition, it looks like we can employ a similar strategy
        # to the operators bouncing back and forth with the semantics, except this time we
        # bounce back and forth with wherever the definition of a proposition is
    # B: yes, there will definitely also be some bouncing back and forth where really this is the
    # key to the print methods. my thought was that what happens in recursive_print will get
    # divided between operators as before so that users can introduce this alongside the operators
    # semantics clause, etc.
    
    # Right now we explicitly save the extension of some functions (verify, falsify—in atomic_props_dict). 
    # it would be nice if we could choose not to. 
    # B: I agree

    # or if we made everything a Z3 function? That way we can just do z3model.evalute(*) on all
    # functions. 
    # B: not sure I understand this suggestion

    # to be honest the entirety of the state space is user-dependent. The only thing that we could
    # do is maybe save the extensions of all the functions. Tbh, not that much for small values of N.
    # you could then save all those extensions and when you're evaluating you'd just need to check
    # if a specific set of values is in the extension of the given function. Now the problem is,
    # how do we know for a generic case what the name of a given function is? Maybe it is better
    # instead to rely on a method that is like the current evaluate one but for functions. 
        # as a concrete example take find_compatible_parts in model_definitions rn. Right now,
        # to find what bits are compatible with a world, you check if some things are in the
        # extension of other things. With the new implementation, you would simply do
        # z3_model.evaluate(compatible_parts)
    # B: this is interesting and worth discussing
    
    # how about you just don't worry about all that stuff? Like, focus on the extensional case.
    # all that crap only matters for the later stuff anyways.
    # B: good to anticipate what will be needed later on to save trouble then
    # M: that is true, sorry this comment was meant to myself and i probably should have worded
    # better anyways lol




