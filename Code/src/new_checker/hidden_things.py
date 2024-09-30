from z3 import (
    sat,
    Solver,
    BoolRef,
    simplify,
    Const,
)

import time

from syntax import (prefix, AtomSort,
                    )

from old_semantics_helpers import (all_sentence_letters, 
                                   find_all_bits,
                                   bitvec_to_substates,
                                   int_to_binary,

                                   )

import sys

class Operator:
    name = None
    arity = None

    def __init__(self, semantics):
        self.semantics = semantics

    def __str__(self):
        return self.name if self.name else "Unnamed Operator"
    
    def __repr__(self):
        return self.name if self.name else "Unnamed Operator"

    def __eq__(self, other):
        if isinstance(other, Operator):
            return self.name == other.name and self.arity == other.arity
        return False

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
            operator_collection,
            proposition_class,
            max_time=1000,
            contingent=False,
            non_null=True,
            disjoint=False,
        ):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.operators = {op_name:op_class(semantics) for (op_name, op_class) in operator_collection.items()}
        self.proposition_class = proposition_class
        self.max_time = max_time
        self.contingent = contingent
        self.non_null = non_null
        self.disjoint = disjoint

        self.prefix_premises = [prefix(prem, self) for prem in infix_premises]
        self.prefix_conclusions = [prefix(con, self) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = self.find_subsentences(prefix_sentences)
        self.all_sentence_letters = self.find_sentence_letters(prefix_sentences)
        
        self.frame_constraints = semantics.frame_constraints
        self.model_constraints = []
        for sl in self.all_sentence_letters:
            self.model_constraints.extend(proposition_class.proposition_constraints(sl, self))
        self.premise_constraints = [
            semantics.premise_behavior(prem, semantics.main_world)
            for prem in self.prefix_premises
        ]
        self.conclusion_constraints = [
            semantics.conclusion_behavior(conc, semantics.main_world)
            for conc in self.prefix_conclusions
        ]
        self.all_constraints = (
                                self.frame_constraints + 
                                self.model_constraints + 
                                self.premise_constraints + self.conclusion_constraints)
        
    def print_enumerate(self, output=sys.__stdout__):
        """prints the premises and conclusions with numbers"""
        infix_premises = self.infix_premises
        infix_conclusions = self.infix_conclusions
        start_con_num = len(infix_premises) + 1
        if self.infix_premises:
            if len(self.infix_premises) < 2:
                print("Premise:", file=output)
            else:
                print("Premises:", file=output)
            for index, sent in enumerate(self.infix_premises, start=1):
                print(f"{index}. {sent}", file=output)
        if infix_conclusions:
            if len(infix_conclusions) < 2:
                print("\nConclusion:", file=output)
            else:
                print("\nConclusions:", file=output)
            for index, sent in enumerate(infix_conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)

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
            return [self.operators[operator], left_arg, right_arg]

        # M: made a slight change here to match up with old prefix notation syntax
        # Handle atomic sentences and zero-place extremal operators
        if token.isalnum():
            return [Const(token, AtomSort)]
        elif token in {'\\top', '\\bot'}:
            return [self.operators[token]]

        # Handle unary operators which don't need parentheses
        return [self.operators[token], self.parse_expression(tokens)]  # Recursively parse the argument for unary operators

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
        self.sentence_letters = all_sentence_letters(prefix_sentences)

        self.all_bits = find_all_bits(self.N)
        self.poss_bits = [bit for bit in self.all_bits if self.z3_model.evaluate(semantics.possible(bit))]
        self.world_bits = [bit for bit in self.poss_bits if self.z3_model.evaluate(semantics.is_world(bit))]
        self.main_world = self.z3_model[semantics.main_world]
        self.all_propositions = set() # this will be automatically populated when the two below are called
                                      # right now all subpropositions are added
        self.premise_propositions = [model_setup.proposition_class(prefix_sent, self)
                                    for prefix_sent in model_setup.prefix_premises]
        self.conclusion_propositions = [model_setup.proposition_class(prefix_sent, self)
                                    for prefix_sent in model_setup.prefix_conclusions]

    # this is not used right now but may be later
    def evaluate(self, z3_expr):
        '''
        This will get rid of need for all the bit_ functions. 
        However, it does not get rid of e.g. find_compatible_parts.
        '''
        if isinstance(z3_expr, BoolRef):
            return bool(simplify(z3_expr))
        return simplify(z3_expr)
    
    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        N = self.model_setup.semantics.N
        sentence_letters = self.sentence_letters
        main_world = self.main_world
        print(
            f"\nThe evaluation world is: {bitvec_to_substates(main_world, N)}",
            file=output,
        )
        # true_in_eval = set()
        # for sent in sentence_letters:
        #     for bit in self.all_bits:
        #         ver_bool = self.model_setup.verify(bit, self.z3_model[sent])
        #         part_bool = bit_part(bit, main_world)
        #         if bool(self.z3_model.evaluate(ver_bool) and part_bool):
        #             true_in_eval.add(sent)
        #             break  # exits the first for loop
        # false_in_eval = {R for R in sentence_letters if not R in true_in_eval}
        # GREEN = '\033[32m'
        # RED = '\033[31m'
        # # YELLOW = '\033[33m'
        # RESET = '\033[0m'
        # world_state = bitvec_to_substates(main_world, N)
        # if true_in_eval:
        #     true_eval_list = sorted([str(sent) for sent in true_in_eval])
        #     true_eval_string = ", ".join(true_eval_list)
        #     print(
        #         f"  {GREEN}{true_eval_string}  (True in {world_state}){RESET}",
        #         file=output,
        #     )
        # if false_in_eval:
        #     false_eval_list = sorted([str(sent) for sent in false_in_eval])
        #     false_eval_string = ", ".join(false_eval_list)
        #     print(
        #         f"  {RED}{false_eval_string}  (False in {world_state}){RESET}",
        #         file=output,
        #     )
        # print(file=output)

    # def print_to(self, print_constraints_bool, print_impossible, output=sys.__stdout__):
    #     """append all elements of the model to the file provided"""
    #     self.print_all(print_impossible, output)
    #     structure = self.model_setup
    #     setup = self.model_setup
    #     if print_constraints_bool:
    #         structure.print_constraints(setup.frame_constraints, 'FRAME', output)
    #         structure.print_constraints(setup.prop_constraints, 'PROPOSITION', output)
    #         structure.print_constraints(setup.premise_constraints, 'PREMISE', output)
    #         structure.print_constraints(setup.conclusion_constraints, 'CONCLUSION', output)
    #     print(f"Run time: {self.model_runtime} seconds\n", file=output)

    # def save_to(self, cons_include, print_impossible, output):
    #     """append all elements of the model to the file provided"""
    #     constraints = self.model_setup.constraints
    #     self.print_all(print_impossible, output)
    #     self.model_setup.build_test_file(output)
    #     if cons_include:
    #         print("# Satisfiable constraints", file=output)
    #         # TODO: print constraint objects, not constraint strings
    #         print(f"all_constraints = {constraints}", file=output)

    def print_states(self, print_impossible=False, output=sys.__stdout__):
        """print all fusions of atomic states in the model
        print_impossible is a boolean for whether to print impossible states or not
        first print function in print.py"""
        N = self.model_setup.semantics.N
        print("\nState Space:", file=output)  # Print states
        YELLOW = '\033[33m'
        BLUE = '\033[34m'
        MAGENTA = '\033[35m'
        CYAN = '\033[36m'
        WHITE = '\033[37m'
        RESET = '\033[0m'
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, N)
            bin_rep = (
                bit.sexpr()
                if N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), N)
            )
            if bit == 0:
                print(f"  {WHITE}{bin_rep} = {YELLOW}{state}{RESET}", file=output)
                continue
            if bit in self.world_bits:
                print(f"  {WHITE}{bin_rep} = {BLUE}{state} (world){RESET}", file=output)
                continue
            if bit in self.poss_bits:
                print(f"  {WHITE}{bin_rep} = {CYAN}{state}{RESET}", file=output)
                continue
            if print_impossible:
                print(f"  {WHITE}{bin_rep} = {MAGENTA}{state} (impossible){RESET}", file=output)

    def print_all(self, print_impossible=False, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        N = self.model_setup.semantics.N
        print(f"\nThere is a {N}-model of:\n", file=output)
        self.model_setup.print_enumerate(output)
        self.print_states(print_impossible, output)
        self.print_evaluation(output)
        # self.print_inputs_recursively(print_impossible, output) # missing

    
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
    # M: yes. on a simlar note I was wondering—is it fair to assume that all models will have
    # possible states, and all models will have a definition for worlds?

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
    # M: never mind, this was fixed

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
    # M: I tried this, it didn't work because it actually takes a lot of computational power.
    # (and I think we actually discussed and discarded a similar strategy back in February
    # when things were getting started)
    # M: It turns out that even for small values of N saving the extensions of function is a lot,
    # since there are a couple functions that would take 3 inputs (e.g. is_alternative), which has
    # inputs in R^3, meaning, with e.g. N=7 there are (2^7)^3 = 2 million different input combos. 
    # Even worse, in that strategy you'd create a constraint for every single combination of
    # bits in the space R^n for n the number of arguments taken by the function. 
    # so for N=7 and a 3-place predicate, you'd create a constraint that is itself a conjunction of
    # 2 million constraints—in tests Z3 was taking too long for that (I never saw it terminate)
    
    # how about you just don't worry about all that stuff? Like, focus on the extensional case.
    # all that crap only matters for the later stuff anyways.
    # B: good to anticipate what will be needed later on to save trouble then
    # M: that is true, sorry this comment was meant to myself and i probably should have worded
    # better anyways lol
    # M: I also have a better idea of how that would look—just before I was kind of lost




