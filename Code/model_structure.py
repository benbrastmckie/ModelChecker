from definitions import *
from semantics import *
import time
from model_builder_definitions import *

class ModelStructure():
    '''self.premises is a list of prefix sentences
    self.conclusions is a list of prefix sentences
    self.input_sentences is the combination of self.premises and self.conclusions with the conclusions negated
    self.sentence letters is a list of atomic sentence letters (each of sort AtomSort)
    self.constraints is a list (?) of constraints
    everything else is initialized as None'''
    def __init__(self, input_premises, input_conclusions):
        self.premises = input_premises
        self.conclusions = input_conclusions
        self.input_sentences = combine(input_premises, input_conclusions)
        prefix_sentences, consts, sent_lets = find_all_constraints(self.input_sentences)
        self.sentence_letters = sent_lets
        self.constraints = consts
        # # initialize yet-undefined attributes
        # self.model = None
        # self.model_runtime = None
        # self.all_bits = None
        # self.poss_bits = None
        # self.world_bits = None
        # self.eval_world = None
        # self.atomic_props_dict = None
        
    def solve(self):
        '''solves the model, returns None
        self.model is the ModelRef object resulting from solving the model
        self.model_runtime is the runtime of the model as a float
        self.all_bits is a list of all bits (each of sort BitVecVal)
        self.poss_bits is a list of all possible bits
        self.world_bits is a lsit of all world bits
        self.eval_world is the eval world (as a BitVecVal)
        self.atomic_props_dict is a dictionary with keys AtomSorts and keys (V,F)
        '''
        model_start = time.time() # start benchmark timer
        solved_model = solve_constraints(self.constraints)
        self.model = solved_model
        model_end = time.time()
        model_total = round(model_end - model_start,4)
        self.model_runtime = model_total
        if self.model:
            self.all_bits = find_all_bits(N) # var accessed from outside (not bad, just noting)
            self.poss_bits = find_poss_bits(self.model,self.all_bits)
            self.world_bits = find_world_bits(self.poss_bits)
            self.eval_world = self.model[w] # var accessed from outside (not bad, just noting)

            self.atomic_props_dict = atomic_propositions_dict(self.all_bits, self.sentence_letters, self.model)
            # just missing the which-sentences-true-in-which-worlds

    def find_complex_proposition(self,complex_sentence):
        """sentence is a sentence in prefix notation
        For a given complex proposition, returns the verifiers and falsifiers of that proposition
        given a solved model"""
        if not self.atomic_props_dict: 
            raise ValueError("There is nothing in atomic_props_dict yet. Have you actually run the model?")
        if len(complex_sentence) == 1:
            sent = complex_sentence[0]
            return self.atomic_props_dict[sent]
        op = complex_sentence[0]
        if "neg" in op:
            return (self.atomic_props_dict[sent][1], self.atomic_props_dict[sent][0])
        Y = complex_sentence[1]
        Z = complex_sentence[2]
        Y_V = self.find_complex_proposition(Y)[0]
        Y_F = self.find_complex_proposition(Y)[1]
        Z_V = self.find_complex_proposition(Z)[0]
        Z_F = self.find_complex_proposition(Z)[1]
        if "wedge" in op:
            return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
        if "vee" in op:
            return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
        if "leftrightarrow" in op:
            return (product(coproduct(Y_F, Z_V), coproduct(Y_V, Z_F)), 
                    coproduct(product(Y_V, Z_F), product(Y_F, Z_V)))
        if "rightarrow" in op:
            return (coproduct(Y_F, Z_V), product(Y_V, Z_F))
        if "boxright" in op:
            raise ValueError("don't knowhow to handle boxright case yet")

    def print_states(self):
        """print all fusions of atomic states in the model
        first print function in print.py"""
        # print("\n(Possible) States:")  # Print states
        print("\nStates:")  # Print states
        for bit in self.all_bits:
            # test_state = BitVecVal(val, size) # was instead of bit
            state = bitvec_to_substates(bit)
            bin_rep = (
                bit.sexpr()
                if N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), N)
            )
            if bit in self.world_bits:
                print(f"  {bin_rep} = {state} (world)")
            elif self.model.evaluate(possible(bit)):
                print(f"  {bin_rep} = {state} (possible)")
            else:
                # print(f"  {bin_rep} = {state} (impossible)")
                continue

    def print_evaluation(self):
        """print the evaluation world and all sentences true/false in that world
        sentence letters is an iterable (a list, I think?)
        second print function in print.py"""
        print(f"\nThe evaluation world is {bitvec_to_substates(self.eval_world)}:")
        true_in_eval = set()
        for sent in self.sentence_letters:
            for bit in self.all_bits:
                if self.model.evaluate(verify(bit, self.model[sent])) and bit_part(bit, self.eval_world):
                    true_in_eval.add(sent)
                    break  # exits the first for loop
        false_in_eval = {R for R in self.sentence_letters if not R in true_in_eval}
        if true_in_eval:
            true_eval_list = sorted([str(sent) for sent in true_in_eval])
            true_eval_string = ", ".join(true_eval_list)
            print(f"  {true_eval_string}  (true in {bitvec_to_substates(self.eval_world)})")
        if false_in_eval:
            false_eval_list = sorted([str(sent) for sent in false_in_eval])
            false_eval_string = ", ".join(false_eval_list)
            print(f"  {false_eval_string}  (not true in {bitvec_to_substates(self.eval_world)})")
    
    # this is exactly the old thing. Needs to be changed once figure out how to store Proposition info somewhere
    # and in a useable way
    def print_props(self):
        print_propositions(self.model, self.sentence_letters)


# the Proposition class is unused because I haven't gotten to a couple of things that would enable it to be integrated, namely:
#     1. I can easily set everything in the input_sentences to be a propositon. How to make subsentences and un-negated conclusions?
#     2. I thought I had another issue but I can't think of it rn off the top of my head
class Proposition():
    def __init__(self, infix_expr, prefix_expr):
        self.prop_dict = dict()
        self.prop_dict['infix_expr'] = infix_expr
        self.prop_dict['prefix_expr'] = prefix_expr
        self.parent = None # because at initialization, the model has not been solved

    def __setitem__(self, key, value):
        self.prop_dict[key] = value

    def __getitem__(self, key):
        return self.prop_dict[key]
    
    def update_prop_after_running_model(self, parent_model_structure):
        self.parent = parent_model_structure
        verifiers, falisifiers = self.parent.find_complex_proposition(self['prefix_expr'])
        alt_worlds = find_alt_bits(verifiers, self.parent.poss_bits, self.parent.world_bits, self.parent.eval_world)
        self['verifiers'] = verifiers
        self['falsifieres'] = falisifiers
        self['alt_worlds'] = alt_worlds
    
    def __str__(self):
        return self['infix_expr']