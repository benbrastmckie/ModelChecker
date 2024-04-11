from definitions import *
from print import *
from semantics import *
import time

def product(set_A, set_B):
    product_set = set()
    for a in set_A:
        for b in set_B:
            product_set.add(bit_fusion(a,b)) # NOTE: pretty sure it should be bit_fusion and not fusion, but not certain

def coproduct(set_A, set_B):
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))

def atomic_propositions_dict(all_bits, sentence_letters, model):
    atomic_VFs_dict = dict()
    for letter in sentence_letters:
        ver_bits = relate_sents_and_states(all_bits, letter, model, verify)
        fal_bits = relate_sents_and_states(all_bits, letter, model, falsify)
        atomic_VFs_dict[letter] = (ver_bits, fal_bits)
    return atomic_VFs_dict


def all_propositions_dict(sentence, dictionary): # NEED TO MAKE INPUT DICT, WHIHC WOUDL BE ONLY ATOMIC
    """sentence is a sentence in prefix notation"""
    if len(sentence) == 1:
        sent = sentence[0]
        return dictionary[sent]
    op = sentence[0]
    if "neg" in op:
        return (dictionary[sent][1], dictionary[sent][0])
    Y = sentence[1]
    Z = sentence[2]
    Y_V = all_propositions_dict(Y, dictionary)[0]
    Y_F = all_propositions_dict(Y, dictionary)[1]
    Z_V = all_propositions_dict(Z, dictionary)[0]
    Z_F = all_propositions_dict(Z, dictionary)[1]
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

class ModelStructure():
    def __init__(self, input_premises, input_conclusions): # N is defined outside this thing
        self.premises = input_premises
        self.conclusions = input_conclusions
        self.input_sentences = combine(input_premises, input_conclusions)
        constraints, sent_lets = find_all_constraints(self.input_sentences)
        self.sentence_letters = sent_lets
        
        model_start = time.time() # start benchmark timer
        solved_model = solve_constraints(constraints)
        self.model = solved_model
        model_end = time.time()
        model_total = round(model_end - model_start,4)
        self.model_runtime = model_total

        self.all_bits = find_all_bits(N) # var accessed from outside (not bad, just noting)
        self.poss_bits = find_poss_bits(self.model,self.all_bits)
        self.world_bits = find_world_bits(self.poss_bits)
        self.eval_world = self.model[w] # var accessed from outside (not bad, just noting)

        self.atomic_props_dict = atomic_propositions_dict(self.all_bits, self.sentence_letters, self.model)
        # just missing the which-sentences-true-in-which-worlds

    def find_complex_proposition(self,complex_sentence):
        """sentence is a sentence in prefix notation"""
        if len(complex_sentence) == 1:
            sent = complex_sentence[0]
            return self.atomic_props_dict[sent]
        op = complex_sentence[0]
        if "neg" in op:
            return (self.atomic_props_dict[sent][1], self.atomic_props_dict[sent][0])
        Y = complex_sentence[1]
        Z = complex_sentence[2]
        Y_V = all_propositions_dict(Y, self.atomic_props_dict)[0]
        Y_F = all_propositions_dict(Y, self.atomic_props_dict)[1]
        Z_V = all_propositions_dict(Z, self.atomic_props_dict)[0]
        Z_F = all_propositions_dict(Z, self.atomic_props_dict)[1]
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

    def print_model(self):
        pass


