'''
just a place to put helper fucntions that are in semantics.py that are not in the Semantics class
'''

# from z3 import ForAll as z3ForAll
from z3 import (
    sat,
    Lambda, # used in FiniteForAll and FiniteExists definitions
    Implies,
    Or,
    Not,
    Solver,
    And,
    BitVec,
    BitVecVal,
    substitute, # used in FiniteForAll definition
)
from z3 import Exists as Z3Exists
from z3 import ForAll as Z3ForAll

use_z3_quantifiers = False # currently Z3Exists is being used despite this setting

unid_set = set()
def find_unused_id():
    num = 0
    while num in unid_set:
        num += 1
    unid_set.add(num)
    return str(num)

def ForAllFinite(bvs, formula):
    """
    generates constraints by substituting all possible bitvectors for the variables in the formula
    before taking the conjunction of those constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = ForAllFinite(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return And(constraints)

def ExistsFinite(bvs, formula):
    """
    generates constraints by substituting all possible bitvectors for the variables in the formula
    before taking the disjunction of those constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = ForAllFinite(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)

def SubForAll(bvs, formula):
    """
    This is a modified version of the original which uses substitution
    This works, but gives bad results: false premise models for strengthening the antecedent
    """
    cons_list = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)))
            cons_list.append(substituted_formula)
    if len(bvs) == 2:
        for i in range(num_bvs):
            for j in range(num_bvs):
                substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)), (bvs[1], BitVecVal(j, temp_N)))
                cons_list.append(substituted_formula)
    if len(bvs) == 3:
        for i in range(num_bvs):
            for j in range(num_bvs):
                for k in range(num_bvs):
                    substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)), (bvs[1], BitVecVal(j, temp_N)), (bvs[2], BitVecVal(k, temp_N)))
                    cons_list.append(substituted_formula)
    return And(cons_list)


def FiniteForAll(bvs, formula):
    """
    This is a modified version of the original which uses Lambdas
    Couldn't get this to work
    """
    cons_list = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    lambda_formula = Lambda(bvs, formula)
    if len(bvs) == 1:
        for i in range(num_bvs):
            cons_list.append(lambda_formula[BitVecVal(i,temp_N)])
    if len(bvs) == 2:
        for i in range(num_bvs):
            for j in range(num_bvs):
                saturated_formula = lambda_formula[BitVecVal(i,temp_N),BitVecVal(j,temp_N)]
                cons_list.append(saturated_formula)
    if len(bvs) == 3:
        for i in range(num_bvs):
            for j in range(num_bvs):
                for k in range(num_bvs):
                    cons_list.append(lambda_formula[BitVecVal(i,temp_N),BitVecVal(j,temp_N),BitVecVal(k,temp_N)])
    return And(cons_list)

def FiniteExists(bvs, formula):
    if isinstance(bvs, list):
        new_bvs = ()
        for bv in bvs:
            new_bv = BitVec(str(bv) + find_unused_id(), bv.size())
            new_bvs += (new_bv,)
    else:
        new_bvs = BitVec(str(bvs) + find_unused_id(), bvs.size())
    return Lambda(bvs, formula)[new_bvs]

Exists = Z3Exists
# Exists = Z3Exists if use_z3_quantifiers else ExistsFinite
# Exists = Z3Exists if use_z3_quantifiers else FiniteExists

# ForAll = Z3ForAll
ForAll = Z3ForAll if use_z3_quantifiers else ForAllFinite
# ForAll = Z3ForAll if use_z3_quantifiers else FiniteForAll

def sentence_letters_in_compound(prefix_input_sentence): # can go in model_definitions
    """finds all the sentence letters in ONE input sentence. returns a list. WILL HAVE REPEATS
    returns a list of AtomSorts. CRUCIAL: IN THAT SENSE DOES NOT FOLLOW SYNTAX OF PREFIX SENTS.
    But that's ok, just relevant to know
    used in all_sentence_letters
    """
    if len(prefix_input_sentence) == 1:  # base case: atomic sentence
        return [prefix_input_sentence[0]] # redundant but conceptually clear
    return_list = []
    for part in prefix_input_sentence[1:]:
        return_list.extend(sentence_letters_in_compound(part))
    return return_list

def all_sentence_letters(prefix_sentences): # can go in model_definitions
    """finds all the sentence letters in a list of input sentences, in prefix form.
    returns as a list with no repeats (sorted for consistency) of AtomSorts
    used in find_all_constraints (to feed into find_prop_constraints) and StateSpace __init__"""
    sentence_letters = set()
    for prefix_input in prefix_sentences:
        sentence_letters_in_input = sentence_letters_in_compound(prefix_input)
        for sentence_letter in sentence_letters_in_input:
            sentence_letters.add(sentence_letter)
    return list(sentence_letters)
    # sort just to make every output the same, given sets aren't hashable

def solve_constraints(all_constraints): # will go in ModelSetup
    """ all_constraints is a list of constraints
    find model for the input constraints if there is any
    returns a tuple with a boolean representing if the constraints were solved or not
    and, if True, the model, if False the unsatisfiable core of the constraints"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    return (False, solver.unsat_core())