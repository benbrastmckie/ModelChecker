'''
file contains all definitions for defining the model structure
'''

from z3 import (
    BitVecVal,
    simplify,
)

def summation(n, func, start = 0):
    '''summation of i ranging from start to n of func(i)
    used in find_all_bits'''
    if start == n:
        return func(start)
    return func(start) + summation(n,func,start+1)

# unused
# def find_null_bit(size):
#     '''finds the null bit'''
#     return [BitVecVal(0, size)]

def find_all_bits(size):
    '''extract all bitvectors from the input model
    imported by model_structure'''
    all_bits = []
    max_bit_number = summation(
        size + 1, lambda x: 2**x
    )  # this should hopefully be enough to cover all states
    for val in range(max_bit_number):
        test_bit = BitVecVal(val, size)
        if test_bit in all_bits:
        # break once bits start to repeat
            continue
        all_bits.append(test_bit)
    return all_bits


def find_poss_bits(model,all_bits, possible):
    '''extract all possible bitvectors from all_bits given the model
    imported by model_structure'''
    poss_bits = []
    for bit in all_bits:
        if model.evaluate(possible(bit)): # of type/sort BoolRef
            poss_bits.append(bit)
    return poss_bits


def find_world_bits(poss_bits):
    '''finds the world bits from a list of possible bits.
    used in print_states() and find_relations()'''
    not_worlds = []
    for potential_world in poss_bits:
        if potential_world in not_worlds:
            continue
        for test in poss_bits:
            if bit_part(test, potential_world):
                continue
            if bit_proper_part(potential_world, test):
                not_worlds.append(potential_world)
                break
    world_bits = [world for world in poss_bits if world not in not_worlds]
    # for world in world_bits:
    #     print(model.evaluate(is_world(world)))
    #     if not model.evaluate(is_world(world)):
    #         raise ValueError(f'{world} was in world_bits but is not a world per the model')
    # for not_world in not_worlds:
    #     print(model.evaluate(is_world(not_world)))
    #     # if model.evaluate(is_world(not_world)):
    #     #     raise ValueError(f'{not_world} was not in world_bits but is a world per the model')
    return world_bits


def find_compatible_parts(verifier_bit, poss_bits, eval_world):
    """
    Finds the parts of the eval_world compatible with the verifier_bit.
    Used in find_alt_bits() method in ModelStructure class
    """
    comp_parts = []
    for part in poss_bits:
        if bit_fusion(verifier_bit, part) in poss_bits and bit_part(part, eval_world):
            comp_parts.append(part)
            # ie, if fusion is possible and the bit part is in the eval_world
    return comp_parts


def find_max_comp_ver_parts(verifier_bit, comp_parts):
    """
    Finds a list of fusions of the verifier_bit and a maximal compatible part.
    Used in find_alt_bits() method of ModelStructure class,
    immediately after find_compatible_parts() above.
    """
    not_max_comp_part = []
    for max_part in comp_parts:
        for test in comp_parts:
            if bit_proper_part(max_part, test):
                not_max_comp_part.append(max_part)
                break  # continues with the first for loop
    max_comp_parts = [part for part in comp_parts if part not in not_max_comp_part]
    max_comp_ver_parts = [bit_fusion(verifier_bit, max) for max in max_comp_parts]
    return max_comp_ver_parts

def relate_sents_and_states(all_bits, sentence, model, relation):
    """helper function for finding verifier and falsifier states to sentences in a model
    Used in atomic_propositions_dict
    DOES NOT CHECK IF THESE ARE POSSIBLE. """
    relation_set = set()
    for bit in all_bits:
        if model.evaluate(relation(bit, model[sentence])):
            relation_set.add(bit)
    return relation_set

def find_true_and_false_in_alt(alt_bit, parent_model_structure):
    """returns two sets as a tuple, one being the set of sentences true in the alt world and the other the set being false.
    Used in evaluate_mainclause_cf_expr()"""
    extensional_sentences = parent_model_structure.extensional_subsentences
    # B: is this still true once modal and counterfactual prop_objects include verifiers and falsifiers?
    # TODO: below creates problem with nested counterfactuals
    # TODO: I think this was resolved
    # extensional_sentences = parent_model_structure.all_subsentences
    all_bits = parent_model_structure.all_bits
    true_in_alt = []
    for R in extensional_sentences:
        for bit in all_bits:
            # print(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True))
            # print(type(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True)))
            if bit in find_complex_proposition(parent_model_structure, R, alt_bit)[0] and bit_part(bit, alt_bit):
                true_in_alt.append(R)
                break  # returns to the for loop over sentence_letters
    false_in_alt = [R for R in extensional_sentences if not R in true_in_alt] # replace with
    return (repeats_removed(true_in_alt), repeats_removed(false_in_alt))
    # was giving repeats for some reason? Wasn't previously. fixed it up with repeats_removed


def pretty_set_print(set_with_strings):
    """input a set with strings
    print that same set but with no quotation marks around each individual string, and also with the set in order
    returns the set as a string
    Used in print_vers_and_fals() and print_alt_worlds()"""
    sorted_set = sorted(list(set_with_strings))  # actually type list, not set
    print_str = "{"
    for i, elem in enumerate(sorted_set):
        print_str += elem
        if i != len(sorted_set) - 1:
            print_str += ", "
    print_str += "}"
    return print_str

def product(set_A, set_B):
    product_set = set()
    for a in set_A:
        for b in set_B:
            product_set.add(bit_fusion(a,b))
    return product_set

def coproduct(set_A, set_B):
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))

def atomic_propositions_dict(ms_object):
    all_bits = ms_object.all_bits
    sentence_letters = ms_object.sentence_letters
    model = ms_object.model
    verify = ms_object.verify
    falsify = ms_object.falsify
    atomic_VFs_dict = {}
    for letter in sentence_letters:
        ver_bits = relate_sents_and_states(all_bits, letter, model, verify)
        fal_bits = relate_sents_and_states(all_bits, letter, model, falsify)
        atomic_VFs_dict[letter] = (ver_bits, fal_bits)
    return atomic_VFs_dict


#############################################
######### MOVED FROM DEFINITIONS.PY #########
#############################################
        


def bit_fusion(bit_s, bit_t):
    """the result of taking the maximum for each index in _s and _t"""
    return simplify(bit_s | bit_t)
    # NOTE: this does seem to make a difference, otherwise no comp_parts

def bit_part(bit_s, bit_t):
    """the fusion of _s and _t is identical to bit_t"""
    return bool(simplify(bit_fusion(bit_s, bit_t) == bit_t))
    # NOTE: this does seem to make a difference, otherwise no comp_parts

def bit_proper_part(bit_s, bit_t):
    """bit_s is a part of bit_t and bit_t is not a part of bit_s"""
    return bool(bit_part(bit_s, bit_t)) and not bit_s == bit_t
    # NOTE: this does not seem to make a difference and so has been turned off
    # in the interest of discovering if it is required or not
    # return bool(bit_part(bit_s, bit_t)) and not bit_s == bit_t

def index_to_substate(index):
    '''
    test cases should make evident what's going on
    >>> index_to_substate(0)
    'a'
    >>> index_to_substate(26)
    'aa'
    >>> index_to_substate(27)
    'bb'
    >>> index_to_substate(194)
    'mmmmmmmm'
    used in bitvec_to_substates
    '''
    number = index + 1 # because python indices start at 0
    letter_dict = {1:'a', 2:'b', 3:'c', 4:'d', 5:'e', 6:'f', 7:'g', 8:'h', 9:'i', 10:'j',
                   11:'k', 12:'l', 13:'m', 14:'n', 15:'o', 16:'p', 17:'q', 18:'r', 19:'s', 20:'t',
                   21:'u', 22:'v', 23:'w', 24:'x', 25:'y', 26:'z'} # could be make less hard-code-y
                            # but this makes it clearer and more intuitive what we want to happen
    letter = letter_dict[number%26]
    return ((number//26) + 1) * letter

def int_to_binary(integer, number, backwards_binary_str = ''):
    '''converts a #x string to a #b string. follows the first algorithm that shows up on google
    when you google how to do this
    used in bitvec_to_substates'''
    rem = integer%2
    new_backwards_str = backwards_binary_str + str(rem)
    if integer//2 == 0: # base case: we've reached the end
        remaining_0s_to_tack_on = number - len(new_backwards_str) # to fill in the zeroes
        return '#b' + remaining_0s_to_tack_on * '0' + new_backwards_str[::-1]
    new_int = integer//2
    return int_to_binary(new_int, number, new_backwards_str)


# has to do with printing
def bitvec_to_substates(bit_vec, N):
    '''converts bitvectors to fusions of atomic states.'''
    bit_vec_as_string = bit_vec.sexpr()
    if 'x' in bit_vec_as_string: # if we have a hexadecimal, ie N=4m
        integer = int(bit_vec_as_string[2:],16)
        bit_vec_as_string = int_to_binary(integer, N)
    bit_vec_backwards = bit_vec_as_string[::-1]
    state_repr = ""
    for i, char in enumerate(bit_vec_backwards):
        if char == "b":
            if not state_repr:
                return "□"  #  null state
            return state_repr[0 : len(state_repr) - 1]
        if char == "1":
            state_repr += index_to_substate(i)
            state_repr += "."
    raise ValueError("should have run into 'b' at the end but didn't")

def infix_combine(premises, conclusions):
    '''combines the premises with the negation of the conclusion(s).
    premises are infix sentences, and so are the conclusions
    imported by model_structure, in __init__ method of ModelStructure'''
    input_sentences = premises[:]
    for sent in conclusions:
        neg_sent = '\\neg ' + sent
        input_sentences.append(neg_sent)
    return input_sentences

def disjoin_prefix(sentences):
    """disjoins the list of sentences in prefix form
    helper for prefix_combine (immediately below)"""
    if len(sentences) > 2:
        copy_sentences = sentences[:]
        first_sent = copy_sentences.pop(0)
        return ['\\vee ', first_sent, disjoin_prefix(copy_sentences)]
    # if len(sentences) == 1:
    #     return sentences[0]
    return sentences

def prefix_combine(prefix_premises, prefix_conclusions):
    '''negates and disjoins the prefix conclusions, combining the result with
    prefix premises to form a new list'''
    neg_conclusions = [['\\neg ', con] for con in prefix_conclusions]
    disjoin_neg_conclusions = disjoin_prefix(neg_conclusions)
    return prefix_premises + disjoin_neg_conclusions

#################################
##### MOVED FROM SEMANTICS ######
#################################

def is_counterfactual(prefix_sentence):
    '''returns a boolean to say whether a given sentence is a counterfactual
    used in find_extensional_subsentences'''
    if len(prefix_sentence) == 1:
        return False
    if len(prefix_sentence) == 2:
        return is_counterfactual(prefix_sentence[1])
    if 'boxright' in prefix_sentence[0]:
        return True
    return is_counterfactual(prefix_sentence[1]) or is_counterfactual(prefix_sentence[2])

def is_modal(prefix_sentence):
    '''returns a boolean to say whether a given sentence is a counterfactual
    used in find_extensional_subsentences'''
    if len(prefix_sentence) == 1:
        return False
    op = prefix_sentence[0]
    if len(prefix_sentence) == 2:
        if 'Box' in op or 'Diamond' in op:
            return True
        return is_modal(prefix_sentence[1])
    return is_modal(prefix_sentence[1]) or is_modal(prefix_sentence[2])

def is_extensional(prefix_sentence):
    return not is_modal(prefix_sentence) and not is_counterfactual(prefix_sentence)

# TODO: linter says all or none of the returns should be an expression
def all_subsentences_of_a_sentence(prefix_sentence, progress=False):
    '''finds all the subsentence of a prefix sentence
    returns these as a set
    used in find_extensional_subsentences'''
    if progress is False:
        progress = []
    # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
    progress.append(prefix_sentence)
    if len(prefix_sentence) == 1:
        return progress
    if len(prefix_sentence) == 2:
        # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
        return all_subsentences_of_a_sentence(prefix_sentence[1], progress)
    if len(prefix_sentence) == 3:
        # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
        left_subsentences = all_subsentences_of_a_sentence(prefix_sentence[1], progress)
        # TODO: linter says cannot access member "append" for type "Literal[True]" Member "append" is unknown
        right_subsentences = all_subsentences_of_a_sentence(prefix_sentence[2], progress)
        all_subsentences = left_subsentences + right_subsentences
        return all_subsentences

def find_subsentences_of_kind(prefix_sentences, kind):
    '''used to find the extensional, modal, and counterfactual sentences. 
    kind is a string, either "extensional", "modal", "counterfactual", or 'all' for a tuple of
    of the three kinds in the order extensional, modal, counterfactual, and then all the subsents
    returns a list of that kind'''
    rr = repeats_removed
    all_subsentences = []
    for prefix_sent in prefix_sentences:
        all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
    if kind == 'extensional':
        return_list = [sent for sent in all_subsentences if is_extensional(sent)]
    if kind == 'modal':
        return_list = [sent for sent in all_subsentences if is_modal(sent)]
    if kind == 'counterfactual':
        return_list = [sent for sent in all_subsentences if is_counterfactual(sent)]
    if kind == 'all':
        counterfactual = rr([sent for sent in all_subsentences if is_counterfactual(sent)])
        modal = rr([sent for sent in all_subsentences if is_modal(sent)])
        extensional = rr([sent for sent in all_subsentences if sent not in counterfactual and sent not in modal])
        return (extensional, modal, counterfactual, all_subsentences)
    return rr(return_list)

def repeats_removed(L):
    '''takes a list and removes the repeats in it.
    used in find_all_constraints'''
    seen = []
    for obj in L:
        if obj not in seen:
            seen.append(obj)
    return seen


########################################
###### MOVED FROM model_structure ######
########################################

def evaluate_modal_expr(modelstructure, prefix_modal, eval_world):
    '''evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
    used to initialize Counterfactuals
    returns a bool representing whether the counterfactual is true at the world or not'''
    op, argument = prefix_modal[0], prefix_modal[1]
    if is_modal(argument):
        if modelstructure.evaluate_modal_expr(prefix_modal) is True: # ie, verifiers is null state
            return True # both Box and Diamond will return true, since verifiers is not empty
        return False
    if 'Diamond' in op:
        # TODO: linter error: uninitalized is not iterable  "__iter__" does not return object
        for world in modelstructure.world_bits:
            if world in find_complex_proposition(modelstructure, argument, eval_world)[0]:
                return True
        return False
    if 'Box' in op:
        # TODO: linter error: uninitalized is not iterable  "__iter__" does not return object
        for world in modelstructure.world_bits:
            if world not in find_complex_proposition(modelstructure, argument, eval_world)[0]:
                return False
        return True
    
def evaluate_mainclause_cf_expr(modelstructure, prefix_cf, eval_world):
    """evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
    used to initialize Counterfactuals
    returns a bool representing whether the counterfactual is true at the world or not
    """
    op = prefix_cf[0]
    assert "boxright" in op, f"{prefix_cf} is not a main-clause counterfactual!"
    ant_expr, consequent_expr = prefix_cf[1], prefix_cf[2]
    assert is_extensional(ant_expr), f"the antecedent {ant_expr} is not extensional!"
    ant_verifiers = find_complex_proposition(modelstructure, ant_expr, eval_world)[0]
    # ant_prop = self.find_proposition_object(ant_verifiers, ext_only=True)
    ant_alts_to_eval_world = modelstructure.find_alt_bits(ant_verifiers, eval_world)
    for u in ant_alts_to_eval_world:
        # QUESTION: why is string required? Is Z3 removing the lists?
        if is_counterfactual(consequent_expr):
            if not find_complex_proposition(modelstructure, consequent_expr, u)[0]:
                return False
        elif str(consequent_expr) not in str(find_true_and_false_in_alt(u, modelstructure)[0]):
            return False
    return True

def true_and_false_worlds_for_cf(modelstructure, complex_cf_sent):
    '''used in find_complex_proposition'''
    # assert 'boxright' in complex_cf_sent[0], 'this func is only for main-clause cfs!'
    worlds_true_at, worlds_false_at = set(), set()
    for world in modelstructure.world_bits:
        if find_complex_proposition(modelstructure, complex_cf_sent, world)[0]:
            worlds_true_at.add(world)
            continue
        worlds_false_at.add(world)
    return (worlds_true_at, worlds_false_at)

def find_complex_proposition(modelstructure, complex_sentence, eval_world):
    """sentence is a sentence in prefix notation
    For a given complex proposition, returns the verifiers and falsifiers of that proposition
    given a solved model
    for a counterfactual, it'll just give the worlds it's true at and worlds it's not true at
    """
    if not modelstructure.atomic_props_dict:
        raise ValueError(
            "There is nothing in atomic_props_dict yet. Have you actually run the model?"
        )
    if len(complex_sentence) == 1:
        sent = complex_sentence[0]
        # TODO: linter error: expected 0 arguments
        return modelstructure.atomic_props_dict[sent]
    op = complex_sentence[0]
    Y = complex_sentence[1]
    if "neg" in op:
        Y_V, Y_F = find_complex_proposition(modelstructure, Y, eval_world)
        return (Y_F, Y_V)
    null_state = {BitVecVal(0,modelstructure.N)}
    if 'Box' in op or 'Diamond' in op:
        if evaluate_modal_expr(modelstructure, complex_sentence, eval_world):
            return (null_state, set())
        return (set(), null_state)
    Z = complex_sentence[2]
    Y_V, Y_F = find_complex_proposition(modelstructure, Y, eval_world)
    Z_V, Z_F = find_complex_proposition(modelstructure, Z, eval_world)
    if "wedge" in op:
        return (product(Y_V, Z_V), coproduct(Y_F, Z_F))
    if "vee" in op:
        return (coproduct(Y_V, Z_V), product(Y_F, Z_F))
    if "leftrightarrow" in op:
        return (
            product(coproduct(Y_F, Z_V), coproduct(Y_V, Z_F)),
            coproduct(product(Y_V, Z_F), product(Y_F, Z_V)),
        )
    if "rightarrow" in op:
        return (coproduct(Y_F, Z_V), product(Y_V, Z_F))
    if "boxright" in op:
        if evaluate_mainclause_cf_expr(modelstructure, complex_sentence, eval_world):
            return (null_state, set())
        return (set(), null_state)
    raise ValueError(f"Don't know how to handle {op} operator")
