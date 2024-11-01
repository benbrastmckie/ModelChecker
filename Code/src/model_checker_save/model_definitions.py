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
    max_bit_number = summation(size + 1, lambda x: 2**x)
    for val in range(max_bit_number):
        test_bit = BitVecVal(val, size)
        if test_bit in all_bits:
            continue
        all_bits.append(test_bit)
    return all_bits


def find_poss_bits(z3_model, all_bits, possible):
    '''extract all possible bitvectors from all_bits given the model
    imported by model_structure'''
    poss_bits = []
    for bit in all_bits:
        if z3_model.evaluate(possible(bit)): # of type/sort BoolRef
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
    return world_bits


def find_compatible_parts(verifier_bit, poss_bits, eval_world):
    """
    Finds the parts of the eval_world compatible with the verifier_bit.
    Used in find_alt_bits() method in ModelSetup class
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
    Used in find_alt_bits() method of ModelSetup class,
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

def relate_sents_and_states(all_bits, sentence, z3_model, relation):
    """helper function for finding verifier and falsifier states to sentences in a model
    Used in atomic_propositions_dict
    DOES NOT CHECK IF THESE ARE POSSIBLE. """
    relation_set = set()
    for bit in all_bits:
        if z3_model.evaluate(relation(bit, z3_model[sentence])):
            relation_set.add(bit)
    return relation_set

# def find_true_and_false_in_alt(alt_bit, model_structure):
#     """returns two sets as a tuple, one being the set of sentences true in the alt world and the other the set being false.
#     Used in evaluate_mainclause_cf_expr()"""
#     all_subsentences = model_structure.all_subsentences
#     # extensional_sentences = parent_model_structure.all_subsentences
#     all_bits = model_structure.all_bits
#     true_in_alt = []
#     for sub in all_subsentences:
#         for bit in all_bits:
#             # print(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True))
#             # print(type(model.evaluate(extended_verify(bit, R, evaluate=True), model_completion=True)))
#             if bit in find_complex_proposition(model_structure, sub, alt_bit)[0] and bit_part(bit, alt_bit):
#                 true_in_alt.append(sub)
#                 break  # returns to the for loop over sentence_letters
#     false_in_alt = [R for R in all_subsentences if not R in true_in_alt] # replace with
#     return (repeats_removed(true_in_alt), repeats_removed(false_in_alt))
#     # was giving repeats for some reason? Wasn't previously. fixed it up with repeats_removed


def pretty_set_print(set_with_strings):
    """input a set with strings print that same set but with no quotation marks around each
    individual string, and also with the set in order returns the set as a string
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
    """set of pairwise fusions of elements in set_A and set_B"""
    product_set = set()
    for bit_a in set_A:
        for bit_b in set_B:
            bit_ab = bit_fusion(bit_a, bit_b)
            product_set.add(bit_ab)
    return product_set

def coproduct(set_A, set_B):
    """union closed under pairwise fusion"""
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))

def atomic_propositions_dict_maker(state_space):
    """assigns sentence_letters to propositions"""
    all_bits = state_space.all_bits
    sentence_letters = state_space.sentence_letters
    z3_model = state_space.z3_model
    verify = state_space.verify
    falsify = state_space.falsify
    atomic_VFs_dict = {}
    for letter in sentence_letters:
        ver_bits = relate_sents_and_states(all_bits, letter, z3_model, verify)
        fal_bits = relate_sents_and_states(all_bits, letter, z3_model, falsify)
        atomic_VFs_dict[letter] = (ver_bits, fal_bits)
    return atomic_VFs_dict

def bit_fusion(bit_s, bit_t):
    """the result of taking the maximum for each index in _s and _t"""
    return simplify(bit_s | bit_t)
    # NOTE: 'simplify' does seem to make a difference, otherwise no comp_parts

def bit_part(bit_s, bit_t):
    """the fusion of _s and _t is identical to bit_t"""
    return bool(simplify(bit_fusion(bit_s, bit_t) == bit_t))
    # NOTE: 'bool' does seem to make a difference, otherwise no comp_parts

def bit_proper_part(bit_s, bit_t):
    """bit_s is a part of bit_t and bit_t is not a part of bit_s"""
    return bool(bit_part(bit_s, bit_t)) and not bit_s == bit_t
    # NOTE: this does not seem to make a difference and so has been turned off

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

# def infix_combine(premises, conclusions):
#     '''combines the premises with the negation of the conclusion(s).
#     premises are infix sentences, and so are the conclusions
#     imported by model_structure, in __init__ method of ModelStructure'''
#     input_sentences = premises[:]
#     for sent in conclusions:
#         neg_sent = '\\neg ' + sent
#         input_sentences.append(neg_sent)
#     return input_sentences

# def disjoin_prefix(sentences):
#     """disjoins the list of sentences in prefix form
#     helper for prefix_combine (immediately below)"""
#     if len(sentences) > 2:
#         copy_sentences = sentences[:]
#         first_sent = copy_sentences.pop(0)
#         return ['\\vee ', first_sent, disjoin_prefix(copy_sentences)]
#     # if len(sentences) == 1:
#     #     return sentences[0]
#     return sentences

# def prefix_combine(prefix_premises, prefix_conclusions):
#     '''negates and disjoins the prefix conclusions, combining the result with
#     prefix premises to form a new list'''
#     neg_conclusions = [['\\neg ', con] for con in prefix_conclusions]
#     disjoin_neg_conclusions = disjoin_prefix(neg_conclusions)
#     return prefix_premises + disjoin_neg_conclusions

# def is_counterfactual(prefix_sentence):
#     '''returns a boolean to say whether a given sentence is a counterfactual
#     used in find_extensional_subsentences'''
#     if len(prefix_sentence) == 1:
#         return False
#     if len(prefix_sentence) == 2:
#         return is_counterfactual(prefix_sentence[1])
#     if 'boxright' in prefix_sentence[0]:
#         return True
#     return is_counterfactual(prefix_sentence[1]) or is_counterfactual(prefix_sentence[2])

# def is_modal(prefix_sentence):
#     '''returns a boolean to say whether a given sentence is a counterfactual
#     used in find_extensional_subsentences'''
#     if len(prefix_sentence) == 1:
#         return False
#     op = prefix_sentence[0]
#     if len(prefix_sentence) == 2:
#         if 'Box' in op or 'Diamond' in op:
#             return True
#         return is_modal(prefix_sentence[1])
#     return is_modal(prefix_sentence[1]) or is_modal(prefix_sentence[2])

# def is_extensional(prefix_sentence):
#     return not is_modal(prefix_sentence) and not is_counterfactual(prefix_sentence)

# def all_subsentences_of_a_sentence(prefix_sentence, progress=[]):
#     '''finds all the subsentence of a prefix sentence
#     returns these as a set
#     used in find_extensional_subsentences'''
#     if progress is False:
#         progress = []
#     progress.append(prefix_sentence)
#     if len(prefix_sentence) == 1:
#         return progress
#     if len(prefix_sentence) == 2:
#         return all_subsentences_of_a_sentence(prefix_sentence[1], progress)
#     if len(prefix_sentence) == 3:
#         left_subsentences = all_subsentences_of_a_sentence(prefix_sentence[1], progress)
#         right_subsentences = all_subsentences_of_a_sentence(prefix_sentence[2], progress)
#         all_subsentences = left_subsentences + right_subsentences
#         return all_subsentences

# def find_subsentences_of_kind(prefix_sentences, kind):
#     '''used to find the extensional, modal, and counterfactual sentences. 
#     kind is a string, either "extensional", "modal", "counterfactual", or 'all' for a tuple of
#     of the three kinds in the order extensional, modal, counterfactual, and then all the subsents
#     returns a list of that kind'''
#     rr = repeats_removed
#     all_subsentences = []
#     for prefix_sent in prefix_sentences:
#         all_subsentences.extend(all_subsentences_of_a_sentence(prefix_sent))
#     if kind == 'extensional':
#         return_list = [sent for sent in all_subsentences if is_extensional(sent)]
#     if kind == 'modal':
#         return_list = [sent for sent in all_subsentences if is_modal(sent)]
#     if kind == 'counterfactual':
#         return_list = [sent for sent in all_subsentences if is_counterfactual(sent)]
#     if kind == 'all':
#         counterfactual = rr([sent for sent in all_subsentences if is_counterfactual(sent)])
#         modal = rr([sent for sent in all_subsentences if is_modal(sent)])
#         extensional = rr([sent for sent in all_subsentences if sent not in counterfactual and sent not in modal])
#         return (extensional, modal, counterfactual, all_subsentences)
#     return rr(return_list)

def repeats_removed(sentences):
    '''takes a list and removes the repeats in it.
    used in find_all_constraints'''
    seen = []
    for obj in sentences:
        if obj not in seen:
            seen.append(obj)
    return seen

def subsentences_of(prefix_sentence):
    '''finds all the subsentence of a prefix sentence
    returns these as a set
    used in find_extensional_subsentences'''
    progress = []
    progress.append(prefix_sentence)
    if len(prefix_sentence) == 2:
        sub_sentsentences = subsentences_of(prefix_sentence[1])
        return progress + sub_sentsentences
    if len(prefix_sentence) == 3:
        left_subsentences = subsentences_of(prefix_sentence[1])
        right_subsentences = subsentences_of(prefix_sentence[2])
        all_subsentences = left_subsentences + right_subsentences + progress
        return repeats_removed(all_subsentences)
    return progress

def find_subsentences(prefix_sentences):
    """take a set of prefix sentences and returns a set of all subsentences"""
    all_subsentences = []
    for prefix_sent in prefix_sentences:
        all_prefix_subs = subsentences_of(prefix_sent)
        all_subsentences.extend(all_prefix_subs)
    return repeats_removed(all_subsentences)

def evaluate_modal_expr(model_setup, prefix_modal, eval_world):
    '''evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
    used to initialize Counterfactuals
    returns a bool representing whether the counterfactual is true at the world or not'''
    operator, argument = prefix_modal[0], prefix_modal[1]
    # TODO: is this necessary?
    # if is_modal(argument):
    #     if model_structure.evaluate_modal_expr(prefix_modal) is True: # ie, verifiers is null state
    #         return True # both Box and Diamond will return true, since verifiers is not empty
    #     return False
    if 'Diamond' in operator:
        for poss in model_setup.poss_bits:
            if poss in find_complex_proposition(model_setup, argument, eval_world)[0]:
                return True
        return False
    if 'Box' in operator:
        for poss in model_setup.poss_bits:
            if poss in find_complex_proposition(model_setup, argument, eval_world)[1]:
                return False
        return True
    raise ValueError(
        prefix_modal,
        "Something has gone wrong in evaluate_cf_counterfactual. "
        f"The operator {operator} in {prefix_modal} is not a modal."
    )

def evaluate_cf_expr(model_setup, cf_sentence, eval_world):
    """evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
    used to initialize Counterfactuals
    returns a bool representing whether the counterfactual is true at the world or not
    """
    operator, antecedent, consequent = cf_sentence[0], cf_sentence[1], cf_sentence[2]
    antecedent_vers = find_complex_proposition(model_setup, antecedent, eval_world)[0]
    consequent_vers, consequent_fals = find_complex_proposition(
        model_setup,
        consequent,
        eval_world,
    )
    if 'boxright' in operator:
        antecedent_alts = model_setup.find_alt_bits(antecedent_vers, eval_world)
        for alt_world in antecedent_alts:
            for falsifier in consequent_fals:
                if bit_part(falsifier, alt_world):
                    return False
        return True
    if 'circleright' in operator:
        antecedent_alts = model_setup.find_alt_bits(antecedent_vers, eval_world)
        for alt_world in antecedent_alts:
            for verifier in consequent_vers:
                if bit_part(verifier, alt_world):
                    return True
        return False
    if 'imposition' in operator:
        antecedent_imps = model_setup.find_imp_bits(antecedent_vers, eval_world)
        for alt_world in antecedent_imps:
            for falsifier in consequent_fals:
                if bit_part(falsifier, alt_world):
                    return False
        return True
    raise ValueError(
        cf_sentence,
        "Something has gone wrong in evaluate_cf_counterfactual. "
        f"The operator {operator} in {cf_sentence} is not a counterfatual."
    )


# def evaluate_mainclause_cf_expr(model_structure, prefix_cf, eval_world):
#     """evaluates whether a counterfatual in prefix form is true at a world (BitVecVal).
#     used to initialize Counterfactuals
#     returns a bool representing whether the counterfactual is true at the world or not
#     """
#     op = prefix_cf[0]
#     assert "boxright" in op, f"{prefix_cf} is not a main-clause counterfactual!"
#     ant_expr, consequent_expr = prefix_cf[1], prefix_cf[2]
#     # assert is_extensional(ant_expr), f"the antecedent {ant_expr} is not extensional!"
#     ant_verifiers = find_complex_proposition(model_structure, ant_expr, eval_world)[0]
#     ant_alts_to_eval_world = model_structure.find_alt_bits(ant_verifiers, eval_world)
#     for u in ant_alts_to_eval_world:
#         # QUESTION: why is string required? Is Z3 removing the lists?
#         if is_counterfactual(consequent_expr):
#             if not find_complex_proposition(model_structure, consequent_expr, u)[0]:
#                 return False
#         elif str(consequent_expr) not in str(find_true_and_false_in_alt(u, model_structure)[0]):
#             return False
#     return True

def true_and_false_worlds_for_cf(model_structure, cf_sentence):
    '''used in find_complex_proposition'''
    worlds_true_at, worlds_false_at = set(), set()
    for world in model_structure.world_bits:
        if find_complex_proposition(model_structure, cf_sentence, world)[0]:
            worlds_true_at.add(world)
            continue
        worlds_false_at.add(world)
    return (worlds_true_at, worlds_false_at)

def find_precluders(verifiers, all_bits, poss_bits):
    """simulates the set of falsifiers"""
    # if not verifiers:
    #     return null_singleton
    precluders = []
    for state in all_bits:
        incomp_ver = set()
        for ver in verifiers:
            if bit_fusion(state, ver) not in poss_bits:
                incomp_ver.add(ver)
                break
        comp_ver = set()
        for ver in verifiers:
            if bit_fusion(state, ver) in poss_bits:
                comp_ver.add(ver)
                break
        if incomp_ver and not comp_ver:
            precluders.append(state)
    # TODO: would be nice to sort the precluders but they are bits
    # excluders_list = sorted(excluders)
    return precluders

def find_excluders(verifiers, all_bits, poss_bits, null_singleton):
    """simulates the set of falsifiers"""
    # if not verifiers:
    #     return null_singleton
    excluders = []
    for state in all_bits:
        comp_state_parts = set()
        for part in all_bits:
            if bit_part(part, state) and not part in null_singleton:
                for ver in verifiers:
                    if bit_fusion(part, ver) in poss_bits:
                        comp_state_parts.add(part)
                        break
        incomp_ver_parts = set()
        for ver in verifiers:
            for part in all_bits:
                if bit_part(part, state) and not part in null_singleton:
                    if bit_fusion(part, ver) not in poss_bits:
                        incomp_ver_parts.add(part)
                        break
        if not comp_state_parts and incomp_ver_parts:
            excluders.append(state)
    # TODO: would be nice to sort the excluders but they are bits
    # excluders_list = sorted(excluders)
    return excluders

def contained_in(set_A, set_B):
    """checks whether every element in set_A has a part in set_B"""
    for bit_a in set_A:
        found = False
        for bit_b in set_B:
            if bit_part(bit_b, bit_a):
                found = True
                break
        if not found:
            return False
    return True

def find_complex_proposition(model_setup, complex_sentence, eval_world):
    """sentence is a sentence in prefix notation
    For a given complex proposition, returns the verifiers and falsifiers of that proposition
    given a solved model
    for a counterfactual, it'll just give the worlds it's true at and worlds it's not true at
    """
    if not model_setup.atomic_props_dict:
        raise ValueError(
            "There is nothing in atomic_props_dict yet. Has a model been found?"
        )
    if len(complex_sentence) == 1:
        sent = complex_sentence[0]
        return model_setup.atomic_props_dict[sent]
    op = complex_sentence[0]
    Y = complex_sentence[1]
    if "neg" in op:
        Y_V, Y_F = find_complex_proposition(model_setup, Y, eval_world)
        return (Y_F, Y_V)
    N = model_setup.N
    null_singleton = {BitVecVal(0,N)}
    if "not" in op:
        all_bits = model_setup.all_bits
        poss_bits = model_setup.poss_bits
        Y_V, Y_F = find_complex_proposition(model_setup, Y, eval_world)
        vers = find_excluders(Y_F, all_bits, poss_bits, null_singleton)
        fals = find_excluders(Y_V, all_bits, poss_bits, null_singleton)
        return (vers, fals)
    # if "pre" in op:
    #     all_bits = model_structure.all_bits
    #     poss_bits = model_structure.poss_bits
    #     Y_V, Y_F = find_complex_proposition(model_structure, Y, eval_world)
    #     vers = find_precluders(Y_F, all_bits, poss_bits)
    #     fals = find_precluders(Y_V, all_bits, poss_bits)
    #     return (vers, fals)
    if 'Box' in op or 'Diamond' in op:
        if evaluate_modal_expr(model_setup, complex_sentence, eval_world):
            return (null_singleton, set())
        return (set(), null_singleton)
    Z = complex_sentence[2]
    Y_V, Y_F = find_complex_proposition(model_setup, Y, eval_world)
    Z_V, Z_F = find_complex_proposition(model_setup, Z, eval_world)
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
    if "imposition" in op:
        if evaluate_cf_expr(model_setup, complex_sentence, eval_world):
            return (null_singleton, set())
        return (set(), null_singleton)
    if "boxright" in op:
        if evaluate_cf_expr(model_setup, complex_sentence, eval_world):
            # val = evaluate_cf_expr(model_structure, complex_sentence, eval_world)
            # print(f"TEST: truth_vf of cf = {val}")
            return (null_singleton, set())
        return (set(), null_singleton)
    if "circleright" in op:
        if evaluate_cf_expr(model_setup, complex_sentence, eval_world):
            return (null_singleton, set())
        return (set(), null_singleton)
    if "leq" in op:
        if Y_V <= Z_V and product(Y_F, Z_F) <= Z_F and contained_in(Z_F, Y_F):
            return (null_singleton, set())
        return (set(), null_singleton)
    if "sqsubseteq" in op:
        if product(Y_V, Z_V) <= Z_V and contained_in(Z_V, Y_V) and Y_F <= Z_F:
            return (null_singleton, set())
        return (set(), null_singleton)
    if "preceq" in op:
        if product(Y_V, Z_V) <= Z_V and product(Y_F, Z_F) <= Z_F:
            return (null_singleton, set())
        return (set(), null_singleton)
    if "equiv" in op:
        if Y_V == Z_V and Y_F == Z_F:
            return (null_singleton, set())
        return (set(), null_singleton)
    raise ValueError(f"Don't know how to handle {op} operator")
