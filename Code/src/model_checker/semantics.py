"""
contains all semantic functions
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
"""

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

def sentence_letters_in_compound(prefix_input_sentence):
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

def all_sentence_letters(prefix_sentences):
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


def define_N_semantics(verify, falsify, possible, assign, N):
    # NOTE: just thought of this—we could make the options to do non_null or non_triv optional.
    # Like it coulld be an optional argument put into the model at the top level, just like
    # unsat_core is. Let me below know if you think that's a good idea or if it wouln't be useful.
    '''function that makes the function to make the constraints (and list of sentence letters
    and prefix sentences) This has to be done in order to define N in an input file—you'll see
    here that N is passed in as a variable to the function, after which these 'make' a semantics
    with that N (and the other inputs to this function also depend on N)
    returns a function find_all_constraints that is used to find the constraints, the sentence letters,
    and prefix sentences.. 
    '''
    # def non_null_verify(bit_s, atom):
    #     """bit_s verifies atom and is not the null state
    #     returns a Z3 constraint"""
    #     return And(Not(bit_s == 0), verify(bit_s, atom))
    #
    # def non_null_falsify(bit_s, atom):
    #     """bit_s verifies atom and is not the null state
    #     returns a Z3 constraint"""
    #     return And(Not(bit_s == 0), falsify(bit_s, atom))
    #
    # def non_triv_verify(bit_s, atom):
    #     """bit_s verifies atom and is not the null state
    #     returns a Z3 constraint"""
    #     return And(non_null_verify(bit_s, atom), possible(bit_s))
    #
    # def non_triv_falsify(bit_s, atom):
    #     """bit_s verifies atom and is not the null state
    #     returns a Z3 constraint"""
    #     return And(non_null_falsify(bit_s, atom), possible(bit_s))

    def fusion(bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t

    def is_part_of(bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return fusion(bit_s, bit_t) == bit_t

    def non_null_part_of(bit_s, bit_t):
        """bit_s verifies atom and is not the null state
        returns a Z3 constraint"""
        return And(Not(bit_s == 0), is_part_of(bit_s, bit_t))

    def compatible(bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return possible(fusion(bit_x, bit_y))

    def maximal(bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = BitVec("max_x", N)
        return ForAll(
            x,
            Implies(
                compatible(x, bit_w),
                is_part_of(x, bit_w),
            ),
        )

    def is_world(bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return And(
            possible(bit_w),
            maximal(bit_w),
        )

    def max_compatible_part(bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = BitVec("max_part", N)
        return And(
            is_part_of(bit_x, bit_w),
            compatible(bit_x, bit_y),
            ForAll(
                z,
                Implies(
                    And(
                        is_part_of(z, bit_w),
                        compatible(z, bit_y),
                        is_part_of(bit_x, z),
                    ),
                    bit_x == z,
                ),
            ),
        )

    def is_alternative(bit_u, bit_y, bit_w):
        """
        bit_u is a world that is the alternative that results from imposing state bit_y on
        world bit_w.
        returns a Z3 constraint
        """
        z = BitVec("alt_z", N)
        return And(
            is_world(bit_u),
            is_part_of(bit_y, bit_u),
            And(is_part_of(z, bit_u), max_compatible_part(z, bit_w, bit_y)), # REMOVABLE
        )

    # def preclude(state, sentence, eval_world):
    #     """to simulate bilateral semantics
    #     returns a Z3 constraint"""
    #     x = BitVec("preclude_x", N)
    #     # return And(
    #     #     Exists(
    #     #         x,
    #     #         And(
    #     #             extended_verify(x, sentence, eval_world),
    #     #             Not(compatible(x, state))
    #     #         )
    #     #     ),
    #     return ForAll(
    #         x,
    #         Implies(
    #             extended_verify(x, sentence, eval_world),
    #             Not(compatible(x, state))
    #         )
    #     )
    # # ),

    # def precluder_fusion(state, sentence, eval_world):
    #     x = BitVec("exclude_x", N)
    #     y = BitVec("exclude_y", N)
    #     return Or(
    #         preclude(state, sentence, eval_world),
    #         Exists(
    #             [x, y],
    #             And(
    #                 non_null_part_of(x, state),
    #                 preclude(x, sentence, eval_world),
    #                 precluder_fusion(y, sentence, eval_world),
    #                 state == fusion(x, y)
    #             )
    #         )
    #     )

    def exclude(state, sentence, eval_world):
        """to simulate bilateral semantics
        returns a Z3 constraint"""
        x = BitVec("exclude_x", N)
        y = BitVec("exclude_y", N)
        return And(
            ForAll(
                x,
                Implies(
                    # is_part_of(x, state),
                    non_null_part_of(x, state),
                    Exists( # HARD TO REMOVE
                        y,
                        And(
                            extended_verify(y, sentence, eval_world),
                            Not(compatible(x, y))
                        )
                    )
                )
            ),
            ForAll(
                x,
                Implies(
                    extended_verify(x, sentence, eval_world),
                    Exists( # HARD TO REMOVE
                        y,
                        And(
                            # is_part_of(y, state),
                            non_null_part_of(y, state),
                            Not(compatible(x, y))
                        )
                    )
                )
            )
        )

    def extended_verify(state, sentence, eval_world):
        """sentence is in prefix form. The state is the state that verifies sentence. 
        evaluate is an optional bool to evaluate something (now unused).
        returns a Z3 constraint"""
        if len(sentence) == 1:
            sentence_letter = sentence[0]
            return verify(state, sentence_letter)
        operator = sentence[0]
        non_ext_ops = [
            "Box",
            "Diamond",
            "boxright",
            "circleright",
            "leq",
            "sqsubseteq",
            "equiv",
            "preceq",
        ]
        for choice in non_ext_ops:
            if choice in operator:
                return true_at(sentence, eval_world)
        Y = sentence[1]
        if "neg" in operator:
            return extended_falsify(state, Y, eval_world)
        if "not" in operator:
            return exclude(state, Y, eval_world)
        Z = sentence[2]
        if "wedge" in operator:
            y = BitVec("ex_ver_y", N)
            z = BitVec("ex_ver_z", N)
            return And(
                    fusion(y, z) == state,
                    extended_verify(y, Y, eval_world),
                    extended_verify(z, Z, eval_world),
                )
        if "vee" in operator:
            return Or(
                extended_verify(state, Y, eval_world),
                extended_verify(state, Z, eval_world),
                extended_verify(state, ["wedge", Y, Z], eval_world),
            )
        if "leftrightarrow" in operator:
            return Or(
                extended_verify(state, ["wedge", Y, Z], eval_world),
                extended_falsify(state, ["vee", Y, Z], eval_world),
            )
        if "rightarrow" in operator:
            return Or(
                extended_falsify(state, Y, eval_world),
                extended_verify(state, Z, eval_world),
                extended_verify(state, ["wedge", ["neg", Y], Z], eval_world),
                # M: out of curiosity, what's this for?
                # B: this assumes that 'A rightarrow B' is treated like 'neg A vee B'
                # the last clause is comparable to the last clause for 'vee' but where Y is negated
            )
        raise ValueError(
            sentence,
            "Something has gone wrong in extended_falsify. "
            f"The operator {operator} in {sentence} is not a recognized operator."
        )

    def extended_falsify(state, sentence, eval_world):
        """ext_sent is in prefix form. The state is the state that falsifies ext_sent. 
        returns a Z3 constraint"""
        if len(sentence) == 1:
            return falsify(state, sentence[0])
        operator = sentence[0]
        non_ext_ops = [
            "Box",
            "Diamond",
            "boxright",
            "circleright",
            "leq",
            "sqsubseteq",
            "equiv",
            "preceq",
        ]
        for choice in non_ext_ops:
            if choice in operator:
                return false_at(sentence, eval_world)
        Y = sentence[1]
        if "neg" in operator:
            return extended_verify(state, Y, eval_world)
        if "not" in operator:
            return exclude(state, Y, eval_world)
        Z = sentence[2]
        if "wedge" in operator:
            return Or(
                extended_falsify(state, Y, eval_world),
                extended_falsify(state, Z, eval_world),
                extended_falsify(state, ["vee", Y, Z], eval_world),
            )
        y = BitVec("ex_fal_y", N)
        z = BitVec("ex_fal_z", N)
        if "vee" in operator:
            return Exists( # REMOVABLE
                [y, z],
                And(
                    state == fusion(y, z),
                    extended_falsify(y, Y, eval_world),
                    extended_falsify(z, Z, eval_world),
                ),
            )
        if "leftrightarrow" in operator:
            return Or(
                extended_verify(state, ["wedge", Y, ["neg", Z]], eval_world),
                extended_falsify(state, ["vee", Y, ["neg", Z]], eval_world),
            )
        if "rightarrow" in operator:
            return Exists( # REMOVABLE
                [y, z],
                And(
                    state == fusion(y, z),
                    extended_verify(y, Y, eval_world),
                    extended_falsify(z, Z, eval_world),
                ),
            )
        raise ValueError(
            sentence,
            "Something has gone wrong in extended_falsify. "
            f"The operator {operator} in {sentence} is not a recognized."
        )

    def true_at(sentence, eval_world):
        """sentence is a sentence in prefix notation. Eval world is the world the sentence is
        to be evaluated at (changes for counterfactuals). 
        NOTE: the true_at/false-at definitions are bilateral to accommodate the fact
        that the exhaustivity constraint is not included in the definition of props
        this should avoid the need for specific clauses for (un)negated CFs. 
        returns a Z3 constraint"""
        if len(sentence) == 1:
            sent = sentence[0]
            if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                x = BitVec("t_atom_x", N)
                return Exists(x, And(is_part_of(x, eval_world), verify(x, sent))) # REMOVABLE
        if len(sentence) == 2:
            operator = sentence[0]
            Y = sentence[1]
            if "neg" in operator or "not" in operator:
                return false_at(sentence[1], eval_world)
            if 'Box' in operator:
                u = BitVec("t_nec_u", N)
                return ForAll(u, Implies(is_world(u), true_at(sentence[1], u)))
            if 'Diamond' in operator:
                u = BitVec("t_pos_u", N)
                return Exists(u, And(is_world(u), true_at(sentence[1], u))) # REMOVABLE
        if len(sentence) == 3:
            operator = sentence[0]
            Y = sentence[1]
            Z = sentence[2]
            if "wedge" in operator:
                return And(true_at(Y, eval_world), true_at(Z, eval_world))
            if "vee" in operator:
                return Or(true_at(Y, eval_world), true_at(Z, eval_world))
            if "leftrightarrow" in operator:
                return Or(
                    And(true_at(Y, eval_world), true_at(Z, eval_world)),
                    And(false_at(Y, eval_world), false_at(Z, eval_world)),
                )
            if "rightarrow" in operator:
                return Or(false_at(Y, eval_world), true_at(Z, eval_world))
            if "leq" in operator:
                x = BitVec("t_leq_x", N)
                y = BitVec("t_leq_y", N)
                return And(
                    ForAll(
                        x,
                        Implies(
                            extended_verify(x, Y, eval_world),
                            extended_verify(x, Z, eval_world)
                        ),
                    ),
                    ForAll(
                        [x, y],
                        Implies(
                            And(
                                extended_falsify(x, Y, eval_world),
                                extended_falsify(y, Z, eval_world)
                            ),
                            extended_falsify(fusion(x, y), Z, eval_world)
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_falsify(x, Z, eval_world),
                            Exists( # HARD TO REMOVE
                                y,
                                And(
                                    extended_falsify(y, Y, eval_world),
                                    is_part_of(y, x),
                                )
                            )
                        )
                    )
                )
            if "sqsubseteq" in operator:
                x = BitVec("t_seq_x", N)
                y = BitVec("t_seq_y", N)
                return And(
                    ForAll(
                        [x, y],
                        Implies(
                            And(
                                extended_verify(x, Y, eval_world),
                                extended_verify(y, Z, eval_world)
                            ),
                            extended_verify(fusion(x, y), Z, eval_world)
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_verify(x, Z, eval_world),
                            Exists( # HARD TO REMOVE
                                y,
                                And(
                                    extended_verify(y, Y, eval_world),
                                    is_part_of(y, x),
                                )
                            )
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_falsify(x, Y, eval_world),
                            extended_falsify(x, Z, eval_world)
                        )
                    )
                )
            if "preceq" in operator:
                x = BitVec("t_peq_x", N)
                y = BitVec("t_peq_y", N)
                return And(
                    ForAll(
                        [x, y],
                        Implies(
                            And(
                                extended_verify(x, Y, eval_world),
                                extended_verify(y, Z, eval_world)
                            ),
                            extended_verify(fusion(x, y), Z, eval_world)
                        ),
                    ),
                    ForAll(
                        [x, y],
                        Implies(
                            And(
                                extended_falsify(x, Y, eval_world),
                                extended_falsify(y, Z, eval_world)
                            ),
                            extended_falsify(fusion(x, y), Z, eval_world)
                        ),
                    ),
                    # ForAll( # stronger relevance
                    #     x,
                    #     Implies(
                    #         extended_verify(x, Z, eval_world),
                    #         Exists(
                    #             y,
                    #             And(
                    #                 is_part_of(y, x),
                    #                 extended_verify(y, Y, eval_world)
                    #             )
                    #         )
                    #     ),
                    # ),
                    # ForAll(
                    #     x,
                    #     Implies(
                    #         extended_falsify(x, Z, eval_world),
                    #         Exists(
                    #             y,
                    #             And(
                    #                 is_part_of(y, x),
                    #                 extended_falsify(y, Y, eval_world)
                    #             )
                    #         )
                    #     ),
                    # ),
                )
            if "equiv" in operator:
                x = BitVec("t_id_x", N)
                y = BitVec("t_id_y", N)
                return And(
                    ForAll(
                        x,
                        Implies(
                            extended_verify(x, Y, eval_world),
                            extended_verify(x, Z, eval_world)
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_falsify(x, Y, eval_world),
                            extended_falsify(x, Z, eval_world)
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_verify(x, Z, eval_world),
                            extended_verify(x, Y, eval_world)
                        ),
                    ),
                    ForAll(
                        x,
                        Implies(
                            extended_falsify(x, Z, eval_world),
                            extended_falsify(x, Y, eval_world)
                        ),
                    )
                )
            if "boxright" in operator:
                x = BitVec("t_ncf_x", N)
                u = BitVec("t_ncf_u", N)
                return ForAll(
                    [x, u],
                    Implies(
                        And(
                            extended_verify(x, Y, eval_world),
                            is_alternative(u, x, eval_world)
                        ),
                        true_at(Z, u),
                    ),
                )
            if "circleright" in operator:
                x = BitVec("t_pcf_x", N)
                u = BitVec("t_pcf_u", N)
                return Exists( # REMOVABLE
                    [x, u],
                    And(
                        extended_verify(x, Y, eval_world),
                        is_alternative(u, x, eval_world),
                        true_at(Z, u),
                    ),
                )
        raise ValueError(
            f'No if statements triggered— true_at for {sentence} at world {eval_world}'
        )

    def false_at(sentence, eval_world):
        """X is a sentence in prefix notation, eval world is the world the sentence is to be
        evaulated at. See true_at (above) for an important note on exhaustivity.
        returns a Z3 constraint"""
        if len(sentence) == 1:
            sent = sentence[0]
            x = BitVec("f_atom_x", N)
            return Exists(x, And(is_part_of(x, eval_world), falsify(x, sent))) # REMOVABLE
        if len(sentence) == 2:
            operator = sentence[0]
            Y = sentence[1]
            if "neg" in operator or "not" in operator:
                return true_at(sentence[1], eval_world)
            if 'Box' in operator:
                u = BitVec("f_nec_u", N)
                return Exists(u, And(is_world(u), false_at(sentence[1], u))) # REMOVABLE
            if 'Diamond' in operator:
                u = BitVec("f_pos_u", N)
                return ForAll(u, Implies(is_world(u), false_at(sentence[1], u)))
        if len(sentence) == 3:
            operator = sentence[0]
            Y = sentence[1]
            Z = sentence[2]
            if "wedge" in operator:
                return Or(false_at(Y, eval_world), false_at(Z, eval_world))
            if "vee" in operator:
                return And(false_at(Y, eval_world), false_at(Z, eval_world))
            if "leftrightarrow" in operator:
                return Or(
                    And(true_at(Y, eval_world), false_at(Z, eval_world)),
                    And(false_at(Y, eval_world), true_at(Z, eval_world)),
                )
            if "rightarrow" in operator:
                return And(true_at(Y, eval_world), false_at(Z, eval_world))
            if "leq" in operator:
                x = BitVec("f_leq_x", N)
                y = BitVec("f_leq_y", N)
                return Or(
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_verify(x, Y, eval_world),
                            Not(extended_verify(x, Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        [x, y],
                        And(
                            extended_falsify(x, Y, eval_world),
                            extended_falsify(y, Z, eval_world),
                            Not(extended_falsify(fusion(x, y), Z, eval_world))
                            # z == fusion(x, y),
                            # Not(extended_falsify(z, Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_falsify(x, Z, eval_world),
                            ForAll(
                                y,
                                Implies(
                                    extended_falsify(y, Y, eval_world),
                                    Not(is_part_of(y, x)),
                                )
                            )
                        )
                    )
                )
            if "sqsubseteq" in operator:
                x = BitVec("f_seq_x", N)
                y = BitVec("f_seq_y", N)
                return Or(
                    Exists( # REMOVABLE
                        [x, y],
                        And(
                            extended_verify(x, Y, eval_world),
                            extended_verify(y, Z, eval_world),
                            Not(extended_verify(fusion(x, y), Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_verify(x, Z, eval_world),
                            ForAll(
                                y,
                                Implies(
                                    extended_verify(y, Y, eval_world),
                                    Not(is_part_of(y, x)),
                                )
                            )
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_falsify(x, Y, eval_world),
                            Not(extended_falsify(x, Z, eval_world))
                        )
                    )
                )
            if "preceq" in operator:
                x = BitVec("f_peq_x", N)
                y = BitVec("f_peq_y", N)
                return Or(
                    Exists( # REMOVABLE
                        [x, y],
                        And(
                            extended_verify(x, Y, eval_world),
                            extended_verify(y, Z, eval_world),
                            Not(extended_verify(fusion(x, y), Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        [x, y],
                        And(
                            extended_falsify(x, Y, eval_world),
                            extended_falsify(y, Z, eval_world),
                            Not(extended_falsify(fusion(x, y), Z, eval_world))
                        ),
                    )
                    # Exists( # stronger relevance
                    #     x,
                    #     And(
                    #         extended_verify(x, Z, eval_world),
                    #         ForAll(
                    #             y,
                    #             Implies(
                    #                 is_part_of(y, x),
                    #                 Not(extended_verify(y, Y, eval_world))
                    #             )
                    #         )
                    #     ),
                    # ),
                    # Exists(
                    #     x,
                    #     And(
                    #         extended_falsify(x, Z, eval_world),
                    #         ForAll(
                    #             y,
                    #             Implies(
                    #                 is_part_of(y, x),
                    #                 Not(extended_falsify(y, Y, eval_world))
                    #             )
                    #         )
                    #     ),
                    # ),
                )
            if "equiv" in operator:
                x = BitVec("f_id_x", N)
                y = BitVec("f_id_y", N)
                return Or(
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_verify(x, Y, eval_world),
                            Not(extended_verify(x, Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_falsify(x, Y, eval_world),
                            Not(extended_falsify(x, Z, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_verify(x, Z, eval_world),
                            Not(extended_verify(x, Y, eval_world))
                        ),
                    ),
                    Exists( # REMOVABLE
                        x,
                        And(
                            extended_falsify(x, Z, eval_world),
                            Not(extended_falsify(x, Y, eval_world))
                        ),
                    )
                )
            if "boxright" in operator:
                x = BitVec("f_ncf_x", N)
                u = BitVec("f_ncf_u", N)
                return Exists( # REMOVABLE
                    [x, u],
                    And(
                        extended_verify(x, Y, eval_world),
                        is_alternative(u, x, eval_world),
                        false_at(Z, u)),
                )
            if "circleright" in operator:
                x = BitVec("f_pcf_x", N)
                u = BitVec("f_pcf_u", N)
                return ForAll(
                    [x, u],
                    Implies(
                        And(
                            extended_verify(x, Y, eval_world),
                            is_alternative(u, x, eval_world)
                        ),
                        false_at(Z, u),
                    ),
                )
        raise ValueError(
            f'No if statements triggered in false_at for {sentence} at world {eval_world}'
        )

    def make_atom_prop_constraint(atom):
        """
        Input: an atomic proposition as an AtomSort (ie, NOT in prefix notation)
        atom is a proposition since its verifiers and falsifiers are closed under
        fusion respectively, and the verifiers and falsifiers for atom are
        incompatible (exclusivity). NOTE: exhaustivity crashes Z3 so left off.
        returns a Z3 constraint for the proposition atom
        """
        x = BitVec("prop_x", N)
        y = BitVec("prop_y", N)
        sent_to_prop = [
            Not(verify(0, atom)),
            Not(falsify(0, atom)),
            ForAll(
                [x, y],
                Implies(
                    And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(And(verify(x, atom), falsify(y, atom)), Not(compatible(x, y))),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(possible(x), assign(x, atom) == y),
                    And(
                        compatible(x, y),
                        Or(verify(y, atom), falsify(y, atom)),
                    ),
                ),
            ),
        ]
        return sent_to_prop

    def find_frame_constraints(main_world):
        """returns constraints that govern how states act:
        1. for any two states x and y, if y is possible and x is a part of y, then x is possible
        2. for any two states x and y, there exists a state z that is the fusion of x and y
        3. there is a state which is a world state (we call it w)
        returns a list of Z3 constraints"""
        w = main_world
        x = BitVec("frame_x", N)
        y = BitVec("frame_y", N)
        z = BitVec("frame_z", N)
        frame_constraints = [
            ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
            ForAll([x, y], Exists(z, fusion(x, y) == z)), # HARD TO REMOVE
            is_world(main_world), # w is passed in from the big outer function define_N_semantics
        ]
        return frame_constraints

    def find_prop_constraints(sentence_letters):
        """Input: a list of all sentence letters in the premises and conclusions, as returned
        by the function all_sentence_letters (i.e., a list of AtomSorts).
        Returns the a list of the Z3 constraints that each atomic proposition gets, which is
        the one defined by make_atom_prop_constraint.
        Note that all atomic propositions all get the same one, except if the atomic proposition
        is \\top, in which case it gets its own constraint that every state verifies it and none
        falsify it.
        """
        prop_constraints = []
        for sent_letter in sentence_letters:
            if 'top' in str(sent_letter):
                x = BitVec("top_x", N)
                top_constraint = ForAll(x,
                    And(
                        verify(x,sent_letter),
                        Not(falsify(x,sent_letter))
                    )
                )
                prop_constraints.append(top_constraint)
                continue # ie, make_atom_prop_constraint should never be called on '\\top'
            for constraint in make_atom_prop_constraint(sent_letter):
                prop_constraints.append(constraint)
        return prop_constraints

    def find_premise_const(prefix_premises, main_world):
        """find constraints corresponding to the input sentences
        takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
        returns a list of Z3 constraints
        used in find_all_constraints"""
        premise_constraints = []
        for premise in prefix_premises:
            premise_constraint = true_at(premise, main_world)
            premise_constraints.append(premise_constraint)
        return premise_constraints

    def find_conclusion_const(prefix_conclusions, main_world):
        """find constraints corresponding to the input sentences
        takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
        returns a list of Z3 constraints
        used in find_all_constraints"""
        conclusion_constraints = []
        for conclusion in prefix_conclusions:
            conclusion_constraint = false_at(conclusion, main_world)
            conclusion_constraints.append(conclusion_constraint)
            # conclusion_constraint = Not(true_at(conclusion, main_world))
            # M: is there a reason you chose to do it like this?
            # B: the idea was to get it to try to find models where the premises are all true and
            # the conclusions are all false. if there is no such model, we may conclude that any
            # model where the premises are true is one where at least one conclusion is true.
            # NOTE: it seems to find models where the premises are false, and similarly where the
            # conclusions are true even though these shouldn't count as models. I suspect this is
            # to do with a discrepancy between the z3 constraints and the found/printed propositions
        return conclusion_constraints

    # def find_sent_constraints(prefix_premises,prefix_conclusions):
    #     """find constraints corresponding to the input sentences
    #     takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
    #     returns a list of Z3 constraints
    #     used in find_all_constraints"""
    #     premise_constraints = []
    #     conclusion_constraints = []
    #     for premise in prefix_premises:
    #         premise_constraint = true_at(premise, w)
    #         premise_constraints.append(premise_constraint)
    #     for conclusion in prefix_conclusions:
    #         conclusion_constraint = false_at(conclusion, w)
    #         conclusion_constraints.append(conclusion_constraint)
    #     model_constraints = premise_constraints + conclusion_constraints
    #     return model_constraints

    def find_all_constraints(prefix_premises, prefix_conclusions, main_world):
        """find Z3 constraints for input sentences
        input_sents are a list of infix sentences
        returns a tuple with all Z3 constraints, for the model, the sentence letters
        (a list of AtomSorts), and the prefix_sentences (a list of lists, since prefix
        sentences are lists)
        function that is returned by the big outer function"""
        prefix_sentences = prefix_premises + prefix_conclusions
        global sentence_letters
        sentence_letters = all_sentence_letters(prefix_sentences)
        frame_constraints = find_frame_constraints(main_world)
        prop_constraints = find_prop_constraints(sentence_letters)
        premise_constraints = find_premise_const(prefix_premises, main_world)
        conclusion_constraints = find_conclusion_const(prefix_conclusions, main_world)
        return frame_constraints, prop_constraints, premise_constraints, conclusion_constraints
    
    # def find_rest_and_old_name(formula_fragment):
    #     '''
    #     formula_fragment is a str and starts AFTER the parenthesis after Exists
    #     returns a tuple of the rest of the formula and the old bv name
    #     '''
    #     old_bv_name = ''
    #     for i, char in enumerate(formula_fragment):
    #         if char == ',':
    #             return formula_fragment[i+2:-1], old_bv_name # remove ')'
    #         if char == '\t' or char == '\n': # dunno if necessary
    #             continue
    #         old_bv_name += char

    # def remove_Exists_in_univ_scope(formula):
    #     '''
    #     formula is a str
    #     returns tuple of new formula and old bv name that was the bound variable
    #     '''
    #     new_formula = ''
    #     for i, char in enumerate(formula):
    #         if formula[i:i+6] == 'Exists':
    #             rest_of_formula, old_bv_name = find_rest_and_old_name(formula[i+7:])
    #             new_formula += rest_of_formula
    #             return new_formula, old_bv_name
    #         new_formula += char

    # def ForAll(bvs, formula, exec_str=None):
    #     '''
    #     replace universal quantifier with a condition on each bitvector
    #     if exec and eval give trouble, just use the .replace method, which also worked
    #     NOTE: looking at the documentation of eval(), it looks like this is going to be
    #     much harder than I thought
    #     TODO: actually above issue was resolved. Only problem is need to get rid of existential
    #     quantifiers. Prolly do that by hand, test it works with the old ForAll, and then
    #     try the new (this) ForAll.
    #     '''
    #     sentence_letters # this doens't work rn, but this is going to be a big problem.
    #     # need to make these things all global.
    #     verify, falsify, possible, assign # have to be here to make them local for eval
    #     if exec_str:
    #         exec(exec_str)
    #     cons_list = []
    #     formula = str(formula) if not isinstance(formula, str) else formula # make formula a str
    #     current_bv = bvs if not isinstance(bvs, list) else bvs[0]
    #     temp_N = current_bv.size()
    #     num_bvs = 2 ** temp_N
    #     bv_str = str(current_bv)
    #     if (not isinstance(bvs, list)) or (isinstance(bvs, list) and len(bvs) == 1):
    #         for i in range(num_bvs):
    #             if 'Exists' in formula:
    #                 new_formula, old_bbv_name = remove_Exists_in_univ_scope(formula)
    #                 new_bbv_name = old_bbv_name+str(i)
    #                 exec(f'{new_bbv_name} = BitVec("{new_bbv_name}",{temp_N})')
    #                 formula = new_formula.replace(old_bbv_name, new_bbv_name)
    #             exec(f'{bv_str} = BitVecVal({i},{temp_N})')
    #             print(eval('dir()'))
    #             cons_list.append(eval(formula))
    #         return And(cons_list)
    #     # recursive call
    #     rem_bvs = bvs[1:]
    #     for i in range(num_bvs):
    #         exec_str = exec_str + f'\n{bv_str} = BitVecVal({i},{temp_N})' if exec_str else f'{bv_str} = BitVecVal({i},{temp_N})'
    #         cons_list.append(ForAll(rem_bvs, formula, exec_str = exec_str))
    #     return And(cons_list)

    return find_all_constraints


def solve_constraints(all_constraints): # all_constraints is a list of constraints
    """find model for the input constraints if there is any
    returns a tuple with a boolean representing if the constraints were solved or not
    and, if True, the model, if False the unsatisfiable core of the constraints"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    return (False, solver.unsat_core())
