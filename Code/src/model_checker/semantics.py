"""
contains all semantic functions
this file defines the functions needed to generate Z3 constraints from
input_sentences in infix form.
"""

from z3 import (
    sat,
    Exists,
    ForAll,
    Implies,
    Or,
    Not,
    Solver,
    And,
    BitVec,
)

from model_checker.model_definitions import all_sentence_letters

def make_constraints(verify, falsify, possible, assign, N, w):
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
            Exists(z, And(is_part_of(z, bit_u), max_compatible_part(z, bit_w, bit_y))),
        )

    def extended_verify(state, ext_sent, eval_world):
        """ext_sent is in prefix form. The state is the state that verifies ext_sent. 
        evaluate is an optional bool to evaluate something (now unused).
        returns a Z3 constraint"""
        if len(ext_sent) == 1:
            return verify(state, ext_sent[0])
        op = ext_sent[0]
        if "boxright" in op or "Box" in op or "Diamond" in op:
            return true_at(ext_sent, eval_world)
            # raise ValueError(
            #     f"\n\nThe antecedent of a counterfactual conditional must be extensional.\n"
            #     f"The sentence '{infix(ext_sent)}' is not extensional.\n"
            # )
        if "neg" in op:
            return extended_falsify(state, ext_sent[1], eval_world)
        Y = ext_sent[1]  # is a list itself
        Z = ext_sent[2]  # is a list itself
        if "wedge" in op:
            y = BitVec("ex_ver_y", N)
            z = BitVec("ex_ver_z", N)
            # if evaluate is True:
            #     return And(
            #         fusion(y, z) == state, extended_verify(y, Y), extended_verify(z, Z)
            #     )
            # had this in here for some reason. Don't remember why.
            return Exists(
                [y, z],
                And(
                    fusion(y, z) == state,
                    extended_verify(y, Y, eval_world),
                    extended_verify(z, Z, eval_world),
                ),
            )
        if "vee" in op:
            return Or(
                extended_verify(state, Y, eval_world),
                extended_verify(state, Z, eval_world),
                extended_verify(state, ["wedge", Y, Z], eval_world),
            )
        if "leftrightarrow" in op:
            return Or(
                extended_verify(state, ["wedge", Y, Z], eval_world),
                extended_falsify(state, ["vee", Y, Z], eval_world),
            )
        if "rightarrow" in op:
            return Or(
                extended_falsify(state, Y, eval_world),
                extended_verify(state, Z, eval_world),
                extended_verify(state, ["wedge", ["neg", Y], Z], eval_world),
            )
        raise ValueError(
            f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
        )

    def extended_falsify(state, ext_sent, eval_world):
        """ext_sent is in prefix form. The state is the state that falsifies ext_sent. 
        returns a Z3 constraint"""
        if len(ext_sent) == 1:
            return falsify(state, ext_sent[0])
        op = ext_sent[0]
        if "boxright" in op or "Box" in op or "Diamond" in op:
            return false_at(ext_sent, eval_world)
            # raise ValueError(
            #     f"\n\nThe antecedent of a counterfactual conditional must be extensional.\n"
            #     f"The sentence '{infix(ext_sent)}' is not extensional.\n"
            # )
        if "neg" in op:
            return extended_verify(state, ext_sent[1], eval_world)
        Y = ext_sent[1]
        Z = ext_sent[2]
        if "wedge" in op:
            return Or(
                extended_falsify(state, Y, eval_world),
                extended_falsify(state, Z, eval_world),
                extended_falsify(state, ["vee", Y, Z], eval_world),
            )
        y = BitVec("ex_fal_y", N)
        z = BitVec("ex_fal_z", N)
        # usage of these two in vee and right arrow is mutually exclusive,
        # so can define the y and z dummy bitvecs up here
        if "vee" in op:
            return Exists(
                [y, z],
                And(
                    state == fusion(y, z),
                    extended_falsify(y, Y, eval_world),
                    extended_falsify(z, Z, eval_world),
                ),
            )
        if "leftrightarrow" in op:
            return Or(
                extended_verify(state, ["wedge", Y, ["neg", Z]], eval_world),
                extended_falsify(state, ["vee", Y, ["neg", Z]], eval_world),
            )
        if "rightarrow" in op:
            return Exists(
                [y, z],
                And(
                    state == fusion(y, z),
                    extended_verify(y, Y, eval_world),
                    extended_falsify(z, Z, eval_world),
                ),
            )
        raise ValueError(
            f"Something went wrong in extended_verify in evaluating the operator {op} in [{op}, {Y}, {Z}]"
        )

    def true_at(sentence, eval_world):
        """sentence is a sentence in prefix notation. Eval world is the world the sentence is
        to be evaluated at (changes for counterfactuals). 
        NOTE: the true_at/false-at definitions are bilateral to accommodate the fact
        that the exhaustivity constraint is not included in the definition of props
        this should avoid the need for specific clauses for (un)negated CFs. 
        returns a Z3 constraint"""
        x = BitVec("t_x", N)
        u = BitVec("t_u", N)
        if len(sentence) == 1:
            sent = sentence[0]
            if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                return Exists(x, And(is_part_of(x, eval_world), verify(x, sent)))
        op = sentence[0]
        if "neg" in op:
            return false_at(sentence[1], eval_world)
        if len(sentence) == 2 and 'Box' in op:
            return ForAll(u, Implies(is_world(u), true_at(sentence[1], u)))
        if len(sentence) == 2 and 'Diamond' in op:
            return Exists(u, And(is_world(u), true_at(sentence[1], u)))
        Y = sentence[1]
        Z = sentence[2]
        if "wedge" in op:
            return And(true_at(Y, eval_world), true_at(Z, eval_world))
        if "vee" in op:
            return Or(true_at(Y, eval_world), true_at(Z, eval_world))
        if "leftrightarrow" in op:
            return Or(
                And(true_at(Y, eval_world), true_at(Z, eval_world)),
                And(false_at(Y, eval_world), false_at(Z, eval_world)),
            )
        if "rightarrow" in op:
            return Or(false_at(Y, eval_world), true_at(Z, eval_world))
        if "boxright" in op:
            return ForAll(
                [x, u],
                Implies(
                    And(extended_verify(x, Y, eval_world), is_alternative(u, x, eval_world)),
                    true_at(Z, u),
                ),
            )
        raise ValueError(f'No if statements triggered— true_at for {sentence} at world {eval_world}')

    def false_at(sentence, eval_world):
        """X is a sentence in prefix notation, eval world is the world the sentence is to be
        evaulated at. See true_at (above) for an important note on exhaustivity.
        returns a Z3 constraint"""
        x = BitVec("f_x", N)
        u = BitVec("f_u", N)
        if len(sentence) == 1:
            sent = sentence[0]
            return Exists(x, And(is_part_of(x, eval_world), falsify(x, sent)))
        op = sentence[0]
        if "neg" in op:
            return true_at(sentence[1], eval_world)
        if len(sentence) == 2 and 'Box' in op:
            # print(sentence)
            return Exists(u, And(is_world(u), false_at(sentence[1], u)))
        if len(sentence) == 2 and 'Diamond' in op:
            # print(sentence)
            return ForAll(u, Implies(is_world(u), false_at(sentence[1], u)))
        Y = sentence[1]
        Z = sentence[2]
        if "wedge" in op:
            return Or(false_at(Y, eval_world), false_at(Z, eval_world))
        if "vee" in op:
            return And(false_at(Y, eval_world), false_at(Z, eval_world))
        if "leftrightarrow" in op:
            return Or(
                And(true_at(Y, eval_world), false_at(Z, eval_world)),
                And(false_at(Y, eval_world), true_at(Z, eval_world)),
            )
        if "rightarrow" in op:
            return And(true_at(Y, eval_world), false_at(Z, eval_world))
        if "boxright" in op:
            return Exists(
                [x, u],
                And(extended_verify(x, Y, eval_world), is_alternative(u, x, eval_world), false_at(Z, u)),
            )
        raise ValueError(f'No if statements triggered in false_at for {sentence} at world {eval_world}')

    def prop_const(atom):
        """
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
            # Exists(x, non_null_verify(x, atom)),
            # Exists(y, non_null_falsify(y, atom)),
            # Exists(x, non_triv_verify(x, atom)),
            # Exists(y, non_triv_falsify(y, atom)),
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

    def find_frame_constraints():
        """returns constraints that govern how states act:
        1. for any two states x and y, if y is possible and x is a part of y, then x is possible
        2. for any two states x and y, there exists a state z that is the fusion of x and y
        3. there is a state which is a world state (we call it w)
        returns a list of Z3 constraints"""
        x = BitVec("frame_x", N)
        y = BitVec("frame_y", N)
        z = BitVec("frame_z", N)
        frame_constraints = [
            ForAll([x, y], Implies(And(possible(y), is_part_of(x, y)), possible(x))),
            ForAll([x, y], Exists(z, fusion(x, y) == z)),
            is_world(w), # w is passed in from the big outer function
        ]
        return frame_constraints

    def find_prop_constraints(sentence_letters):
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
                continue # ie, prop_const should never be called on '\\top'
            for constraint in prop_const(sent_letter):
                prop_constraints.append(constraint)
        return prop_constraints

    def find_sent_constraints(prefix_premises,prefix_conclusions):
        """find constraints corresponding to the input sentences
        takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
        returns a list of Z3 constraints
        used in find_all_constraints"""
        premise_constraints = []
        conclusion_constraints = []
        for premise in prefix_premises:
            premise_constraint = true_at(premise, w)
            premise_constraints.append(premise_constraint)
        for conclusion in prefix_conclusions:
            conclusion_constraint = false_at(conclusion, w)
            conclusion_constraints.append(conclusion_constraint)
        model_constraints = premise_constraints + conclusion_constraints
        return model_constraints

    def find_all_constraints(prefix_premises,prefix_conclusions):
        """find Z3 constraints for input sentences
        input_sents are a list of infix sentences
        returns a tuple with all Z3 constraints, for the model, the sentence letters
        (a list of AtomSorts), and the prefix_sentences (a list of lists, since prefix
        sentences are lists)
        function that is returned by the big outer function"""
        prefix_sentences = prefix_premises + prefix_conclusions
        sentence_letters = all_sentence_letters(prefix_sentences)
        frame_constraints = find_frame_constraints()
        proposition_constraints = find_prop_constraints(sentence_letters)
        sentence_constraints = find_sent_constraints(prefix_premises, prefix_conclusions)
        model_constraints = frame_constraints + proposition_constraints + sentence_constraints
        return model_constraints

    return find_all_constraints


def solve_constraints(all_constraints): # all_constraints is a list
    """find model for the input constraints if there is any
    returns a tuple with a boolean representing if the constraints were solved or not
    and, if True, the model, if False the unsatisfiable core of the constraints"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    return (False, solver.unsat_core())
