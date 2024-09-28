from z3 import (
    And,
    BitVec,
    BitVecSort,
    BitVecs,
    BitVecSortRef,
    BoolSort,
    Function,
    Implies,
    Not,
    Or,
    simplify,
    substitute,
    BitVecVal,
    )

from syntax import AtomSort

from hidden_things import Operator

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

ForAll = ForAllFinite
Exists = ExistsFinite

def product(set_A, set_B):
    """set of pairwise fusions of elements in set_A and set_B"""
    product_set = set()
    for bit_a in set_A:
        for bit_b in set_B:
            bit_ab = simplify(bit_a | bit_b)
            product_set.add(bit_ab)
    return product_set

def coproduct(set_A, set_B):
    """union closed under pairwise fusion"""
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))

class Semantics:
    def __init__(self, N):
        self.N = N
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.main_world = BitVec("w", N) # B: I figured this might help users
        x, y, z = BitVecs("frame_x frame_y frame_z", N)
        self.frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            ForAll([x, y], Exists(z, self.fusion(x, y) == z)), # M: is this necessary?
            self.is_world(self.main_world),
        ]
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at
    
    def fusion(self, bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t

    def non_null_part_of(self, bit_s, bit_t):
        """bit_s verifies atom and is not the null state
        returns a Z3 constraint"""
        return And(Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = BitVec("max_x", self.N)
        return ForAll(
            x,
            Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def max_compatible_part(self, bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = BitVec("max_part", self.N)
        return And(
            self.is_part_of(bit_x, bit_w),
            self.compatible(bit_x, bit_y),
            ForAll(
                z,
                Implies(
                    And(
                        self.is_part_of(z, bit_w),
                        self.compatible(z, bit_y),
                        self.is_part_of(bit_x, z),
                    ),
                    bit_x == z,
                ),
            ),
        )

    def is_alternative(self, bit_u, bit_y, bit_w):
        """
        bit_u is a world that is the alternative that results from imposing state bit_y on
        world bit_w.
        returns a Z3 constraint
        """
        z = BitVec("alt_z", self.N)
        return And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)),
        )
    
    def true_at(self, prefix_sentence, eval_world):
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if not sent in {'\\top', '\\bot'}: # sentence letter case
            # B: it used to look like this:
            # if 'top' not in str(sent)[0]:
                x = BitVec("t_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_sentence, eval_world):
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if not sent in {'\\top', '\\bot'}: # sentence letter case
            # B: it used to look like this:
            # if 'bot' not in str(sent)[0]:
                x = BitVec("f_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent))) # REMOVABLE
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.false_at(*args, eval_world)

class Proposition:
    def proposition_constraints(atom, model_setup): # reason for model_setup is anticipating contingent
                                                    # and non_null affecting these constraints
        '''
        currently does not have contingent props. commented code (null_cons and skolem, latter of
        which was no longer needed) in addition to contingent props was deleted for space
        '''
        semantics = model_setup.semantics
        x = BitVec("prop_x", semantics.N)
        y = BitVec("prop_y", semantics.N)
        return [
            # B: these following null_constraints should be included given the
            # default values `contingent = false` and `non_null = true`.
            # we need to exclude these constraints otherwise.
            Not(semantics.verify(0, atom)), 
            Not(semantics.falsify(0, atom)),

            ForAll(
                [x, y],
                Implies(
                    And(semantics.verify(x, atom), semantics.verify(y, atom)), semantics.verify(semantics.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(semantics.falsify(x, atom), semantics.falsify(y, atom)), semantics.falsify(semantics.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(And(semantics.verify(x, atom), semantics.falsify(y, atom)), Not(semantics.compatible(x, y))),
            ),
            ForAll(
                x,
                Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        And(
                            semantics.compatible(x, y),
                            Or(semantics.verify(y, atom), semantics.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]
    
    def __init__(self, prefix_sentence, model_structure):
        self.prefix_sentence = prefix_sentence
        self.model_structure = model_structure
        self.semantics = model_structure.model_setup.semantics
        self.verifiers, self.falsifiers = self.find_verifiers_and_falsifiers()
        self.model_structure.all_propositions.add(self)
        print(f'made proposition for {prefix_sentence}')

    def __repr__(self):
        return str(self.prefix_sentence)

    def __hash__(self):
        return 0
    
    def __eq__(self, other):
        if (self.verifiers == other.verifiers and 
            self.falsifiers == other.falsifiers and 
            str(self.prefix_sentence) == str(other.prefix_sentence)):
            return True
        return False

    def find_verifiers_and_falsifiers(self):
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        sem = self.semantics
        if len(self.prefix_sentence) == 1:
            atom = self.prefix_sentence[0]
            V = {bit for bit in all_bits if model.evaluate(sem.verify(bit, atom))}
            F = {bit for bit in all_bits if model.evaluate(sem.falsify(bit, atom))}
            return V, F
        else:
            operator = self.prefix_sentence[0]
            prefix_args = self.prefix_sentence[1:]
            # instead of making new propositions no matter what, we could do a memoization
            # sort of thing where first we check if a proposition with the prefix form
            # in question has already been made—if so, it would be in the model_structure's
            # all_propositions attribute
            # this would speed things up during the creation of the ModelStructure object
            children_subprops = [Proposition(arg, self.model_structure) for arg in prefix_args]
            return operator.find_verifiers_and_falsifiers(*children_subprops)
        
    def truth_or_falsity_at_world(self, world):
        semantics = self.model_structure.model_setup.semantics
        z3_model = self.model_structure.z3_model
        for bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(bit, world)):
                return True
        return False

class AndOperator(Operator):
    """doc string place holder"""
    name = '\\wedge'
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))
    
    def find_verifiers_and_falsifiers(self, leftprop, rightprop):
        Y_V, Y_F = leftprop.find_verifiers_and_falsifiers()
        Z_V, Z_F = rightprop.find_verifiers_and_falsifiers()
        return (product(Y_V, Z_V), coproduct(Y_F, Z_F))

class OrOperator(Operator):
    """doc string place holder"""
    name = '\\vee'
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))
    
    def find_verifiers_and_falsifiers(self, leftprop, rightprop):
        Y_V, Y_F = leftprop.find_verifiers_and_falsifiers()
        Z_V, Z_F = rightprop.find_verifiers_and_falsifiers()
        return (coproduct(Y_V, Z_V), product(Y_F, Z_F))

class NegOperator(Operator):
    """doc string place holder"""
    name = '\\neg'
    arity = 1

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        print(type(self.semantics))
        return self.semantics.false_at(arg, eval_world)

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.true_at(arg, eval_world)
    
    def find_verifiers_and_falsifiers(self, argprop):
        Y_V, Y_F = argprop.find_verifiers_and_falsifiers()
        return (Y_F, Y_V)

class TopOperator(Operator):
    """doc string place holder"""
    name = '\\top'
    arity = 0

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be no constraint at all, or a trivial one

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be a constraint that cannot be satisfied
    
    def find_verifiers_and_falsifiers(argprop):
        pass

class BotOperator(Operator):
    """doc string place holder"""
    name = '\\bot'
    arity = 0

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be a constraint that cannot be satisfied

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be no constraint at all, or a trivial one
    
    def find_verifiers_and_falsifiers(argprop):
        pass
