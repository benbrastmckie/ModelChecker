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

from syntax import AtomSort, find_operator

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

def Def(arg1, arg2):
    return And(Implies(arg1, arg2), Implies(arg2, arg1))

class Semantics:
    def __init__(self, N):
        self.N = N
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.main_world = BitVec("w", N) # B: I figured this might help users
        x, y, z = BitVecs("frame_x frame_y frame_z", N)
        # u, v, w = BitVecs("frame_u, frame_v, frame_w", N)
        # self.fusion = Function("fusion", BitVecSort(N), BitVecSort(N), BitVecSort(N))
        # self.fusion_constraint = ForAll([x,y], self.fusion(x,y) == x | y)

        # self.is_part_of = Function("is_part_of", BitVecSort(N), BitVecSort(N), BoolSort())
        # self.is_part_of_constraint = ForAll([x,y], Def(self.is_part_of(x,y), self.fusion(x, y) == y))

        # self.compatible = Function("compatible", BitVecSort(N), BitVecSort(N), BoolSort())
        # self.compatible_constraint = ForAll([x,y], Def(self.compatible(x,y), self.possible(self.fusion(x, y))))

        # self.maximal = Function("maximal", BitVecSort(N), BoolSort())
        # self.maximal_constraint = ForAll(x, Def(self.maximal(x), ForAll(y, Implies(self.compatible(y,x), self.is_part_of(y,x)))))

        # # could reduce if we somehow restricted the domain to possible bits
        # self.is_world = Function("is_world", BitVecSort(N), BoolSort())
        # self.is_world_constraint = ForAll(x, Def(self.is_world(x), And(self.possible(x), self.maximal(x),)))

        # # this constraints takes a lot of time. Any way to restrict the domain?
        # self.max_compatible_part = Function("max_compatible_part", BitVecSort(N), BitVecSort(N), BitVecSort(N), BoolSort())
        # self.max_compatible_part_constraint = ForAll([x,w,y], 
        #                                              Def(self.max_compatible_part(x,w,y),
        #                                                  And(self.is_part_of(x, w), self.compatible(x, y),
        #                                                     ForAll(
        #                                                         z,
        #                                                         Implies(
        #                                                             And(
        #                                                                 self.is_part_of(z, w),
        #                                                                 self.compatible(z, y),
        #                                                                 self.is_part_of(x, z),
        #                                                             ),
        #                                                             x == z,
        #                                                         ),
        #                                                     ),
        #                                                 )))
        
        # # this constraints takes a lot of time. Any way to restrict the domain?
        # self.is_alternative = Function("is_alternative", BitVecSort(N), BitVecSort(N), BitVecSort(N), BoolSort())
        # self.is_alternative_constraint = ForAll([u,y,w], Def(self.is_alternative(u,w,y), 
        #                                                      And(self.is_world(u), self.is_part_of(y, u),
        #                                                         And(self.is_part_of(z, u), self.max_compatible_part(z, w, y)),
        #                                                         )))
        # self.function_constraints = [self.fusion_constraint, self.is_part_of_constraint, 
        #                              self.compatible_constraint, self.maximal_constraint, 
        #                              self.is_world_constraint, 
        #                             self.max_compatible_part_constraint, 
        #                              self.is_alternative_constraint
        #                              ]
        # # with this approach, the extension of every function is actually explicitly saved.
        # # and, this is actually a bad model of what the functions actually are—e.g. is_alternative
        # # should not have its first or third arguments be anything other than worlds—if they aren't
        # # worlds, the function should not be applied and constraint not even considered
        # # (arguably it should crash). 
        # # If we can instead se the evaluate method of ModelRef objects to pass in Z3 constraints,
        # # and then build verifiers/falsifiers/alt worlds/etc that way, 
        self.frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            # ForAll([x, y], Exists(z, self.fusion(x, y) == z)), # is this necessary?
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
        z = BitVec("alt_z", N)
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

    # B: this should go in the Proposition class which will need to be passed to ModelSetup to get
    # for getting the model_constraints.
    def find_model_constraints(self, atom):
        '''
        currently does not have contingent props. commented code (null_cons and skolem, latter of
        which was no longer needed) in addition to contingent props was deleted for space
        '''
        x = BitVec("prop_x", self.N)
        y = BitVec("prop_y", self.N)
        return [
            # B: these following null_constraints should be included given the
            # default values `contingent = false` and `non_null = true`.
            # we need to exclude these constraints otherwise.
            Not(self.verify(0, atom)), 
            Not(self.falsify(0, atom)),

            ForAll(
                [x, y],
                Implies(
                    And(self.verify(x, atom), self.verify(y, atom)), self.verify(self.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(self.falsify(x, atom), self.falsify(y, atom)), self.falsify(self.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(And(self.verify(x, atom), self.falsify(y, atom)), Not(self.compatible(x, y))),
            ),
            ForAll(
                x,
                Implies(
                    self.possible(x),
                    Exists(
                        y,
                        And(
                            self.compatible(x, y),
                            Or(self.verify(y, atom), self.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]

class Proposition:
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
        ms = self.model_structure
        model = self.model_structure.z3_model
        sem = self.semantics
        if len(self.prefix_sentence) == 1:
            atom = self.prefix_sentence[0]
            print(self.semantics.verify(3, atom))
            V = {bit for bit in ms.all_bits if model.evaluate(sem.verify(bit, atom))}
            F = {bit for bit in ms.all_bits if model.evaluate(sem.falsify(bit, atom))}
            return V, F
        else:
            operator = self.prefix_sentence[0]
            prefix_args = self.prefix_sentence[1:]
            # instead of making new propositions no matter what, we could do a memoization
            # sort of thing where first we check if a proposition with the prefix form
            # in question has already been made—if so, it would be in the model_structure's
            # all_propositions attribute
            children_subprops = [Proposition(arg, self.model_structure) for arg in prefix_args]
            return operator.find_verifiers_and_falsifiers(*children_subprops)
        
    def truth_or_falsity_at_world(self, world, model_structure):
        semantics = model_structure.model_setup.semantics
        z3_model = model_structure.z3_model
        # Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        for bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(bit, world)):
                return True
        return False

# TODO: this class could be hidden later
class Operator:

    # B: I added this to fix the linter complaints... let me know if this seems right
    def __init__(self, name=None, arity=None):
        self.name = name
        self.arity = arity

    def __str__(self):
        return self.name if self.name else "Unnamed Operator"
        # B: I added the above in place of the below
        # return self.name # B: Instance of 'Operator' has no 'name' member
    
    def __repr__(self):
        return self.name if self.name else "Unnamed Operator"

    def __eq__(self, other):
        if isinstance(other, Operator):
            return self.name == other.name and self.arity == other.arity
        return False
    # B: I added the above in place of the below
    # def __eq__(self, other): # M: currently unused but may be nice to have
    #     if self.name == other.name and self.arity == other.arity: # B: Attribute 'arity' is unknown
    #         return True
    #     return False

class AndOperator(Operator):
    """doc string place holder"""

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 2
        self.name = '\\wedge'

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

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 2
        self.name = '\\vee'

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

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 1
        self.name = '\\neg'

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

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 0
        self.name = '\\top'

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

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 0
        self.name = '\\bot'

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be a constraint that cannot be satisfied

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return # B: we want this to be no constraint at all, or a trivial one
    
    def find_verifiers_and_falsifiers(argprop):
        pass
