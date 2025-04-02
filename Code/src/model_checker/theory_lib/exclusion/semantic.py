##########################
### DEFINE THE IMPORTS ###
##########################

import z3
import sys
import time


try: # Try local imports first (for development)
    from src.model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
        pretty_set_print,
        int_to_binary,
    )
    from src.model_checker import model
    from src.model_checker import syntactic
except ImportError:
    from model_checker.utils import (
        ForAll,
        Exists,
        bitvec_to_substates,
        pretty_set_print,
        int_to_binary,
    )
    from model_checker import model
    from model_checker import syntactic

class ExclusionSemantics(model.SemanticDefaults):

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'possible' : False,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False, # TODO: check about falsifiers
        'disjoint' : False,
        'fusion_closure' : False,
        'iterate' : 1,
        'max_time' : 1,
        'expectation' : None,
    }

    def __init__(self, combined_settings): # TODO: 

        # Initialize the superclass to set defaults
        super().__init__(combined_settings)

        # Define the Z3 primitives
        self.verify = z3.Function(
            "verify",  # name
            z3.BitVecSort(self.N),  # first argument type: bitvector
            syntactic.AtomSort,     # second argument type: sentence letter
            z3.BoolSort(),          # return type: boolean
        )
        self.excludes = z3.Function(
            "excludes",  # name
            z3.BitVecSort(self.N),  # first argument type: bitvector
            z3.BitVecSort(self.N),  # second argument type: bitvector
            z3.BoolSort(),          # return type: boolean
        )
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world" : self.main_world
        }

        # Define frame constraints
        x, y, z = z3.BitVecs("frame_x frame_y frame_z", self.N)
        actuality = self.is_world(self.main_world)
        
        # Basic exclusion properties
        exclusion_symmetry = ForAll(
            [x, y],
            z3.Implies(
                self.excludes(x, y),
                self.excludes(y, x)
            )
        )
        
        # Null state excludes nothing
        # NOTE: adding the negation of this constraint is satisfiable and so not already entailed
        null_state = ForAll(
            x,
            z3.Not(self.excludes(self.null_state, x))
        )
        
        # Harmony between worlds and possibility
        harmony = ForAll( 
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_world(x),
                    self.coheres(x, y)
                ),
                self.possible(y)
            ),
        )
        
        # Rashomon principle
        rashomon = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(x),
                    self.possible(y),
                    self.coheres(x, y)
                ),
                self.compossible(x, y),
            ),
        )

        # Cosmopolitanism principle
        cosmopolitanism = ForAll(   # NOTE: redundant for finite models
            x,                      # since adding the negation of this is unsat
            z3.Implies(             # there is no need to impose cosmopolitanism  
                self.possible(x),   # it has been included for clarity
                Exists(
                    y,
                    z3.And(
                        self.is_world(y),
                        self.is_part_of(x, y)
                    )
                )
            )
        )

        excluders = ForAll(
            x,
            z3.Implies(
                x != self.null_state,
                Exists(
                    y,
                    self.excludes(y, x)
                )
            )
        )

        partial_excluders = ForAll(
            x,
            z3.Implies(
                x != self.null_state,
                Exists(
                    [y, z],
                    z3.And(
                        self.is_part_of(y, x),
                        self.excludes(z, y)
                    )
                )
            )
        )

        # NOTE: used to prove that the null_state is always possible
        impossible_null = z3.Not(self.possible(self.null_state))
        

        # Set frame constraints
        self.frame_constraints = [
            # Core constraints
            actuality,
            exclusion_symmetry,

            # Optional complex constraints
            harmony,
            rashomon,   # guards against emergent impossibility (pg 538)

            # Additional constraints
            null_state,
            # excluders,
            # partial_excluders,
        ]

        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point["world"])
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point["world"])

    # # TODO: this has to be the problem but looks find
    # def conflicts(self, bit_e1, bit_e2):
    #     f1, f2 = z3.BitVecs("f1 f2", self.N)
    #     return z3.And(
    #         self.is_part_of(f1, bit_e1),
    #         self.is_part_of(f2, bit_e2),
    #         self.excludes(f1, f2),
    #     )

    # TODO: this has to be the problem but looks find
    def conflicts(self, bit_e1, bit_e2):
        f1, f2 = z3.BitVecs("f1 f2", self.N)
        return Exists(
            [f1, f2],
            z3.And(
                self.is_part_of(f1, bit_e1),
                self.is_part_of(f2, bit_e2),
                self.excludes(f1, f2),
            ),
        )

    def coheres(self, bit_e1, bit_e2):
        return z3.Not(self.conflicts(bit_e1, bit_e2))

    def possible(self, bit_e):
        return self.coheres(bit_e, bit_e)

    def compossible(self, bit_e1, bit_e2):
        return self.possible(self.fusion(bit_e1, bit_e2))

    # B: compossible => coheres but not vice versa
    # would they be equivalent if the following constraint were added:
    # (CON_REF) if x and y are parts of s that exclude each other, then s excludes s

    def is_world(self, bit_s):
        """
        Determines if a state is a world by checking if it is possible and maximal.
        A state is maximal if it has no proper extension that is possible.

        Args:
            bit_s: BitVec representing the state to check

        Returns:
            z3.BoolRef: Formula that is true iff bit_s is a world
        """
        m = z3.BitVec("m", self.N)
        return z3.And(
            self.possible(bit_s),
            z3.Not(
                Exists(
                    m,
                    z3.And(
                        self.is_proper_part_of(bit_s, m),
                        self.possible(m)
                    )
                )
            )
        )

    def necessary(self, bit_e1):
        x = z3.BitVec("nec_x", self.N)
        return ForAll(x, z3.Implies(self.possible(x), self.compossible(bit_e1, x)))

    def collectively_excludes(self, bit_s, set_P):
        return self.excludes(bit_s, self.total_fusion(set_P))

    def individually_excludes(self, bit_s, set_P):
        sub_s, p = z3.BitVecs("sub_s p", self.N)
        P = self.z3_set(set_P, self.N)
        cond_a = Exists(
            [sub_s, p],
            z3.And(self.is_part_of(sub_s, bit_s), P[p], self.excludes(sub_s, p)),
        )
        # Sigma is upper bound on excluders of set P
        Sigma = z3.BitVec(str(set_P), self.N)
        x, y, z, p = z3.BitVecs("x y z p", self.N)
        Sigma_UB = ForAll(
            x,
            z3.Implies(
                Exists(
                    p,
                    z3.And(
                        P[p],
                        self.excludes(x, p)
                    )
                ),
                self.is_part_of(x, Sigma)
            ),
        )
        # Sigma is the least upper bound on excluders of set P
        Sigma_LUB = ForAll(
            z,
            z3.Implies(
                ForAll(
                    y,
                    z3.Implies(
                        Exists(
                            p,
                            z3.And(
                                P[p],
                                self.excludes(y, p)
                            )
                        ),
                        self.is_part_of(y, z),
                    ),
                ),
                z == Sigma
            ),
        )

        return z3.And(
            cond_a,
            Sigma_UB,
            Sigma_LUB,
            self.is_part_of(bit_s, Sigma)
        )

    def emergently_excludes(self, bit_s, set_P):
        return z3.And(
            self.collectively_excludes(bit_s, set_P),
            z3.Not(self.individually_excludes(bit_s, set_P)),
        )

    def precludes(self, state, z3_set):
        """
        Determines if a state precludes a set of states by finding a function h
        that maps each state in set_S to a part of some state such that for each
        state f in set_S, h(f) excludes some part of f.
    
        Args:
            state: BitVec representing the state to check
            set_S: Set of BitVecs representing the states to check against
    
        Returns:
            z3.BoolRef: Formula that is true iff state precludes set_S, meaning there exists a function h and state s such that:
                1. For all x in set_S, h(x) is part of s
                2. s is the smallest state satisfying condition 1
                3. For all f in set_S, h(f) excludes some part u of f
        """
        h = z3.Function(
            f"h_{(state, z3_set)}*", # function name type: string
            z3.BitVecSort(self.N),  # argument type: bitvector
            z3.BitVecSort(self.N)   # return type: bitvector
        )

        x, y, z, u, v = z3.BitVecs("x y z u v", self.N)
        return z3.And(
            ForAll( # 1. for every extended_verifiers x of the argument, there 
                x,  #    is some part y of x where h(x) excludes y                                    
                z3.Implies(
                    z3_set[x],
                    Exists(
                        y,
                        z3.And(
                            self.is_part_of(y, x),
                            self.excludes(h(x), y)
                        )
                    )
                )
            ),
            ForAll( # 2. h(z) is a part of the state for all extended_verifiers z of the argument
                z,
                z3.Implies(
                    z3_set[z],
                    self.is_part_of(h(z), state),
                )
            ),
            ForAll( # 3. the state is the smallest state to satisfy condition 2
                u,
                z3.Implies(
                    ForAll(
                        v,
                        z3.Implies(
                            z3_set[v],
                            self.is_part_of(h(v), state)
                        )
                    ),
                    self.is_part_of(state, u)
                )
            )
        )

    def occurs(self, bit_s):
        return self.is_part_of(bit_s, self.main_world)
    
    # TODO: should this be eval_point?
    def true_at(self, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(
                x,
                z3.And(
                    self.is_part_of(x, eval_world),
                    self.verify(x, sentence_letter)
                )
            )
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_world)

    def false_at(self, sentence, eval_point):
        return z3.Not(self.true_at(sentence, eval_point))

    def extended_verify(self, state, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_world)


class UnilateralProposition(model.PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence_obj, model_structure, eval_world='main'):
        """TODO"""

        super().__init__(sentence_obj, model_structure)

        self.z3_model = model_structure.z3_model
        self.eval_world = model_structure.main_point["world"] if eval_world == 'main' else eval_world
        self.all_bits = model_structure.all_bits
        self.verifiers = self.find_proposition()
        self.precluders = self.find_precluders(self.verifiers)

    def __eq__(self, other):
        return (self.verifiers == other.verifiers)

    def __repr__(self):
        N = self.model_structure.model_constraints.semantics.N
        possible = self.model_structure.model_constraints.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
            if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        }
        # NOTE: I left this b/c I think it may make sense to add falsifiers
        # these would be defined as the exact excluders
        # if isinstance(self.falsifiers, set): # because default is an empty list
        #     fal_states = {
        #         bitvec_to_substates(bit, N)
        #         for bit in self.falsifiers
        #         if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        #     }
        #     return f"< {pretty_set_print(ver_states)}, {pretty_set_print(fal_states)} >"
        return pretty_set_print(ver_states)

    def find_precluders(self, py_verifier_set):
        z3_verifier_set = self.semantics.z3_set(py_verifier_set, self.N)
        precludes = self.semantics.precludes
        all_bits = self.semantics.all_bits
        result = set()
        for state in all_bits:
            preclude_formula = precludes(state, z3_verifier_set)
            preclude_result = self.z3_model.evaluate(preclude_formula)
            # Check if the evaluated result is True
            if preclude_result == True:
                result.add(state)
        return result

    def proposition_constraints(self, sentence_letter):
        """
        Generates Z3 constraints for a sentence letter including the classical
        constraints and optionally the non-null, contingent, and disjoint
        constraints depending on the user settings."""

        semantics = self.semantics
        N = semantics.N

        def get_fusion_closure_constraint():
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", N)
            """The classical_constraints rule out truth_value gaps and gluts."""
            verifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, sentence_letter), semantics.verify(y, sentence_letter)),
                    semantics.verify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            return [verifier_fusion_closure]

        def get_non_empty_constraints():
            """The non_empty_constraints are important to avoid trivializing
            the disjoin_constraints, but are entailed by the contingent_constraints."""
            x = z3.BitVec("ct_empty_x", N)
            return [
                z3.Exists(
                    x,
                    semantics.verify(x, sentence_letter)
                )
            ]

        def get_non_null_constraints():
            """The non_null_constraints are important to avoid trivializing
            the disjoin_constraints, but are entailed by the contingent_constraints."""
            return [z3.Not(semantics.verify(0, sentence_letter))]

        def get_possible_constraints():
            """The possible_constraint entail the non_null_constraints."""
            x = z3.BitVec("ps_prop_x", N)
            possible_verifier = Exists(
                x,
                z3.And(
                    semantics.possible(x),
                    semantics.verify(x, sentence_letter)
                )
            )
            return [possible_verifier]

        def get_contingent_constraint():
            """The contingent_constraint entail the possible_constraint."""

            # Abbreviations
            extended_verify = semantics.extended_verify
            excludes = semantics.excludes
            is_part_of = semantics.is_part_of

            # NOTE: that Z3 can introduce arbitrary functions demonstrates its expressive power
            h = z3.Function(
                f"h_{sentence_letter}",   # function name
                z3.BitVecSort(N),           # bitvector argument type
                z3.BitVecSort(N)            # bitvector return type
            )

            w, m, x, y, z, u, v = z3.BitVecs("w m x y z u v", N)

            possibly_true = Exists(
                w,
                z3.And(
                    semantics.possible(w),
                    semantics.verify(w, sentence_letter)
                )
            )
            possibly_false = Exists(
                m,
                z3.And(
                    ForAll( # 1. for every extended_verifiers x of the argument, there 
                        x,  #    is some part y of x where h(x) excludes y                                    
                        z3.Implies(
                            semantics.verify(x, sentence_letter), # member of sentence_letter's set of verifiers
                            Exists(
                                y,
                                z3.And(
                                    is_part_of(y, x),
                                    excludes(h(x), y)
                                )
                            )
                        )
                    ),
                    ForAll( # 2. h(z) is a part of the state for all extended_verifiers z of the sentence_letter
                        z,
                        z3.Implies(
                            semantics.verify(z, sentence_letter),
                            is_part_of(h(z), m),
                        )
                    ),
                    ForAll( # 3. the state is the smallest state to satisfy condition 2
                        u,
                        z3.Implies(
                            ForAll(
                                v,
                                z3.Implies(
                                    semantics.verify(v, sentence_letter),
                                    is_part_of(h(v), m)
                                )
                            ),
                            is_part_of(m, u)
                        )
                    )
                )
            )
            return [possibly_true, possibly_false]

        def get_disjoint_constraints():
            """The non_null_constraints are included in disjoin_constraints."""
            x, y, z = z3.BitVecs("dj_prop_x dj_prop_y dj_prop_z", N)
            disjoint_constraints = []
            for other_letter in self.sentence_letters:
                if other_letter is not sentence_letter:
                    other_disjoint_atom = ForAll(
                        [x, y],
                        z3.Implies(
                            z3.And(
                                semantics.non_null_part_of(x, y),
                                semantics.verify(y, sentence_letter),
                            ),
                            ForAll(
                                z,
                                z3.Implies(
                                    semantics.verify(z, other_letter),
                                    z3.Not(semantics.is_part_of(x, z)),
                                )
                            )
                        )
                    )
                    disjoint_constraints.append(other_disjoint_atom)
            return disjoint_constraints

        # Collect constraints
        constraints = []
        non_empty_needed = True
        non_null_needed = True
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraint())
            non_empty_needed = False
        if self.settings['possible'] and not self.settings['contingent']:
            constraints.extend(get_possible_constraints())
            non_empty_needed = False
        if self.settings['non_empty'] and non_empty_needed:
            constraints.extend(get_non_empty_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
            constraints.extend(get_non_null_constraints())
            non_null_needed = False
        if self.settings['non_null'] and non_null_needed:
            constraints.extend(get_non_null_constraints())
        if self.settings['fusion_closure']:
            constraints.extend(get_fusion_closure_constraint())
        return constraints

    def find_proposition(self):
        """takes self, returns the V, F tuple
        used in find_verifiers"""
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        semantics = self.semantics
        eval_world = self.eval_world
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            V = {
                bit for bit in all_bits
                if model.evaluate(semantics.verify(bit, sentence_letter))
            }
            return V
        if operator is not None:
            return operator.find_verifiers(*arguments, eval_world)
        raise ValueError(f"Their is no proposition for {self.name}.")

    def truth_value_at(self, eval_world):
        """Checks if there is a verifier in world."""
        semantics = self.model_structure.semantics
        z3_model = self.model_structure.z3_model
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, eval_world)):
                return True
        return False

    def print_proposition(self, eval_point, indent_num, use_colors):
        eval_world = eval_point["world"]
        N = self.model_structure.semantics.N
        truth_value = self.truth_value_at(eval_world)
        world_state = bitvec_to_substates(eval_world, N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )

class ExclusionStructure(model.ModelDefaults):

    def __init__(self, model_constraints, combined_settings):
        """Initialize ModelStructure with model constraints and optional max time.
        
        Args:
            model_constraints: ModelConstraints object containing all constraints
            max_time: Maximum time in seconds to allow for solving. Defaults to 1.
        """
        if not isinstance(model_constraints, model.ModelConstraints):
            raise TypeError(
                f"Expected model_constraints to be a ModelConstraints object, got {type(model_constraints)}. "
                "Make sure you're passing the correct model_constraints object."
            )

        super().__init__(model_constraints, combined_settings)

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self._update_model_structure(self.z3_model)

    def _update_model_structure(self, z3_model):
        evaluate = z3_model.evaluate
        self.main_world = self.main_point["world"]
        self.main_point["world"] = z3_model[self.main_world]
        self.z3_poss_bits = [
            bit
            for bit in self.all_states
            if evaluate(self.semantics.possible(bit))
        ]
        self.z3_world_bits = [
            bit
            for bit in self.all_states
            if evaluate(self.semantics.is_world(bit))
        ]
        self.z3_excludes = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if evaluate(self.semantics.excludes(bit_x, bit_y))
        ]
        self.z3_conflicts = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if evaluate(self.semantics.conflicts(bit_x, bit_y))
        ]
        self.z3_coheres = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if evaluate(self.semantics.coheres(bit_x, bit_y))
        ]

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        BLUE = ""
        RESET = ""
        main_world = self.main_point["world"]
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N)}{RESET}\n",
            file=output,
        )

    def print_states(self, output=sys.__stdout__):
        """Print all fusions of atomic states in the model."""

        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )
        
        def format_state(bin_rep, state, color, label=""):
            """Helper function to format and print a state."""
            label_str = f" ({label})" if label else ""
            use_colors = output is sys.__stdout__
            if use_colors:
                print(f"  {self.WHITE}{bin_rep} = {color}{state}{label_str}{self.RESET}", file=output)
            else:
                print(f"  {bin_rep} = {state}{label_str}", file=output)
        
        # Print formatted state space
        print("State Space", file=output)
        for bit in self.all_states:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, self.COLORS["initial"])
            elif bit in self.z3_world_bits:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.z3_poss_bits:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")

    def print_exclusion(self, output=sys.__stdout__):
        print("\nConflicts") if self.z3_conflicts else None
        for bit_x, bit_y in self.z3_conflicts:
            print(f"  {bitvec_to_substates(bit_x, self.N)} conflicts with {bitvec_to_substates(bit_y, self.N)}")
        print("\nCoherence") if self.z3_coheres else None
        for bit_x, bit_y in self.z3_coheres:
            print(f"  {bitvec_to_substates(bit_x, self.N)} coheres with {bitvec_to_substates(bit_y, self.N)}")
        print("\nExclusion") if self.z3_excludes else None
        for bit_x, bit_y in self.z3_excludes:
            print(f"  {bitvec_to_substates(bit_x, self.N)} excludes {bitvec_to_substates(bit_y, self.N)}")

        # Print all h functions from the model
        if self.z3_model:
            print("\nFunctions")
            for decl in self.z3_model.decls():
                if decl.name().startswith('h_'):
                    # Create a BitVec for the argument
                    arg = z3.BitVec("h_arg", self.N)
                    # Create the function application with the argument
                    h_func_app = decl(arg)
                    for bit_x in self.all_states:
                        try:
                            # Evaluate by substituting the actual bit value
                            h_val = self.z3_model.evaluate(z3.substitute(h_func_app, (arg, bit_x)))
                            print(f"  {decl.name()}: {bitvec_to_substates(bit_x, self.N)} → {bitvec_to_substates(h_val, self.N)}")
                        except Exception as e:
                            continue

        # print()
        # for bit_x in self.all_bits:
        #     for bit_y in self.all_bits:
        #         if self.z3_model.evaluate(self.semantics.conflicts(bit_x, bit_y)):
        #             print(f"CONFLICT: {bitvec_to_substates(bit_x, self.N)} conflicts with {bitvec_to_substates(bit_y, self.N)}")
        #             for bit_u in self.all_bits:
        #                 if self.z3_model.evaluate(self.semantics.is_part_of(bit_u, bit_x)):
        #                     for bit_v in self.all_bits:
        #                         if self.z3_model.evaluate(self.semantics.is_part_of(bit_v, bit_y)):
        #                             if self.z3_model.evaluate(self.semantics.excludes(bit_u, bit_v)):
        #                                 print(f"EXCLUDERS: {bitvec_to_substates(bit_u, self.N)} excludes {bitvec_to_substates(bit_v, self.N)}\n")

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        model_status = self.z3_model_status
        self.print_info(model_status, default_settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_exclusion(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """append all elements of the model to the file provided
        
        Args:
            print_constraints: Whether to print constraints. Defaults to value in settings.
            output: Output stream to print to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
        if self.timeout:
            print(f"TIMEOUT: {self.timeout}")
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
            return
        self.print_all(default_settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(self, example_name, theory_name, include_constraints, output):
        """append all elements of the model to the file provided"""
        constraints = self.model_constraints.all_constraints
        self.print_all(example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
