##########################
### DEFINE THE IMPORTS ###
##########################

import z3
import sys
import time


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
        'iteration_timeout': 1.0,
        'iteration_attempts': 5,
        'max_time' : 1,
        'expectation' : None,
    }
    
    # Default general settings for the exclusion theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
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
            f"h_{state, z3_set}", # function name type: string
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

    def false_at(self, sentence, eval_world):
        return z3.Not(self.true_at(sentence, eval_world))

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
        self.all_states = model_structure.all_states
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
        all_states = self.semantics.all_states
        result = set()
        for state in all_states:
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
        all_states = self.model_structure.all_states
        model = self.model_structure.z3_model
        semantics = self.semantics
        eval_world = self.eval_world
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            V = {
                bit for bit in all_states
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
        
        # Update possible states with proper Z3 boolean handling
        possible_states = []
        for state in self.all_states:
            result = evaluate(self.semantics.possible(state))
            is_possible = z3.is_true(result)
            if is_possible:
                possible_states.append(state)
        
        # Store the possible states
        self.z3_possible_states = possible_states
        
        # The null state should always be possible (semantics requirement)
        if 0 not in self.z3_possible_states:
            self.z3_possible_states.append(0)
        
        # Update world states with proper Z3 boolean handling
        self.z3_world_states = [
            state for state in self.z3_possible_states
            if z3.is_true(evaluate(self.semantics.is_world(state)))
        ]
        
        # Update relationship data with proper Z3 boolean handling
        self.z3_excludes = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.excludes(bit_x, bit_y)))
        ]
        
        self.z3_conflicts = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.conflicts(bit_x, bit_y)))
        ]
        
        self.z3_coheres = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.coheres(bit_x, bit_y)))
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
            elif bit in self.z3_world_states:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.z3_possible_states:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")

    def print_h_functions(self, output=sys.__stdout__):
        """Print the h_ function values in the model.
        
        This displays the preclusion functions mapping states to their
        corresponding values based on the actual Z3 model.
        
        Args:
            output: Output stream to write the functions to. Defaults to sys.__stdout__.
        """
        if not self.z3_model:
            return
        
        # Set up colors
        use_colors = output is sys.__stdout__
        WHITE = self.WHITE if use_colors else ""
        RESET = self.RESET if use_colors else ""
        WORLD_COLOR = self.COLORS["world"] if use_colors else ""
        POSSIBLE_COLOR = self.COLORS["possible"] if use_colors else ""
        IMPOSSIBLE_COLOR = self.COLORS["impossible"] if use_colors else ""
        
        def get_state_color(bit):
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR
                
        def should_include_state(bit):
            # Check if we should include this state based on print_impossible setting
            return bit in self.z3_possible_states or bit in self.z3_world_states or self.settings['print_impossible']
            
        print("\nFunctions", file=output)
        
        # Find all h_ functions in the model
        h_funcs = []
        for decl in self.z3_model.decls():
            if decl.name().startswith('h_'):
                h_funcs.append(decl)
        
        if not h_funcs:
            # Don't print anything if no h-functions found
            return
            
        # For each h-function, evaluate it for all states
        for func in h_funcs:
            # Create argument for the function
            arg = z3.BitVec("h_arg", self.N)
            h_func_app = func(arg)
            
            # Try to evaluate for each state
            for state in self.all_states:
                # Skip impossible states if print_impossible is False
                if not should_include_state(state):
                    continue
                    
                try:
                    # Get the corresponding output value
                    result = self.z3_model.evaluate(z3.substitute(h_func_app, (arg, state)))
                    
                    # Skip if result is not a possible state and print_impossible is False
                    if not should_include_state(result.as_long()):
                        continue
                    
                    # Format the output
                    input_state = bitvec_to_substates(state, self.N)
                    output_state = bitvec_to_substates(result.as_long(), self.N)
                    
                    # Apply colors based on state type
                    in_color = get_state_color(state)
                    out_color = get_state_color(result.as_long())
                    
                    # Print in the required format with colors
                    print(f"  {func.name()}: {in_color}{input_state}{RESET} → {out_color}{output_state}{RESET}", file=output)
                except Exception:
                    # Skip if we can't evaluate this input
                    pass

    def print_exclusion(self, output=sys.__stdout__):
        # Set up colors
        use_colors = output is sys.__stdout__
        WHITE = self.WHITE if use_colors else ""
        RESET = self.RESET if use_colors else ""
        WORLD_COLOR = self.COLORS["world"] if use_colors else ""
        POSSIBLE_COLOR = self.COLORS["possible"] if use_colors else ""
        IMPOSSIBLE_COLOR = self.COLORS["impossible"] if use_colors else ""
        
        def get_state_color(bit):
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR
                
        def should_include_state(bit):
            # Check if we should include this state based on print_impossible setting
            # Always include the null state (bit 0)
            return (bit == 0 or 
                   bit in self.z3_possible_states or 
                   bit in self.z3_world_states or 
                   self.settings['print_impossible'])
        
        # Filter and print conflicts
        z3_conflicts = getattr(self, 'z3_conflicts', [])
        filtered_conflicts = [(x, y) for x, y in z3_conflicts if should_include_state(x) and should_include_state(y)]
        if filtered_conflicts:
            print("\nConflicts", file=output)
            for bit_x, bit_y in filtered_conflicts:
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                x_state = bitvec_to_substates(bit_x, self.N)
                y_state = bitvec_to_substates(bit_y, self.N)
                print(f"  {color_x}{x_state}{RESET} conflicts with {color_y}{y_state}{RESET}", file=output)
        
        # Filter and print coherence
        z3_coheres = getattr(self, 'z3_coheres', [])
        filtered_coheres = [(x, y) for x, y in z3_coheres if should_include_state(x) and should_include_state(y)]
        if filtered_coheres:
            print("\nCoherence", file=output)
            for bit_x, bit_y in filtered_coheres:
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                x_state = bitvec_to_substates(bit_x, self.N)
                y_state = bitvec_to_substates(bit_y, self.N)
                print(f"  {color_x}{x_state}{RESET} coheres with {color_y}{y_state}{RESET}", file=output)
        
        # Filter and print exclusions
        z3_excludes = getattr(self, 'z3_excludes', [])
        filtered_excludes = [(x, y) for x, y in z3_excludes if should_include_state(x) and should_include_state(y)]
        if filtered_excludes:
            print("\nExclusion", file=output)
            for bit_x, bit_y in filtered_excludes:
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                x_state = bitvec_to_substates(bit_x, self.N)
                y_state = bitvec_to_substates(bit_y, self.N)
                print(f"  {color_x}{x_state}{RESET} excludes {color_y}{y_state}{RESET}", file=output)

        # Print the h-functions
        self.print_h_functions(output)

        # print()
        # for bit_x in self.all_states:
        #     for bit_y in self.all_states:
        #         if self.z3_model.evaluate(self.semantics.conflicts(bit_x, bit_y)):
        #             print(f"CONFLICT: {bitvec_to_substates(bit_x, self.N)} conflicts with {bitvec_to_substates(bit_y, self.N)}")
        #             for bit_u in self.all_states:
        #                 if self.z3_model.evaluate(self.semantics.is_part_of(bit_u, bit_x)):
        #                     for bit_v in self.all_states:
        #                         if self.z3_model.evaluate(self.semantics.is_part_of(bit_v, bit_y)):
        #                             if self.z3_model.evaluate(self.semantics.excludes(bit_u, bit_v)):
        #                                 print(f"EXCLUDERS: {bitvec_to_substates(bit_u, self.N)} excludes {bitvec_to_substates(bit_v, self.N)}\n")

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
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
        # Check if we actually timed out (runtime >= max_time)
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime >= self.max_time
        
        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
            
        # Print model information    
        self.print_all(self.settings, example_name, theory_name, output)
        
        # Model differences are now handled by the module.py code
        # and printed through the print_model_differences method
        
        # Print constraints if requested
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)
            
    def detect_model_differences(self, previous_structure):
        """Calculate differences between this model and a previous one.
        
        This method implements the model-specific calculation of differences,
        focusing on the aspects relevant to exclusion theory: worlds, possible states,
        exclusion relationships, and sentence letter verifications.
        
        Args:
            previous_structure: The previous model structure to compare against
            
        Returns:
            dict: Dictionary structure of differences
        """
        # Get Z3 models
        current_model = self.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize exclusion theory-specific differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "sentence_letters": {},
            "exclusion_relations": {}
        }
        
        # Get all state collections
        old_worlds = set(getattr(previous_structure, "z3_world_states", []))
        new_worlds = set(getattr(self, "z3_world_states", []))
        old_states = set(getattr(previous_structure, "z3_possible_states", []))
        new_states = set(getattr(self, "z3_possible_states", []))
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare verification for each sentence letter
        for letter in self.sentence_letters:
            old_verifiers = []
            new_verifiers = []
            
            # Check verifiers
            for state in old_states.union(new_states):
                try:
                    # For previously possible states
                    if state in old_states:
                        if z3.is_true(previous_model.evaluate(self.semantics.verifies(letter, state))):
                            old_verifiers.append(state)
                
                    # For currently possible states
                    if state in new_states:
                        if z3.is_true(current_model.evaluate(self.semantics.verifies(letter, state))):
                            new_verifiers.append(state)
                except Exception:
                    # Skip problematic states
                    pass
            
            # Only record differences if something changed
            old_verifiers_set = set(old_verifiers)
            new_verifiers_set = set(new_verifiers)
            
            added_verifiers = [state for state in new_verifiers if state not in old_verifiers_set]
            removed_verifiers = [state for state in old_verifiers if state not in new_verifiers_set]
            
            if added_verifiers or removed_verifiers:
                differences["sentence_letters"][str(letter)] = {
                    "old": old_verifiers,
                    "new": new_verifiers,
                    "verifiers": {
                        "added": added_verifiers,
                        "removed": removed_verifiers
                    }
                }
                
        # Compare exclusion relationships
        if hasattr(self.semantics, 'excludes'):
            all_states = list(old_states.union(new_states))
            for i, state1 in enumerate(all_states):
                for j, state2 in enumerate(all_states[i:], i):
                    # Skip identical states
                    if state1 == state2:
                        continue
                        
                    try:
                        # Check if exclusion relationship changed
                        old_excludes = False
                        new_excludes = False
                        
                        if state1 in old_states and state2 in old_states:
                            old_excludes = z3.is_true(previous_model.evaluate(self.semantics.excludes(state1, state2)))
                            
                        if state1 in new_states and state2 in new_states:
                            new_excludes = z3.is_true(current_model.evaluate(self.semantics.excludes(state1, state2)))
                            
                        if old_excludes != new_excludes:
                            state_pair = f"{state1},{state2}"
                            differences["exclusion_relations"][state_pair] = {
                                "old": old_excludes,
                                "new": new_excludes
                            }
                    except Exception:
                        # Skip problematic state pairs
                        pass
        
        return differences
    
    def print_model_differences(self, output=sys.stdout):
        """Display model differences if they exist.
        
        This method is called by module.py's process_example method or BaseModelIterator
        to display differences between consecutive models.
        
        Args:
            output: Output stream to write to. Defaults to sys.stdout.
        
        Returns:
            bool: True if differences were displayed, False otherwise
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return False
            
        # First, check if there are any actual differences
        differences = self.model_differences
        has_diffs = (
            differences.get('worlds', {}).get('added') or 
            differences.get('worlds', {}).get('removed') or
            differences.get('possible_states', {}).get('added') or 
            differences.get('possible_states', {}).get('removed') or
            differences.get('sentence_letters') or
            differences.get('exclusion_relations')
        )
        
        if not has_diffs:
            return False
            
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # Set up colors
        use_colors = output is sys.__stdout__
        if use_colors:
            BLUE = "\033[34m"
            CYAN = "\033[36m"
            RESET = "\033[0m"
        else:
            BLUE = ""
            CYAN = ""
            RESET = ""
        
        # World changes
        if 'worlds' in differences and (differences['worlds'].get('added') or differences['worlds'].get('removed')):
            print("World Changes:", file=output)
            
            if differences['worlds'].get('added'):
                for world in differences['worlds']['added']:
                    try:
                        # Convert BitVecRef to int if needed
                        if hasattr(world, 'as_long'):
                            world_int = world.as_long()
                        elif isinstance(world, str) and world.isdigit():
                            world_int = int(world)
                        else:
                            world_int = world
                            
                        world_str = bitvec_to_substates(world_int, self.N)
                        print(f"  + {BLUE}{world_str} (world){RESET}", file=output)
                    except Exception:
                        print(f"  + {BLUE}{world} (world){RESET}", file=output)
            
            if differences['worlds'].get('removed'):
                for world in differences['worlds']['removed']:
                    try:
                        # Convert BitVecRef to int if needed
                        if hasattr(world, 'as_long'):
                            world_int = world.as_long()
                        elif isinstance(world, str) and world.isdigit():
                            world_int = int(world)
                        else:
                            world_int = world
                            
                        world_str = bitvec_to_substates(world_int, self.N)
                        print(f"  - {BLUE}{world_str} (world){RESET}", file=output)
                    except Exception:
                        print(f"  - {BLUE}{world} (world){RESET}", file=output)
        
        # Possible state changes
        if 'possible_states' in differences and (differences['possible_states'].get('added') or differences['possible_states'].get('removed')):
            print("\nPossible State Changes:", file=output)
            
            if differences['possible_states'].get('added'):
                for state in differences['possible_states']['added']:
                    try:
                        # Convert BitVecRef to int if needed
                        if hasattr(state, 'as_long'):
                            state_int = state.as_long()
                        elif isinstance(state, str) and state.isdigit():
                            state_int = int(state)
                        else:
                            state_int = state
                            
                        state_str = bitvec_to_substates(state_int, self.N)
                        print(f"  + {CYAN}{state_str}{RESET}", file=output)
                    except Exception:
                        print(f"  + {CYAN}{state}{RESET}", file=output)
            
            if differences['possible_states'].get('removed'):
                for state in differences['possible_states']['removed']:
                    try:
                        # Convert BitVecRef to int if needed
                        if hasattr(state, 'as_long'):
                            state_int = state.as_long()
                        elif isinstance(state, str) and state.isdigit():
                            state_int = int(state)
                        else:
                            state_int = state
                            
                        state_str = bitvec_to_substates(state_int, self.N)
                        print(f"  - {CYAN}{state_str}{RESET}", file=output)
                    except Exception:
                        print(f"  - {CYAN}{state}{RESET}", file=output)
        
        # Exclusion relationship changes
        if 'exclusion_relations' in differences and differences['exclusion_relations']:
            print("\nExclusion Relationship Changes:", file=output)
            
            for pair, change in differences['exclusion_relations'].items():
                # Try to parse the state pair
                try:
                    states = pair.split(',')
                    if len(states) == 2:
                        # Convert to ints properly
                        state1 = states[0].strip()
                        state2 = states[1].strip()
                        
                        # Handle different input types
                        if hasattr(state1, 'as_long'):
                            state1_bitvec = state1.as_long()
                        elif state1.isdigit():
                            state1_bitvec = int(state1)
                        else:
                            state1_bitvec = state1
                            
                        if hasattr(state2, 'as_long'):
                            state2_bitvec = state2.as_long()
                        elif state2.isdigit():
                            state2_bitvec = int(state2)
                        else:
                            state2_bitvec = state2
                        
                        state1_str = bitvec_to_substates(state1_bitvec, self.N)
                        state2_str = bitvec_to_substates(state2_bitvec, self.N)
                        
                        if change.get('new'):
                            print(f"  {state1_str} now excludes {state2_str}", file=output)
                        else:
                            print(f"  {state1_str} no longer excludes {state2_str}", file=output)
                        continue
                except Exception as e:
                    print(f"  Error parsing state pair '{pair}': {e}", file=sys.stderr)
                
                # Fall back to simple representation
                if isinstance(change, dict) and 'old' in change and 'new' in change:
                    status = "now excludes" if change['new'] else "no longer excludes"
                    print(f"  {pair}: {status}", file=output)
                else:
                    print(f"  {pair}: changed", file=output)
        
        return True

    def save_to(self, example_name, theory_name, include_constraints, output):
        """append all elements of the model to the file provided"""
        constraints = self.model_constraints.all_constraints
        self.print_all(self.settings, example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
