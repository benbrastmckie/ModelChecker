import z3

from .model import (
    PropositionDefaults,
    SemanticDefaults,
    ModelDefaults,
)

from .utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)

from . import syntactic


##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################


class Semantics(SemanticDefaults):
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'non_empty' : False,
        'non_null' : False,
        'contingent' : False,
        'disjoint' : False,
        'max_time' : 1,
    }

    def __init__(self, N):

        # Initialize the superclass to set defaults
        super().__init__(N)

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
        self.main_world = z3.BitVec("w", N)

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )
        is_main_world = self.is_world(self.main_world)
        # TODO: make setting constraint
        # impossible_full_bit = z3.Not(self.possible(self.full_bit))

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
            # impossible_full_bit,
        ]

        # Define invalidity conditions
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return z3.And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def max_compatible_part(self, bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = z3.BitVec("max_part", self.N)
        return z3.And(
            self.is_part_of(bit_x, bit_w),
            self.compatible(bit_x, bit_y),
            ForAll(
                z,
                z3.Implies(
                    z3.And(
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
        z = z3.BitVec("alt_z", self.N)
        return z3.And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            Exists(z, z3.And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y))),
        )

    def true_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_world)

    def false_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_world)

    def extended_verify(self, state, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_world)
    
    def extended_falsify(self, state, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_world)

    def calculate_alternative_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        is_alt = model_structure.semantics.is_alternative
        eval = model_structure.z3_model.evaluate
        world_bits = model_structure.world_bits
        return {
            pw for ver in verifiers
            for pw in world_bits
            if eval(is_alt(pw, ver, eval_world))
        }

    def calculate_outcome_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        imposition = model_structure.semantics.imposition
        eval = model_structure.z3_model.evaluate
        world_bits = model_structure.world_bits
        return {
            pw for ver in verifiers
            for pw in world_bits
            if eval(imposition(ver, eval_world, pw))
        }


class ImpositionSemantics(SemanticDefaults):
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'non_empty' : False,
        'non_null' : False,
        'contingent' : False,
        'disjoint' : False,
        'max_time' : 1,
    }

    def __init__(self, N):

        # Initialize the superclass to set defaults
        super().__init__(N)

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
        self.imposition = z3.Function( # needed to encode Fine's semantics
            "imposition",
            z3.BitVecSort(N), # state imposed
            z3.BitVecSort(N), # world being imposed on
            z3.BitVecSort(N), # outcome world
            z3.BoolSort()     # bool
        )
        self.main_world = z3.BitVec("w", N)

        # Define the frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
        )
        is_main_world = self.is_world(self.main_world)
        inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        actuality = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.is_world(y)
                ),
                Exists(
                    z,
                    z3.And(
                        self.is_part_of(z, y),
                        self.imposition(x, y, z),
                    )
                )
            )
        )
        incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.imposition(self.fusion(x, u), y, z)
            )
        )
        completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_world(z)
            )
        )

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
            inclusion,
            actuality,
            incorporation,
            completeness,
        ]

        # Define invalidity conditions
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return z3.And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def true_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_world)

    def false_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_world)

    def extended_verify(self, state, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_world)
    
    def extended_falsify(self, state, sentence, eval_world):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_world)

    def calculate_outcome_worlds(self, verifiers, eval_world, model_structure):
        """Calculate alternative worlds given verifiers and eval_world."""
        imposition = model_structure.semantics.imposition
        eval = model_structure.z3_model.evaluate
        world_bits = model_structure.world_bits
        return {
            pw for ver in verifiers
            for pw in world_bits
            if eval(imposition(ver, eval_world, pw))
        }


class Proposition(PropositionDefaults):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, sentence, model_structure, eval_world='main'):

        super().__init__(sentence, model_structure)
        self.eval_world = model_structure.main_world if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
        

    def __eq__(self, other):
        return (
            self.verifiers == other.verifiers
            and self.falsifiers == other.falsifiers
            and self.name == other.name
        )

    def proposition_constraints(self, sentence_letter):
        """
        Generates Z3 constraints for a sentence letter including the classical
        constraints and optionally the non-null, contingent, and disjoint
        constraints depending on the user settings."""
        semantics = self.semantics

        def get_classical_constraints():
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", semantics.N)
            """The classical_constraints rule out truth_value gaps and gluts."""
            verifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, sentence_letter), semantics.verify(y, sentence_letter)),
                    semantics.verify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            falsifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.falsify(x, sentence_letter), semantics.falsify(y, sentence_letter)),
                    semantics.falsify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            no_glut = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, sentence_letter), semantics.falsify(y, sentence_letter)),
                    z3.Not(semantics.compatible(x, y)),
                ),
            )
            no_gap = ForAll(
                x,
                z3.Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        z3.And(
                            semantics.compatible(x, y),
                            z3.Or(semantics.verify(y, sentence_letter), semantics.falsify(y, sentence_letter)),
                        ),
                    ),
                ),
            )
            return [
                verifier_fusion_closure,
                falsifier_fusion_closure,
                no_glut,
                no_gap
            ]

        def get_non_empty_constraints():
            """The non_empty_constraints are important to avoid trivializing
            the disjoin_constraints, but are entailed by the contingent_constraints."""
            x, y = z3.BitVecs("ct_empty_x ct_empty_y", semantics.N)
            return [
                z3.Exists(
                    [x, y],
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    )
                )
            ]

        def get_non_null_constraints():
            """The non_null_constraints are important to avoid trivializing
            the disjoin_constraints, but are entailed by the contingent_constraints."""
            return [
                z3.Not(semantics.verify(0, sentence_letter)),
                z3.Not(semantics.falsify(0, sentence_letter)),
            ]

        def get_contingent_constraints():
            """The contingent_constraints entail the non_null_constraints."""
            x, y = z3.BitVecs("ct_cont_x ct_cont_y", semantics.N)
            possible_verifier = Exists(
                x,
                z3.And(semantics.possible(x), semantics.verify(x, sentence_letter))
            )
            possible_falsifier = Exists(
                y,
                z3.And(semantics.possible(y), semantics.falsify(y, sentence_letter))
            )
            return [
                possible_verifier,
                possible_falsifier,
            ]

        def get_disjoint_constraints():
            """The non_null_constraints are included in disjoin_constraints."""
            x, y, z = z3.BitVecs("dj_prop_x dj_prop_y dj_prop_z", semantics.N)
            disjoint_constraints = []
            for other_letter in self.sentence_letters:
                if other_letter is not sentence_letter:
                    other_disjoint_atom = ForAll(
                        [x, y],
                        z3.Implies(
                            z3.And(
                                semantics.non_null_part_of(x, y),
                                z3.Or(
                                    semantics.verify(y, sentence_letter),
                                    semantics.falsify(y, sentence_letter),
                                ),
                            ),
                            ForAll(
                                z,
                                z3.Implies(
                                    z3.Or(
                                        semantics.verify(z, other_letter),
                                        semantics.falsify(z, other_letter)
                                    ),
                                    z3.Not(semantics.is_part_of(x, z)),
                                )
                            )
                        )
                    )
                    disjoint_constraints.append(other_disjoint_atom)
            return disjoint_constraints


        # Collect constraints
        constraints = get_classical_constraints()
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraints())
        if self.settings['non_empty'] and not self.settings['contingent']:
            constraints.extend(get_non_empty_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
            constraints.extend(get_non_null_constraints())
        if self.settings['non_null'] and not self.settings['disjoint']:
            constraints.extend(get_non_null_constraints())
        return constraints

    def find_proposition(self):
        """takes self, returns the V, F tuple
        used in find_verifiers_and_falsifiers"""
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
            F = {
                bit for bit in all_bits
                if model.evaluate(semantics.falsify(bit, sentence_letter))
            }
            return V, F
        if operator is not None:
            return operator.find_verifiers_and_falsifiers(*arguments, eval_world)
        raise ValueError(f"Their is no proposition for {self}.")

    def truth_value_at(self, world):
        """Checks if there is a verifier or falsifier in world and not both."""
        semantics = self.model_structure.model_constraints.semantics
        z3_model = self.model_structure.z3_model
        ver_witness = None
        fal_witness = None
        exists_verifier = False
        exists_falsifier = False
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, world)):
                ver_witness = ver_bit
                exists_verifier = True
                break
        for fal_bit in self.falsifiers:
            if z3_model.evaluate(semantics.is_part_of(fal_bit, world)):
                fal_witness = fal_bit
                exists_falsifier = True
                break
        if exists_verifier == exists_falsifier:
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {bitvec_to_substates(world, self.N)} contains both:\n "
                f"  The verifier {bitvec_to_substates(ver_witness, self.N)}; and"
                f"  The falsifier {bitvec_to_substates(fal_witness, self.N)}."
            )
        return exists_verifier
    
    def print_proposition(self, eval_world, indent_num, use_colors):
        N = self.model_structure.model_constraints.semantics.N
        truth_value = self.truth_value_at(eval_world)
        world_state = bitvec_to_substates(eval_world, N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )


# TODO: fix
class ModelStructure(ModelDefaults):

    def __init__(self, model_constraints, max_time=1):

        super().__init__(model_constraints, max_time)

        # Store possible_bits, world_bits, and main_world from the Z3 model
        if not self.z3_model_status:
            self.poss_bits, self.world_bits, self.main_world = None, None, None
            return
        self.poss_bits = [
            bit
            for bit in self.all_bits
            if bool(self.z3_model.evaluate(self.semantics.possible(bit)))  # type: ignore
        ]
        self.world_bits = [
            bit
            for bit in self.poss_bits
            if bool(self.z3_model.evaluate(self.semantics.is_world(bit)))  # type: ignore
        ]
        if not self.z3_model is None:
            self.main_world = self.z3_model[self.main_world]

    def print_evaluation(self, output=sys.__stdout__):
        """print the evaluation world and all sentences letters that true/false
        in that world"""
        BLUE = ""
        RESET = ""
        main_world = self.main_world
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
        print("State Space:", file=output)
        for bit in self.all_bits:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, self.COLORS["initial"])
            elif bit in self.world_bits:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.poss_bits:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """prints states, sentence letters evaluated at the designated world and
        recursively prints each sentence and its parts"""
        model_status = self.z3_model_status
        self.print_info(model_status, default_settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
            return
