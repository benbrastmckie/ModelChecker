"""Exact reproduction script for Defects 2 and 3 (see 05_defect2-3-reproduction.md).

Run with the temporary guard from that document applied to iterate/models.py's
build_new_model_structure, then reverted. Not part of the shipped codebase.
"""
import sys
sys.path.insert(0, "/home/benjamin/Projects/ModelChecker/code/src")
from types import SimpleNamespace
from unittest.mock import Mock
from model_checker.builder.example import BuildExample
from model_checker.theory_lib.bimodal import get_theory
from model_checker.theory_lib.bimodal.iterate import BimodalModelIterator
from model_checker.iterate.constraints import ConstraintGenerator
from model_checker.iterate.graph import IsomorphismChecker

theory = get_theory()
settings = {'back': 2, 'mid': 1, 'fwd': 2, 'max_time': 10, 'iterate': 3}
mock_module = Mock()
mock_module.semantic_theories = {"bimodal": theory}
mock_module.general_settings = settings
mock_module.raw_general_settings = settings
mock_module.module_flags = SimpleNamespace(
    contingent=False, disjoint=False, non_empty=False, non_null=False,
    print_constraints=False, save_output=False, print_impossible=False,
    print_z3=False, maximize=False,
)
example_case = [['\\Future A'], ['\\Box A'], settings]
example = BuildExample(mock_module, theory, example_case)

# Defect 2
cg = ConstraintGenerator(example)
extended = cg.create_extended_constraints([example.model_structure.z3_model])
print("Defect 2 -- create_extended_constraints for bimodal build_example:", extended)
assert extended == [], "expected an empty list (Defect 2)"

# Defect 3
iterator = BimodalModelIterator(example)
structure1 = example.model_structure
print("structure1.z3_world_states:", getattr(structure1, 'z3_world_states', 'MISSING'))

extended_constraints = cg.create_extended_constraints(iterator.found_models)
check_result = cg.check_satisfiability(extended_constraints)
print("second solve result:", check_result)
new_model = cg.get_model()
new_structure = iterator.model_builder.build_new_model_structure(new_model)
print("structure2.z3_world_states:", getattr(new_structure, 'z3_world_states', 'MISSING'))

checker = IsomorphismChecker()
is_iso, iso_model = checker.check_isomorphism(
    new_structure, new_model, [structure1], [example.model_structure.z3_model]
)
print("Defect 3 -- check_isomorphism(new_structure, ..., [structure1], ...) =", is_iso)
