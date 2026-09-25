"""Scratch probe: per-theory live iterate:3 baseline + defect reproductions for the
shared iterator is_world assumption fix. Not part of the shipped codebase -- run
manually, output captured to specs baselines/.
"""
import sys
import traceback
from types import SimpleNamespace
from unittest.mock import Mock

sys.path.insert(0, "/home/benjamin/Projects/ModelChecker/code/src")

from model_checker.builder.example import BuildExample


def make_module(semantic_theory, name, general_settings):
    mock_module = Mock()
    mock_module.semantic_theories = {name: semantic_theory}
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    return mock_module


def run_theory(theory_name, semantic_theory, premises, conclusions, settings, iterator_cls):
    general_settings = dict(settings)
    general_settings['iterate'] = 3
    general_settings.setdefault('max_time', 10)
    mock_module = make_module(semantic_theory, theory_name, general_settings)
    example_case = [premises, conclusions, general_settings]
    example = BuildExample(mock_module, semantic_theory, example_case)
    iterator = iterator_cls(example)
    structures = list(iterator.iterate_generator())
    print(f"=== {theory_name} ===")
    print(f"models yielded (after first): {len(structures)}")
    print(f"total model_structures (incl. first): {len(iterator.model_structures)}")
    print(f"checked_model_count: {iterator.checked_model_count}")
    print(f"isomorphic_model_count: {iterator.isomorphic_model_count}")
    print()


def probe_logos():
    from model_checker.theory_lib.logos import LogosOperatorRegistry, LogosModelIterator, get_theory
    registry = LogosOperatorRegistry()
    registry.load_subtheories(['extensional'])
    semantic_theory = get_theory()
    semantic_theory["operators"] = registry.get_operators()
    settings = {
        'N': 4, 'contingent': True, 'non_null': True, 'non_empty': True,
        'disjoint': False, 'max_time': 10,
    }
    run_theory("logos", semantic_theory, ['B', '(A \\rightarrow B)'], ['A'], settings, LogosModelIterator)


def probe_imposition():
    from model_checker.theory_lib.imposition import get_theory, ImpositionModelIterator
    semantic_theory = get_theory()
    settings = {
        'N': 3, 'contingent': False, 'non_null': True, 'non_empty': True,
        'disjoint': False, 'max_time': 10,
    }
    run_theory(
        "imposition", semantic_theory,
        ['\\neg A', '(A \\diamondright C)', '(A \\boxright C)'],
        ['((A \\wedge B) \\boxright C)'], settings, ImpositionModelIterator,
    )


def probe_exclusion():
    from model_checker.theory_lib.exclusion import get_theory, ExclusionModelIterator
    semantic_theory = get_theory()
    settings = {
        'N': 3, 'contingent': False, 'non_null': True, 'non_empty': True,
        'disjoint': False, 'max_time': 10,
    }
    run_theory(
        "exclusion", semantic_theory,
        ['(\\neg A \\vee \\neg B)'], ['\\neg (A \\wedge B)'], settings, ExclusionModelIterator,
    )


def probe_bimodal(defect1=True):
    from model_checker.theory_lib.bimodal import get_theory
    from model_checker.theory_lib.bimodal.iterate import BimodalModelIterator
    theory = get_theory()
    settings = {'back': 2, 'mid': 1, 'fwd': 2, 'max_time': 10}
    if defect1:
        run_theory("bimodal", theory, ['\\Future A'], ['\\Box A'], settings, BimodalModelIterator)
    else:
        return theory, settings


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("all", "logos"):
        try:
            probe_logos()
        except Exception:
            print("logos FAILED"); traceback.print_exc()
    if what in ("all", "imposition"):
        try:
            probe_imposition()
        except Exception:
            print("imposition FAILED"); traceback.print_exc()
    if what in ("all", "exclusion"):
        try:
            probe_exclusion()
        except Exception:
            print("exclusion FAILED"); traceback.print_exc()
    if what in ("all", "bimodal"):
        try:
            probe_bimodal()
        except Exception:
            print("bimodal FAILED (expected -- Defect 1)")
            traceback.print_exc()
