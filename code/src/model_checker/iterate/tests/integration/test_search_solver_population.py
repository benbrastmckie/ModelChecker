"""Live, non-mocked regression coverage for the persistent search-solver population
defect documented in `iterate/constraints.py`'s `ConstraintGenerator.
_ensure_original_constraints_in_solver`.

Root cause: `ConstraintGenerator._create_persistent_solver` (`iterate/constraints.py`)
builds the live iteration loop's persistent search solver by copying `assertions()` off
the *original* model structure's solver (`build_example.model_structure.solver`, falling
back to `.stored_solver`). For every theory that lacks a bimodal-style workaround (logos,
exclusion, imposition), that copy yields **zero** assertions: `ModelDefaults.solve()`
(`models/structure.py`) assigns `self.stored_solver = self.solver` *before*
`_setup_solver` reassigns `self.solver` to a freshly populated solver, so `stored_solver`
is left referencing the solver's pristine, pre-population state; `solve()`'s `finally`
block then unconditionally sets `self.solver = None`. The live iteration search therefore
ran against an unconstrained problem for every theory except bimodal, which already
carries its own theory-local workaround (`theory_lib/bimodal/iterate.py`).

Why a bare assertion-count check is not enough: `_setup_solver` adds every constraint via
`assert_tracked`, which `Z3SolverAdapter.assert_tracked` implements as
`z3.Solver.assert_and_track(constraint, z3.Bool(label))`. Z3 records that as
`Implies(label, constraint)`, so `assertions()` on the *populated* solver returns tracked
implications, not the raw constraints -- copying those into a fresh solver would be
vacuously satisfiable (every tracking Boolean simply set `False`). A regression test that
only asserts `len(assertions()) > 0` could pass against a still-broken engine that took
that shortcut. The strong test below is the actual acceptance criterion: it requires that
a model the persistent solver produces genuinely satisfies the real
frame/model/premise/conclusion constraints read directly off `model_constraints`.
"""

import pytest
import z3
from types import SimpleNamespace
from unittest.mock import Mock

from model_checker.builder.example import BuildExample
from model_checker.solver import is_true


def _real_build_example(theory, premises, conclusions, settings):
    """A real, non-mocked `BuildExample` -- no Mock stands in for the solver, the model,
    or the semantics. Only the surrounding `BuildModule` is a `Mock`. Duplicated from
    `test_models.py::_real_build_example` deliberately (not imported) so this file stays
    independent of that test module."""
    general_settings = dict(settings)
    mock_module = Mock()
    mock_module.semantic_theories = {"theory": theory}
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example_case = [premises, conclusions, general_settings]
    return BuildExample(mock_module, theory, example_case)


def _search_solver_cases():
    """One case per theory lacking a bimodal-style workaround (logos, exclusion,
    imposition), reusing the concrete per-theory parameters already proven to work in
    `test_models.py::_generic_pinning_cases`. Built lazily (inside a function, not at
    module import time) so importing this test module never pays the cost of importing
    all three theory packages unless this test class actually runs."""
    from model_checker.theory_lib.logos import get_theory as get_logos_theory, LogosModelIterator
    from model_checker.theory_lib.exclusion import get_theory as get_exclusion_theory, ExclusionModelIterator
    from model_checker.theory_lib.exclusion.examples import EX_CM_6_premises, EX_CM_6_conclusions
    from model_checker.theory_lib.imposition import get_theory as get_imposition_theory, ImpositionModelIterator
    from model_checker.theory_lib.imposition.examples import IM_CM_0_premises, IM_CM_0_conclusions

    return [
        pytest.param(
            get_logos_theory(),
            LogosModelIterator,
            [],
            ["\\neg A"],
            {
                "N": 2, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="logos",
        ),
        pytest.param(
            get_exclusion_theory(),
            ExclusionModelIterator,
            EX_CM_6_premises,
            EX_CM_6_conclusions,
            {
                "N": 3, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="exclusion",
        ),
        pytest.param(
            get_imposition_theory(),
            ImpositionModelIterator,
            IM_CM_0_premises,
            IM_CM_0_conclusions,
            {
                "N": 4, "contingent": True, "non_null": True, "non_empty": True,
                "disjoint": False, "max_time": 40, "iterate": 3,
            },
            id="imposition",
        ),
    ]


@pytest.mark.slow
class TestPersistentSearchSolverPopulated:
    """For each theory without its own workaround, the persistent search solver
    (`iterator.constraint_generator.solver`) must carry the real constraints
    immediately after iterator construction, against a real, solved `BuildExample`."""

    @pytest.mark.parametrize(
        "theory, iterator_class, premises, conclusions, settings",
        _search_solver_cases(),
    )
    def test_persistent_solver_has_nonzero_assertions(
        self, theory, iterator_class, premises, conclusions, settings
    ):
        """Diagnostic only -- NOT sufficient on its own. A search solver populated by
        copying `assert_tracked`'s `Implies(label, constraint)` assertions would also
        pass this check while being vacuously satisfiable; see the module docstring.
        Use `test_persistent_solver_model_satisfies_real_constraints` below as the
        actual acceptance criterion."""
        example = _real_build_example(theory, premises, conclusions, settings)
        iterator = iterator_class(example)

        assertion_count = len(iterator.constraint_generator.solver.assertions())
        assert assertion_count > 0, (
            f"persistent search solver has {assertion_count} assertions immediately "
            "after iterator construction -- the live iteration search is running "
            "against an unconstrained problem"
        )

    @pytest.mark.parametrize(
        "theory, iterator_class, premises, conclusions, settings",
        _search_solver_cases(),
    )
    def test_persistent_solver_model_satisfies_real_constraints(
        self, theory, iterator_class, premises, conclusions, settings
    ):
        """The real acceptance criterion: check the persistent search solver, require
        `sat`, and verify that the produced model actually satisfies every constraint in
        `model_constraints.frame_constraints`, `.model_constraints`,
        `.premise_constraints`, and `.conclusion_constraints` -- not merely that the
        solver's assertion count is non-zero."""
        example = _real_build_example(theory, premises, conclusions, settings)
        iterator = iterator_class(example)

        solver = iterator.constraint_generator.solver
        result = solver.check()
        assert result == z3.sat, (
            f"persistent search solver checked {result}, expected sat -- the original "
            "example was already solved, so its own constraints must be satisfiable"
        )
        model = solver.model()

        model_constraints = example.model_constraints
        component_lists = {
            "frame_constraints": model_constraints.frame_constraints,
            "model_constraints": model_constraints.model_constraints,
            "premise_constraints": model_constraints.premise_constraints,
            "conclusion_constraints": model_constraints.conclusion_constraints,
        }

        checked_at_least_one = False
        for list_name, constraints in component_lists.items():
            for index, constraint in enumerate(constraints):
                checked_at_least_one = True
                evaluated = model.eval(constraint, model_completion=True)
                assert is_true(evaluated), (
                    f"persistent search solver's model violates "
                    f"model_constraints.{list_name}[{index}]: {constraint}\n"
                    f"evaluated to: {evaluated}"
                )

        assert checked_at_least_one, (
            "no constraints were checked -- the test would pass vacuously without "
            "exercising the acceptance criterion at all"
        )
