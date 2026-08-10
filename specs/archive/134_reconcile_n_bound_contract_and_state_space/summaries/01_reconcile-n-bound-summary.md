# Implementation Summary: Reconcile the N-bound contract and the eager state space

- **Task**: 134 - reconcile_n_bound_contract_and_state_space
- **Plan**: specs/134_reconcile_n_bound_contract_and_state_space/plans/01_reconcile-n-bound-contract.md
- **Status**: Complete — all 4 phases implemented, tests green
- **Session**: sess_1786219326_e8aed5_134

## Overview

`MAX_N = 20` (`code/src/model_checker/models/semantic.py:44`) was the only real
construction-time enforcement of the N ceiling. Eight other sites declared a stale `1 <= N <= 64`
contract via pure dict checks that never constructed a model, and the settings pipeline applied
no N bound at all. This work made `MAX_N` the single authoritative source across the codebase:
added a settings-layer range check, rewrote every stale declared-contract site to derive from
`MAX_N`, and corrected the one user-facing doc stating the wrong ceiling for the wrong reason.

## Phase-by-Phase Results

### Phase 1: Settings-layer N range check

Added `SettingsManager._validate_n_setting` (`code/src/model_checker/settings/settings.py`),
called from `validate_example_settings` guarded on `'N' in merged_settings`. It validates
int-ness first (`isinstance(value, int) and not isinstance(value, bool)`, since `bool` is an
`int` subclass in Python) before delegating to the existing `_validate_setting_range` helper
with `min_value=1, max_value=MAX_N`. `MAX_N` is imported locally from
`model_checker.models.semantic`, mirroring the existing `SemanticDefaults` import pattern at
`settings.py:72`.

TDD: RED tests were added first to `settings/tests/unit/test_error_handling.py`
(`test_n_setting_range_validation`, `test_n_setting_type_validation`) and confirmed failing for
the right reason (`RangeError`/`ValidationError not raised`) before the GREEN implementation.

Deleted the dead `invalid_settings` fixture in `settings/tests/conftest.py` (its `{'N': 65}`
entry was the stale-contract site) after confirming zero consumers repo-wide.

**Deviation**: the shared mock `semantic_theory` fixture in `test_error_handling.py`'s `setUp`
had no `N` key in `DEFAULT_EXAMPLE_SETTINGS`, so `validate_example_settings` would silently drop
a user-provided `N` before the new guard could see it. Added `"N": 3` to the mock's
`DEFAULT_EXAMPLE_SETTINGS` to match how real theories declare `N`.

### Phase 2: Reconcile the declared contract in test utilities and boundary tests

`assert_settings_valid` (`code/tests/utils/assertions.py`) now imports `MAX_N` and asserts
`1 <= n_value <= MAX_N` instead of the literal 64. All N-boundary parametrizations in
`test_settings_system.py`, `test_system_boundaries.py`, and `test_error_handling.py` now derive
from `MAX_N` rather than hardcoding 32/63/64/65. The "maximum N" tests
(`test_maximum_n_with_many_propositions`, `test_settings_combinations`) now use `MAX_N` instead
of 64. `test_graceful_degradation`'s `{'N': 64, ...}` entry (falsely labeled "Maximum N") was
relabeled to `{'N': MAX_N + 1, ...}` as an intentional over-limit probe.

TDD: changed `assertions.py` first (the RED step — this made the still-64-valued rows in
dependent test files fail against the new `MAX_N=20` bound, confirmed via a full run: 11 failed
for exactly the expected N=32/63/64 rows), then updated all seven caller sites to be
`MAX_N`-relative (GREEN): 158 passed across the three targeted files.

Full `code/tests/` regression after Phase 2: **283 passed** (down from 286 before this phase —
expected, since each of the three N-boundary parametrizations dropped its now-redundant "32" row,
matching the plan's own suggested replacement rows exactly).

**Deviations**:
- Dropped the "Multiple flags" combo's N from 32 to 2 in `test_settings_combinations` rather than
  another near-`MAX_N` value, since 32 was already above `MAX_N` and the combo's point is
  exercising `contingent`/`non_empty` together, not N magnitude.
- Removed the now-redundant local `from model_checker.models.semantic import MAX_N` inside
  `test_memory_limit_handling`, since the new module-level import makes it dead code (a
  REFACTOR-step cleanup, not a behavior change).

### Phase 3: Correct the documented ceiling

`docs/architecture/BUILDER.md:93` corrected from "max 64 due to bit vector representation" (wrong
number, wrong reason) to state the enforced ceiling (20 / `MAX_N` in
`model_checker.models.semantic`) and the real cause — eager `2^N` `all_states` state-space memory
exhaustion (measured ~3.5GB peak RSS at N=20), not a bit-vector width limit.

**Deviation**: also corrected the same stale `"1 to 64"` / `1 <= n <= 64` literal in
`code/docs/implementation/ERROR_HANDLING.md` at both its occurrences (line 359's
`format_config_error` usage example, in addition to the line 600-635 range the plan named) — same
illustrative-pseudocode pattern in the same file, no live enforcement either way, one more echo of
the stale number removed for consistency.

### Phase 4: Full regression run and residual-ceiling sweep

- `PYTHONPATH=code/src pytest code/tests/ -v`: **283 passed, 0 failed** (30.11s).
- `PYTHONPATH=code/src pytest code/src/model_checker/ -q`: **1906 passed, 0 failed** (342.55s /
  5:42 — ran in the background because it exceeded the interactive 120s window, not because
  anything hung).
- The slow N=MAX_N construction test
  (`test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`,
  `@pytest.mark.slow`) passed as part of both the standalone module re-run (12 passed, 11
  subtests passed) and the full 1906-passed run — `addopts` carries no `-m "not slow"` filter
  (confirmed in `code/pyproject.toml:86,92`), so slow tests run by default.
- Residual sweep (`grep -rn "<= *64\|N.*64\|'N': *6[45]" code/src code/tests docs code/docs`):
  every hit accounted for as an allow-listed non-normative mention (historical record, style
  example, performance observation) or an intentional rejected-input probe. See the plan's
  Phase 4 task list for the full accounting, including two additional non-normative hits found
  beyond the plan's original list (`theory_lib/logos/docs/SETTINGS.md:311`,
  `docs/theory/imposition/reports/imposition_comparison/modals_defined.md:734` — both plain 2^N
  arithmetic observations, not ceiling claims).
- No shipped theory default changed: `DEFAULT_EXAMPLE_SETTINGS['N']` confirmed unchanged
  (logos=16, imposition=3, exclusion=3, bimodal=2).
- `all_states` in `models/semantic.py` is untouched — `git diff` against `theory_lib/` and
  `models/semantic.py` for this task's commits is empty.
- No pre-existing failures encountered; both full-suite runs were 100% green.

## Plan Deviations

- None beyond the four inline deviations noted above (all annotated in-place in the plan's
  per-phase task checklists): the mock fixture's missing `N` key (Phase 1), the "Multiple flags"
  combo's N value and the redundant local `MAX_N` import removal (Phase 2), the extra
  `ERROR_HANDLING.md` line-359 literal (Phase 3), and the two additional non-normative sweep hits
  (Phase 4). None changed the plan's scope, goals, or non-goals.

## Non-Goals Honored

- `all_states` in `models/semantic.py` was not converted to a lazy iterator/generator — the
  research established the quadratic-to-cubic consumers in `imposition`/`logos` make the
  exponential inherent, not an eager-materialization artifact.
- No shipped theory's `DEFAULT_EXAMPLE_SETTINGS['N']` changed.
- `MAX_N` itself and `SemanticDefaults._validate_N` were not modified — both were already correct
  and unit-tested, and `models/semantic.py`/its own tests were untouched by this task's diff.

## Files Modified

- `code/src/model_checker/settings/settings.py` — added `_validate_n_setting`, called from
  `validate_example_settings`
- `code/src/model_checker/settings/tests/unit/test_error_handling.py` — new N range/type tests,
  mock fixture `N` key, module-level `MAX_N` import
- `code/src/model_checker/settings/tests/conftest.py` — deleted dead `invalid_settings` fixture
- `code/tests/utils/assertions.py` — `MAX_N`-relative N assertion
- `code/tests/integration/test_settings_system.py` — `MAX_N`-relative parametrization
- `code/tests/integration/test_system_boundaries.py` — three sites, `MAX_N`-relative
- `code/tests/integration/test_error_handling.py` — two parametrizations, one relabeled probe,
  one redundant import removed
- `docs/architecture/BUILDER.md` — corrected N ceiling and reason
- `code/docs/implementation/ERROR_HANDLING.md` — two illustrative-pseudocode literals corrected

## Commits

- `task 134 phase 1: settings-layer N range check`
- `task 134 phase 2: reconcile the declared N contract in test utilities`
- `task 134 phase 3: correct the documented N ceiling`
- (Phase 4 is verification-only; no source changes — see this summary's commit for the record)

## Follow-on Note (not in scope)

Section 2 of the research report identifies three consumers
(`imposition/semantic/model.py:_update_imposition_relations`, `imposition/iterate.py` relation
diffing, `logos/iterate.py` parthood-diff reporting) that do quadratic-to-cubic work over
`all_states`, becoming infeasible well below N=20. This is a real finding but explicitly out of
scope for this task (see Non-Goals); it may warrant a future task if imposition/logos performance
at higher N becomes a priority.
