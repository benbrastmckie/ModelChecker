# Implementation Plan: Reconcile the N-bound contract and the eager state space

- **Task**: 134 - reconcile_n_bound_contract_and_state_space
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/134_reconcile_n_bound_contract_and_state_space/reports/01_reconcile-n-bound-contract.md
- **Artifacts**: plans/01_reconcile-n-bound-contract.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`MAX_N = 20` in `code/src/model_checker/models/semantic.py:44` is the only construction-time
enforcement of the N ceiling and the only value with empirical grounding (measured peak RSS at
N=16/18/20 plus a slow test that actually builds N=20). Eight other sites still declare a
`1 <= N <= 64` contract through pure dict checks that construct nothing, and the settings
pipeline applies no N bound at all despite owning a `_validate_setting_range` helper. This plan
makes `MAX_N` the single authoritative source: it adds a settings-layer range check so a bad `N`
gets a `RangeError` naming the setting before any semantics class is constructed, rewrites every
stale declared-contract site to derive from `MAX_N`, and corrects the one user-facing doc that
states the wrong ceiling for the wrong reason. Done means: no live site names 64 as the ceiling,
`MAX_N` is imported rather than duplicated, and the full test suite is green.

### Research Integration

The research report resolves the plan's two open questions and both resolutions are binding here:

1. **`all_states` stays eagerly materialized.** Three consumers do quadratic-to-cubic work in
   state count with a Z3 `model.eval()` inside every iteration —
   `theory_lib/imposition/semantic/model.py` `_update_imposition_relations` (triple-nested, on the
   hot path for every imposition model), `theory_lib/imposition/iterate.py` relation diffing
   (`O(|all_states|^3)` worst case), and `theory_lib/logos/iterate.py` parthood diffing
   (`O(|all_states|^2)` per sentence letter). These become infeasible well below N=20, so the
   exponential is inherent to the consumers, not an artifact of eager list construction. **No
   lazy-`all_states` refactor is in scope.**
2. **No shipped theory default needs to change** (logos=16, imposition=3, exclusion=3, bimodal=2);
   all sit under `MAX_N=20`.

The report also identifies `test_error_handling.py::test_memory_limit_handling` as the pattern to
follow: it already does `from model_checker.models.semantic import MAX_N` and uses `MAX_N + 1`
rather than a literal. Every site touched by this plan converges on that pattern.

Two facts were established beyond the report during planning and are folded in below:

- There is **no CLI/flag path that supplies `N`** (`apply_flag_overrides` has no `N` handling and
  no `-N` argparse destination exists), so `validate_example_settings` is a sufficient enforcement
  point — a post-`apply_flag_overrides` check is not required.
- The `invalid_settings` fixture at `settings/tests/conftest.py:25-33` has **no consumers** inside
  the settings package. Phase 1 resolves this explicitly rather than blindly rewriting it.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation was provided for this task.

## Goals & Non-Goals

**Goals**:
- Make `models.semantic.MAX_N` the single authoritative N ceiling — every live site derives from
  it by import, never by literal.
- Add an explicit N range check to the settings pipeline so out-of-range `N` raises a
  settings-layer `RangeError` before a semantics class is constructed.
- Rewrite the eight stale `N <= 64` declaration sites to be `MAX_N`-relative.
- Correct `docs/architecture/BUILDER.md:93`, which states both the wrong ceiling and the wrong
  reason for it.
- Keep the full test suite green with no new skips or xfails.

**Non-Goals**:
- Converting `all_states` to a lazy iterator or generator (resolved: inherent exponential, see
  Research Integration).
- Changing any theory's `DEFAULT_EXAMPLE_SETTINGS['N']`.
- Optimizing the quadratic/cubic `all_states` consumers in imposition/logos — a real finding, but
  separate work; note it in the summary rather than acting on it.
- Changing the value of `MAX_N` itself, or `SemanticDefaults._validate_N`, both of which are
  already correct and unit-tested.
- Rewriting non-normative "64" mentions that do not claim a system ceiling
  (`code/docs/core/KNOWN_TEST_FAILURES.md:138` historical record,
  `code/docs/standards/AUDIENCE.md:112,222` writing-style examples,
  `docs/theory/QUANTIFIER_SOLVERS.md:561`, `docs/architecture/ITERATE.md:192,219` performance
  observations).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The new settings-layer check rejects an `N` that some existing test feeds through `SettingsManager`, breaking unrelated tests | M | M | Phase 1 runs the full settings package suite plus `code/tests/` before it is considered green; a grep for large-`N` settings dicts was already done and found no `SettingsManager`-routed caller above 20 |
| `_validate_setting_range` compares with `<`/`>`, so a non-int `N` (e.g. `"2"`) raises `TypeError` instead of a clear validation error | M | H | Phase 1 validates int-ness (excluding `bool`, which is an `int` subclass) *before* the range call, and covers `"2"`, `1.5`, and `True` in the RED tests |
| Rewriting `assert_settings_valid` silently breaks the five parametrized tests that depend on it | H | H | Phase 2 owns `assertions.py` and all five dependents in one phase and is not green until they pass together |
| An importable cycle from adding `from model_checker.models.semantic import MAX_N` to `settings/settings.py` | L | L | `settings.py:72` already imports `SemanticDefaults` from that module inside a method body; use the same local-import placement |
| Phases 1 and 2 run in parallel and collide on a shared file | L | L | Territories are disjoint by construction: Phase 1 owns `code/src/model_checker/settings/**`; Phase 2 owns `code/tests/**` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Settings-layer N range check [COMPLETED]

**Goal**: `SettingsManager` rejects an out-of-range or non-integer `N` with a settings-layer
error naming the setting, before any semantics class is constructed.

**Territory**: `code/src/model_checker/settings/**` only. Do not touch `code/tests/**` in this
phase.

**Tasks**:
- [x] RED: add failing tests to `code/src/model_checker/settings/tests/unit/test_error_handling.py`
      (alongside the existing `_validate_setting_range` tests for `iterate`/`max_depth`/`timeout`)
      covering, via `SettingsManager.validate_example_settings` (or `get_complete_settings`):
      `N = MAX_N` accepted; `N = 1` accepted; `N = MAX_N + 1` raises `RangeError`; `N = 0` and
      `N = -1` raise `RangeError`; `N = "2"`, `N = 1.5`, and `N = True` raise a validation error
      rather than `TypeError`. Import `MAX_N` from `model_checker.models.semantic` — no literals.
      *(deviation: the shared mock `semantic_theory` fixture in `setUp` had no `N` key in
      `DEFAULT_EXAMPLE_SETTINGS`, so `validate_example_settings` would silently drop a
      user-provided `N` before the guard could see it; added `"N": 3` to the mock's
      `DEFAULT_EXAMPLE_SETTINGS` to match how real theories declare `N`.)*
- [x] Confirm the new tests fail for the right reason (no bound enforced today), and record the
      failure output before implementing. Both new tests failed with `RangeError not raised` /
      `ValidationError not raised` prior to the GREEN step.
- [x] GREEN: add a `_validate_n_setting` helper to `SettingsManager` in
      `code/src/model_checker/settings/settings.py` that validates int-ness first
      (`isinstance(value, int) and not isinstance(value, bool)`), then delegates to the existing
      `_validate_setting_range(setting_name='N', value=n, min_value=1, max_value=MAX_N)`.
      Import `MAX_N` locally, mirroring the existing `SemanticDefaults` import at line 72.
- [x] Call `_validate_n_setting` from `validate_example_settings` (lines 121-157), next to the
      existing `solver` field validation, guarded on `'N' in merged_settings`. No `N` arrives via
      `apply_flag_overrides`, so this single call site covers the API/CLI path.
- [x] Resolve `settings/tests/conftest.py:25-33`'s `{'N': 65}  # N too large` entry: grep
      repo-wide for `invalid_settings`; if it still has no consumers, delete the dead fixture
      (clean break, no compatibility shim) and note the deletion; if a consumer is found, convert
      the entry to `MAX_N + 1` with `MAX_N` imported. Confirmed no consumer (`grep -rn
      "invalid_settings" code/` shows no `def test...(..., invalid_settings, ...)` in
      `settings/`) — deleted the fixture.
- [x] Confirm the error message names both the setting and the limit. `RangeError.setting == 'N'`
      and `error.max_value`/`error.min_value` assert the limit in the new tests; the base
      `SettingsError.__str__` prefixes `Setting 'N': ...` and appends the `<= MAX_N`/`>= 1`
      suggestion.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - add `_validate_n_setting`, call it from
  `validate_example_settings`
- `code/src/model_checker/settings/tests/unit/test_error_handling.py` - new `N` range/type tests
- `code/src/model_checker/settings/tests/conftest.py` - delete or de-stale the `invalid_settings`
  fixture

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/settings/ -v` green, with the new tests
  present and passing.
- `PYTHONPATH=code/src pytest code/tests/ -q` shows no new failures attributable to this phase.
- `grep -rn "64\|65" code/src/model_checker/settings/` returns no N-ceiling claim.

---

### Phase 2: Reconcile the declared contract in test utilities and boundary tests [COMPLETED]

**Goal**: Every test site that declares the N contract derives its values from `MAX_N` and agrees
with what the system actually builds.

**Territory**: `code/tests/**` only. Do not touch `code/src/**` in this phase.

**Tasks**:
- [x] `code/tests/utils/assertions.py:132-138` (`assert_settings_valid`): import `MAX_N` from
      `model_checker.models.semantic` and change `assert 1 <= n_value <= 64` to
      `assert 1 <= n_value <= MAX_N`, updating the assertion message to interpolate `MAX_N`
      instead of the literal 64.
- [x] `code/tests/integration/test_settings_system.py:14-25` (`test_n_value_validation`): the
      `(32, True)` and `(64, True)` rows now describe values the system rejects — replace the
      parametrization with `MAX_N`-relative rows (e.g. `(1, True), (2, True), (MAX_N, True),
      (0, False), (-1, False), (MAX_N + 1, False), (100, False), (1.5, False), ("2", False)`).
- [x] `code/tests/integration/test_system_boundaries.py:15-34` (`test_n_value_boundaries`): same
      `MAX_N`-relative treatment; `63`/`64` become `MAX_N - 1`/`MAX_N`, `65` becomes `MAX_N + 1`.
- [x] `code/tests/integration/test_system_boundaries.py:202-211`
      (`test_maximum_n_with_many_propositions`): change `{'N': 64}` to `{'N': MAX_N}` and update
      the docstring, which currently says "Test N=64 with many propositions".
- [x] `code/tests/integration/test_system_boundaries.py:213-220` (`test_settings_combinations`):
      change the `{'N': 64, 'max_time': 3600}` "Maximum values" combo to `{'N': MAX_N, ...}` and
      the `{'N': 32, ...}` combo to a value at or below `MAX_N`. *(deviation: dropped the
      "Multiple flags" combo's N from 32 to 2 rather than another near-MAX_N value, since 32 was
      already above MAX_N and the combo's point is exercising `contingent`/`non_empty` together,
      not N magnitude.)*
- [x] `code/tests/integration/test_error_handling.py:249` (`test_valid_n_boundary_values`):
      replace `[1, 2, 32, 63, 64]` with `MAX_N`-derived values (`[1, 2, MAX_N - 1, MAX_N]`).
- [x] `code/tests/integration/test_error_handling.py:257` (`test_invalid_n_boundary_values`):
      replace `[-1, 0, 65, 100, 1000]` with `[-1, 0, MAX_N + 1, 100, 1000]`.
- [x] `code/tests/integration/test_error_handling.py:216` (`test_graceful_degradation`): the
      `{'N': 64, 'maximize': True}` entry with the comment "Maximum N with maximize" is already
      exception-tolerant and does not need to pass, but its label is now false. Either relabel it
      as an intentional over-limit probe or drop it to `MAX_N`; do not leave the stale "Maximum N"
      claim. Relabeled to `{'N': MAX_N + 1, 'maximize': True}` with an "Over-limit N: intentionally
      rejected probe" comment. *(deviation: also removed the now-redundant local `from
      model_checker.models.semantic import MAX_N` inside `test_memory_limit_handling`, since the
      new module-level import at line 10 makes it dead code — a REFACTOR-step cleanup, not a
      behavior change.)*
- [x] Leave `test_timeout_resources.py:84,136,245` and `test_performance.py:365-380` unchanged —
      they are intentional rejected-input probes with broad exception handling that already
      tolerate `SemanticError`. Confirmed unchanged.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/tests/utils/assertions.py` - `MAX_N`-relative N assertion
- `code/tests/integration/test_settings_system.py` - `MAX_N`-relative parametrization
- `code/tests/integration/test_system_boundaries.py` - three sites, `MAX_N`-relative
- `code/tests/integration/test_error_handling.py` - two parametrizations plus one stale label

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/integration/test_settings_system.py code/tests/integration/test_system_boundaries.py code/tests/integration/test_error_handling.py -v` green.
- `grep -rn "\b64\b" code/tests/utils/assertions.py code/tests/integration/test_settings_system.py code/tests/integration/test_system_boundaries.py` returns no N-ceiling claim.
- Every touched file imports `MAX_N` rather than hardcoding a limit.

---

### Phase 3: Correct the documented ceiling [NOT STARTED]

**Goal**: The one user-facing doc that states an N ceiling states the enforced one, for the real
reason.

**Tasks**:
- [ ] `docs/architecture/BUILDER.md:93`: replace ``max 64 due to bit vector representation`` with
      the enforced ceiling (20) and the real reason — the eager `2^N` `all_states` materialization
      exhausts memory (measured peak RSS: N=16 -> 275MB, N=18 -> 928MB, N=20 -> 3.5GB), not a
      bit-vector width limit. Reference `MAX_N` in `model_checker.models.semantic` as the
      authoritative source so the number has a home if it ever moves.
- [ ] Optionally correct the `1 <= n <= 64` literal in
      `code/docs/implementation/ERROR_HANDLING.md:600-635`. It sits inside illustrative pseudocode
      whose symbols (`format_config_error`, `ErrorCollector`) do not exist in `code/src/`, so it
      enforces nothing — but the one-line change removes another echo of the stale number.
- [ ] Do not touch the non-normative mentions listed under Non-Goals.
- [ ] No task numbers in any file outside `specs/**`; cite `models/semantic.py`'s `MAX_N` as the
      durable anchor.

**Timing**: 0.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `docs/architecture/BUILDER.md` - correct ceiling and reason
- `code/docs/implementation/ERROR_HANDLING.md` - optional pseudocode literal

**Verification**:
- `grep -n "64" docs/architecture/BUILDER.md` shows no N-ceiling claim.
- The corrected text names 20 and attributes it to state-space memory, not bit-vector width.

---

### Phase 4: Full regression run and residual-ceiling sweep [NOT STARTED]

**Goal**: Confirm one authoritative ceiling repo-wide and a green suite.

**Tasks**:
- [ ] Run the full suite: `PYTHONPATH=code/src pytest code/tests/ -v` and
      `PYTHONPATH=code/src pytest code/src/model_checker/ -q`. Record pass/fail counts.
- [ ] Run the slow test that actually constructs `N = MAX_N`
      (`code/src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds`,
      including the `@pytest.mark.slow` case) to confirm the advertised limit is still honest.
- [ ] Sweep for residual live claims: `grep -rn "<= *64\|N.*64\|'N': *6[45]" code/src code/tests docs code/docs`
      and confirm every remaining hit is on the Non-Goals allow-list (historical record, style
      example, performance observation, or intentional over-limit probe).
- [ ] Confirm no shipped theory default changed: `DEFAULT_EXAMPLE_SETTINGS['N']` remains
      logos=16, imposition=3, exclusion=3, bimodal=2.
- [ ] Confirm `all_states` in `models/semantic.py` is untouched (eager list preserved).
- [ ] If any pre-existing failure is encountered that this task did not cause, report it
      explicitly rather than fixing it silently or attributing it to this work.

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**: none (verification only; fixes land in the owning phase)

**Verification**:
- Full suite green, or every failure demonstrated to predate this task with evidence.
- Residual-64 grep yields only allow-listed hits.
- `git diff` touches no theory `semantic/core.py` and no `all_states` construction.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/settings/ -v` green with new N range tests
- [ ] `PYTHONPATH=code/src pytest code/tests/integration/ -v` green
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/models/tests/unit/test_semantic.py -v` green (including the slow N=MAX_N construction case)
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` full-suite green
- [ ] Out-of-range `N` produces a settings-layer `RangeError` naming the setting and the limit, before construction
- [ ] Non-integer `N` produces a clear validation error, not a bare `TypeError`
- [ ] No file outside `models/semantic.py` hardcodes an N ceiling
- [ ] No new skips, xfails, or `@pytest.mark.slow` quarantines introduced

## Artifacts & Outputs

- `specs/134_reconcile_n_bound_contract_and_state_space/plans/01_reconcile-n-bound-contract.md` (this file)
- `specs/134_reconcile_n_bound_contract_and_state_space/summaries/01_reconcile-n-bound-contract-summary.md`
- Modified source: `code/src/model_checker/settings/settings.py`
- Modified tests: `code/src/model_checker/settings/tests/unit/test_error_handling.py`,
  `code/src/model_checker/settings/tests/conftest.py`, `code/tests/utils/assertions.py`,
  `code/tests/integration/test_settings_system.py`,
  `code/tests/integration/test_system_boundaries.py`,
  `code/tests/integration/test_error_handling.py`
- Modified docs: `docs/architecture/BUILDER.md`, optionally
  `code/docs/implementation/ERROR_HANDLING.md`

## Rollback/Contingency

Every phase is an independent, small diff with its own commit, so rollback is per-phase
`git revert` of that phase's commit — no migration or data change is involved.

- If Phase 1's settings-layer check turns out to break a caller that legitimately passes an `N`
  above `MAX_N` through `SettingsManager` without ever constructing a semantics class, revert
  Phase 1 alone. Phases 2-4 stand on their own: the declared contract is still wrong today and
  fixing it does not depend on the settings check.
- If the full-suite run in Phase 4 surfaces a failure caused by this work that is not fixable
  inside the owning phase, revert that phase's commit and record the blocker rather than widening
  scope.
- Do not resolve any failure by relaxing `MAX_N` — it is empirically grounded, and raising it
  reintroduces the unkillable memory-exhaustion path the guard was added to close.
