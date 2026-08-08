# Research: Reconcile the N-bound contract and the eager 2^N state space

## Summary

`MAX_N = 20` (`code/src/model_checker/models/semantic.py:44`) is the only real construction-time
enforcement of the N ceiling, added by a prior fail-fast fix and already covered by its own unit
tests. Everything that *declares* the ceiling as 64 is a pure dict check that never constructs a
model, so it is currently lying about what the system can build. There are eight concrete sites
that assert or fixture the stale 64 ceiling, plus one settings-pipeline gap that enforces nothing
at all. Separately, three consumers of `all_states` (`imposition/semantic/model.py`,
`imposition/iterate.py`, `logos/iterate.py`) do quadratic-to-cubic-in-state-count work over
`all_states`, which means the exponential ceiling is not an artifact of eager list construction —
converting `all_states` to a lazy iterator would not usefully raise the feasible N, because these
consumers already become infeasible far below N=20. Recommendation: adopt MAX_N=20 as the single
authoritative ceiling everywhere, add an explicit N-range check to the settings pipeline, and keep
`all_states` eager.

## 1. The two disagreeing contracts

### 1a. The enforced contract: `MAX_N = 20`

`code/src/model_checker/models/semantic.py:31-179` (`SemanticDefaults.__init__` /
`_validate_N`, added by commit `16202fa2`, "task 134: fail fast on an N whose state space cannot
be built"):

- `MAX_N = 20` (line 44), with a doc comment giving measured peak RSS for `all_states` alone:
  N=16 -> 275MB, N=18 -> 928MB, N=20 -> 3.5GB. The commit message additionally records N=64 ->
  24GB RSS in ~60s, "still climbing when killed," inside an uninterruptible Z3 C call that
  `pytest-timeout`'s thread method cannot stop.
- `_validate_N` (lines 141-179) rejects non-integers, `N < 1`, and `N > MAX_N` with a
  `SemanticError` naming both the rejected value and the limit, raised *before* line 124's
  `self.all_states = [BitVecVal(i, self.N) for i in range(1 << self.N)]` runs.
- This is exercised directly by `code/tests/utils/helpers.py:create_test_model`, which bypasses
  the settings pipeline entirely and constructs `semantics_class(full_settings)` directly — so
  every test using `create_test_model` (and every direct `SemanticDefaults`/theory-semantics
  construction) already hits this guard.
- Already unit-tested at `code/src/model_checker/models/tests/unit/test_semantic.py:97-148`
  (`TestSemanticDefaultsNBounds`), including a `@pytest.mark.slow` test that actually constructs
  N=MAX_N (20) to keep the advertised limit honest.

### 1b. The declared contract: "N in [1, 64]"

Eight sites assert or fixture a 64 ceiling, none of which construct anything:

| # | Site | What it asserts |
|---|------|------------------|
| 1 | `code/tests/utils/assertions.py:133-138` (`assert_settings_valid`) | `assert 1 <= n_value <= 64` — pure dict check |
| 2 | `code/tests/integration/test_error_handling.py:249-255` (`test_valid_n_boundary_values`) | `[1, 2, 32, 63, 64]` all pass `assert_settings_valid` |
| 3 | `code/tests/integration/test_error_handling.py:257-264` (`test_invalid_n_boundary_values`) | `[-1, 0, 65, 100, 1000]` all fail; 65 is the first rejected value |
| 4 | `code/src/model_checker/settings/tests/conftest.py:24-33` (`invalid_settings` fixture) | `{'N': 65}  # N too large` |
| 5 | `code/tests/integration/test_system_boundaries.py:15-34` (`test_n_value_boundaries`) | same `[1,2,32,63,64]` valid / `[65,100]` invalid split as #2/#3 |
| 6 | `code/tests/integration/test_system_boundaries.py:202-211` (`test_maximum_n_with_many_propositions`) | `{'N': 64}` asserted valid, docstring calls it "N=64 with many propositions" |
| 7 | `code/tests/integration/test_system_boundaries.py:213-220` (`test_settings_combinations`) | parametrized with `{'N': 64, 'max_time': 3600}` labeled "Maximum values" and `{'N': 32, ...}` |
| 8 | `code/tests/integration/test_settings_system.py:14-25` (`test_n_value_validation`) | `(32, True), (64, True), (65, False), (100, False)` |

None of these tests currently fail, because `assert_settings_valid` and
`SettingsManager.validate_example_settings`/`validate_general_settings` never construct a
`SemanticDefaults` — they only shape-check a dict. `test_system_boundaries.py`'s two N=64 tests
additionally call `assert_valid_formula`, but that function (`tests/utils/assertions.py:11-…`)
only does syntactic checks (Unicode/parenthesis balance) — it never builds a model either, so
even the "with many propositions" test never actually exercises construction at N=64.

**One site is intentionally out of scope for renumbering**: `code/docs/implementation/ERROR_HANDLING.md:600-635`
contains a `1 <= n <= 64` example inside illustrative pseudocode (`validate_configuration`,
`format_config_error`, `ErrorCollector` — none of these are real repo symbols; a targeted grep
confirms `format_config_error` and `ErrorCollector` do not exist in `code/src/`). It should
ideally be corrected for consistency but is not enforcing anything and is lower priority than the
seven live sites above.

### 1c. The settings pipeline: no bound at all on the real API/CLI path

`code/src/model_checker/settings/settings.py`:
- `SettingsManager._validate_setting_range(setting_name, value, min_value=None, max_value=None)`
  (lines 327-343) is a generic range-check helper that raises `RangeError`. It exists and is unit
  tested (`settings/tests/unit/test_error_handling.py:109-142`) against `iterate`, `max_depth`,
  and `timeout` — **never against `N`**.
- `validate_example_settings` (lines 121-157) merges user example settings against
  `DEFAULT_EXAMPLE_SETTINGS`, validates only the `solver` field, and applies no range check to
  `N` whatsoever.
- `get_complete_settings` (lines 345-372) — the real entry point used by the builder/CLI/API
  path — calls `validate_general_settings` then `validate_example_settings`, so a bad `N` sails
  through settings validation with no complaint and is only caught later, when the theory's
  `semantics_class(full_settings)` is eventually constructed and hits `SemanticDefaults._validate_N`.

So there are, in effect, two independent enforcement points today: the models-layer guard (the
only one that is real) and a settings-layer facade that both `assertions.py` and `settings.py`
present as enforcing something they do not. Direct/test callers (`create_test_model`) and
API/CLI callers (which eventually construct the same `semantics_class`) both still end up
protected by the models-layer guard — the practical safety gap is small — but the settings layer
currently gives a bad `N` no earlier, settings-specific feedback (e.g. `RangeError` naming the
setting) before construction is attempted, and its own tests assert a ceiling (64) it doesn't
enforce and the constructor doesn't honor.

## 2. Is the eager `2^N` state space fixable by laziness? No — several consumers are worse than linear in state count

`all_states` is built once, linearly, in `2^N` time/space
(`models/semantic.py:124`: `[BitVecVal(i, self.N) for i in range(1 << self.N)]`). If that were
the only cost, converting it to a lazy generator would trade peak memory for repeated
recomputation on each consumer pass — a real but modest win. It is not the only cost. Three
consumers do polynomial-in-`|all_states|` work with `all_states` as the base, each iteration
containing a Z3 `model.eval()` call:

- **`imposition/semantic/model.py:84-99` (`_update_imposition_relations`)** — a **triple**-nested
  loop, `for state in self.all_states: for world in self.z3_world_states: for outcome in
  self.z3_world_states:`, each iteration doing `self._evaluate_z3_boolean(...)`. This runs on
  *every* imposition-theory model construction (not just diagnostics/iteration), so it is on the
  hot path, not an edge case. Worst case `O(|all_states| x |worlds|^2)`.
- **`imposition/iterate.py:196-227`** (imposition-relation diffing between iterations) —
  double-nested `for i, state1 in enumerate(all_states): for j, state2 in
  enumerate(all_states[i:], i):` with an inner `for outcome in all_states:` scan inside, i.e.
  `O(|all_states|^3)` in the worst case.
- **`logos/iterate.py:189-...`** (parthood-diff reporting) — `for s1 in new_structure.all_states:
  for s2 in new_structure.all_states:`, `O(|all_states|^2)` per sentence letter, each iteration
  calling `previous_model.eval(...)`/`new_model.eval(...)`.

At N=20, `|all_states| = 2^20 ~ 1.05M`. A quadratic pass over that is already `~1.1 x 10^12`
Z3-eval calls; the imposition triple-nested pass is worse. These consumers become computationally
infeasible at N values far below 20 — likely somewhere in the low double digits, well before
`all_states`'s own linear materialization cost (3.5GB at N=20) becomes the binding constraint for
`imposition` and iteration workflows specifically. This was not previously established; it
follows directly from reading the three call sites above. **Laziness in `all_states` would not
meaningfully raise the feasible N for any theory or workflow that hits these three consumers** —
it only reduces the (already-affordable-at-N<=20) cost of the base construction step, not the
dominant cost of the pairwise/triple-wise consumers layered on top of it.

**Recommendation**: keep `all_states` as an eagerly materialized list. The eager-list design is
already correct, simple, and — per the measured numbers above — not the binding constraint on
feasible N; several consumers already re-iterate `all_states` multiple times (e.g.
`imposition/semantic/model.py` iterates it in at least three separate methods), so a lazy
generator would need caching to avoid re-computation, which is just a list again with extra
complexity. The design question the task description raised ("is the exponential inherent, or
just an eager-materialization artifact?") resolves to: **inherent** — several real consumers are
worse than linear in `|all_states|`, so no amount of laziness in the base list fixes the
underlying complexity.

## 3. Shipped theory defaults vs. the ceiling

All shipped theories' `DEFAULT_EXAMPLE_SETTINGS['N']` sit well under `MAX_N=20`, confirmed by
direct inspection:

| Theory | `N` default | File |
|--------|------------|------|
| logos | 16 | `theory_lib/logos/semantic/core.py:40` |
| imposition | 3 | `theory_lib/imposition/semantic/core.py:93` |
| exclusion | 3 | `theory_lib/exclusion/semantic/core.py:94` |
| bimodal | 2 | `theory_lib/bimodal/semantic/core.py:45` |

logos's N=16 is the closest to the ceiling (4 below it), which the original task description
called out as a "headroom concern." Given MAX_N=20 was set specifically to sit above logos's
default (per the doc comment on `MAX_N`), no default needs to change — there is no shipped
theory default within an unsafe margin of the ceiling, and section 2 above shows logos's own
iterate.py parthood-diff consumer would already be the practical bottleneck at N values well
above 16 for any theory instantiated near this default, not the MAX_N guard itself.

## 4. Documentation stating a 64 limit

Beyond the test/fixture sites in section 1b, one real user-facing doc states the stale ceiling as
fact:

- **`docs/architecture/BUILDER.md:93`**: `` `N`: Number of atomic states (typically 3-5, max 64
  due to bit vector representation) `` — states both the wrong ceiling (64, not 20) and the wrong
  *reason* (it is not a bit-vector width limit — Z3 `BitVec`s are not practically capped at 64;
  the real constraint is the eager `2^N` state-space materialization exhausting memory, per
  section 2/`MAX_N`'s doc comment).

Lower-priority, non-normative mentions of "64" that do **not** claim a system ceiling and can be
left as-is (they are either historical record or unrelated style examples):
- `code/docs/core/KNOWN_TEST_FAILURES.md:138` — historical record of the *pre-fix* bug (N=64
  hanging the suite); accurate as a description of what was fixed, not a live contract.
- `code/docs/standards/AUDIENCE.md:112,222` — a writing-style guide using "bit vectors limit us
  to N <= 64" purely as an illustrative *example* of how to phrase a technical constraint for a
  target audience, not a claim about this codebase's actual limit.
- `docs/theory/QUANTIFIER_SOLVERS.md:561`, `docs/architecture/ITERATE.md:192,219` — describe
  *practical* slowness thresholds around N=6 (64 states), which is a performance observation, not
  a hard ceiling claim, and is consistent with (indeed reinforces) section 2's finding that
  iterate-adjacent consumers get slow long before N approaches 20.
- `code/tests/integration/test_timeout_resources.py:84,136,245` and
  `code/tests/integration/test_performance.py:365,370` already use N=64/48/32 as intentional
  *rejected*-input probes with broad exception handling (`except Exception: pass`, or asserting
  `"memory"`/`"resource"` appears in the exception string) — these already tolerate
  `SemanticError`'s message (which contains the word "memory") and do not need to change.
  `test_error_handling.py::test_memory_limit_handling` (lines 141-160) already imports `MAX_N`
  from `models/semantic` and uses `MAX_N + 1` dynamically rather than a hardcoded 64 — this is
  the pattern the seven stale sites in section 1b should be converted to.

## 5. Recommendation

1. **Adopt `MAX_N = 20` (`code/src/model_checker/models/semantic.py:44`) as the single
   authoritative ceiling.** It is the only value with empirical grounding (measured RSS at
   N=16/18/20, an existing slow-test that actually constructs N=20) and it already sits above
   every shipped theory default (section 3).
2. **Propagate it to all seven live declared-contract sites in section 1b**, following the
   pattern already used by `test_memory_limit_handling`: `from model_checker.models.semantic
   import MAX_N` and parametrize/fixture off that constant rather than a literal 64/65. Concretely:
   - `tests/utils/assertions.py:137-138`: change `1 <= n_value <= 64` to `1 <= n_value <= MAX_N`
     (import `MAX_N` from `model_checker.models.semantic`).
   - `test_error_handling.py:249,257`: replace `[1, 2, 32, 63, 64]` / `[-1, 0, 65, 100, 1000]`
     with values derived from `MAX_N` (e.g. `[1, 2, MAX_N-1, MAX_N]` / `[-1, 0, MAX_N+1, 100,
     1000]`).
   - `settings/tests/conftest.py:29`: change `{'N': 65}` to reference `MAX_N + 1` (or update the
     comment to name the new value if the fixture stays a literal for import-simplicity reasons).
   - `test_system_boundaries.py:15-34,202-220`: same MAX_N-relative treatment; the "maximum N"
     test and the `{'N': 64, ...}` combo need their N value dropped to `MAX_N` (or below) since
     they are meant to test success at the real maximum, not a value the system now rejects.
   - `test_settings_system.py:14-25`: `(32, True), (64, True)` need to move to the invalid side
     (or drop to `MAX_N`-relative values) since 32 and 64 no longer construct.
3. **Add an explicit N-range check to the settings pipeline** (`SettingsManager`, e.g. inside
   `validate_example_settings` or a new `_validate_n_setting` called from
   `get_complete_settings`), using the existing `_validate_setting_range` helper with
   `min_value=1, max_value=MAX_N`, importing `MAX_N` from `model_checker.models.semantic` (the
   module already imports `SemanticDefaults` from there at `settings.py:72`, so this is not a new
   dependency). This closes the "settings pipeline advertises no limit" gap named in the task
   description and gives a `RangeError` naming the setting *before* the theory's `semantics_class`
   is constructed, rather than relying entirely on the models-layer `SemanticError` surfacing
   later in the same call chain.
4. **Update `docs/architecture/BUILDER.md:93`** to state the correct ceiling (20) and the correct
   reason (eager `2^N` state-space memory exhaustion, not bit-vector width).
5. **Keep `all_states` eagerly materialized** (no laziness change) — per section 2, the
   exponential is inherent to several downstream consumers (`imposition/semantic/model.py`,
   `imposition/iterate.py`, `logos/iterate.py`), not an artifact of eager list construction, so
   laziness would add complexity without meaningfully raising the feasible N.
6. **No shipped theory default needs to change** (section 3); logos's N=16 has adequate headroom
   under MAX_N=20 and is not close to becoming the binding constraint given the consumer
   complexity found in section 2.
7. Leave `code/docs/implementation/ERROR_HANDLING.md`'s illustrative pseudocode, the historical
   note in `KNOWN_TEST_FAILURES.md`, and the `AUDIENCE.md` writing-style example as-is or update
   opportunistically — none of them assert a live system contract, so they are not required for
   this task's scope (reconciling the *enforced* contract) but a one-line MAX_N correction in
   `ERROR_HANDLING.md`'s example would remove one more echo of the stale number.

## Files referenced

- `code/src/model_checker/models/semantic.py` (MAX_N, `_validate_N`, `all_states`)
- `code/src/model_checker/models/tests/unit/test_semantic.py` (`TestSemanticDefaultsNBounds`)
- `code/tests/utils/assertions.py` (`assert_settings_valid`)
- `code/tests/utils/helpers.py` (`create_test_model`)
- `code/tests/integration/test_error_handling.py` (`TestEdgeCases`, `test_memory_limit_handling`)
- `code/tests/integration/test_system_boundaries.py` (`TestBoundaryValues`, `TestCombinationEffects`)
- `code/tests/integration/test_settings_system.py` (`TestSettingsValidation`)
- `code/src/model_checker/settings/settings.py` (`SettingsManager`, `_validate_setting_range`,
  `validate_example_settings`, `get_complete_settings`)
- `code/src/model_checker/settings/tests/conftest.py` (`invalid_settings` fixture)
- `code/src/model_checker/theory_lib/imposition/semantic/model.py`
  (`_update_imposition_relations`)
- `code/src/model_checker/theory_lib/imposition/iterate.py` (imposition-relation diffing)
- `code/src/model_checker/theory_lib/logos/iterate.py` (parthood-diff reporting)
- `code/src/model_checker/theory_lib/{logos,imposition,exclusion,bimodal}/semantic/core.py`
  (`DEFAULT_EXAMPLE_SETTINGS['N']`)
- `docs/architecture/BUILDER.md` (stale 64-limit doc claim)
- Prior commits: `16202fa2` (guard added), `9febfb33` (this task spawned), `cc5420fd` (follow-up
  fix to the one call site depending on the pre-guard exception type)
