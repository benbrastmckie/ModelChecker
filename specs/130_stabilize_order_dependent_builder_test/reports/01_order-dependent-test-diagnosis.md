# Diagnosis: order-dependent / misnamed builder test

## Target

`code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_logos_extensional_theory`

## 1. Reproduction: three invocations, actual results observed

All three were run directly on the current branch (`task-117-restore-model-checker`,
post `task 126` core/theory_lib refactor), with `PYTHONPATH=code/src`. Each was run multiple
times (isolated x4, file-scope x1 full + x3 targeted-`-k`, full builder suite x2) to check for
flakiness.

| Invocation | Command | Result observed (every run) |
|---|---|---|
| Isolated | `pytest code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_logos_extensional_theory` | **FAIL** — `AssertionError: False is not true : Should find countermodel where A is true but B is false` |
| File scope | `pytest code/src/model_checker/builder/tests/unit/test_example.py` | **FAIL**, same assertion. (`test_find_next_model_basic` also fails at file scope, with `AttributeError: 'BuildExample' object has no attribute 'find_next_model'` — a separate, pre-existing, out-of-scope defect.) |
| Full builder suite | `pytest code/src/model_checker/builder/tests/` | **FAIL**, same assertion, both runs (6 failed / 238 passed each time, identical failing set). |

On this machine/branch the test now fails **deterministically in all three contexts** — it is
not currently exhibiting the pass in the previous, previously-documented "passes inside the full
suite" mode. A prior baseline (`specs/122_rootcause_crossoracle_differential_and_establish_t/plans/01_rootcause-differential-green-gate.md:114`)
recorded this same test as an *intermittent* flake ("~1 of 4 runs", "Z3-context-isolation-flavored
flake") at an earlier point in the codebase's history. The mechanism identified below (a solve
time that sits close to, or now consistently above, the timeout budget) is consistent with both
observations: a race this close to its deadline will flip between "intermittent" and
"deterministically over budget" as solve time drifts by machine load, Z3 version, or unrelated
code changes that add a few hundred ms to the constraint-generation path. Whichever side of the
race it lands on, the underlying defect — a Z3-solve-time budget that is not comfortably larger
than the actual expected solve time — is identical, and is what makes the test's outcome
sensitive to invocation context in the first place. I could not reproduce the specific
"passes only inside the full suite" polarity on this machine; I looked for (and did not find) any
mechanism that would produce that specific direction of leakage (see part 2).

## 2. Root cause: a timeout race, not state leakage

`example_range = {"SIMPLE": [["A"], ["B"], {"N": 2}]}` sets only `N`; `max_time` is left
unset and inherits `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS['max_time'] = 1`
(`code/src/model_checker/theory_lib/bimodal/semantic/core.py:53`), i.e. Z3 gets **1 second** to
search a bimodal (world-history x time) model space at `N=2, M=2` (M also defaults, from the same
dict, to 2).

Direct reproduction (same `theory`/`semantic_theories`/`example_range` shape as the test, run via
`dev_cli.py`, outside pytest):

- With `max_time` left at the implicit default (1s): `TIMEOUT: Model search exceeded maximum time
  of 1 seconds` -> reported as "there is no countermodel" (i.e. `model_found=False`) — this is a
  **timeout**, not a proof of validity.
- With `max_time: 10`: countermodel found, `Solver Run Time: 1.6883 seconds` (A true, B false at
  the evaluation point, as expected).

So the actual Z3 solve for this exact formula takes **~1.7s**, comfortably longer than the 1s
budget the test silently inherits. The test's outcome is therefore a coin-flip on solver/machine
speed relative to a too-tight deadline — this *is* the "order dependence": which pytest
invocation context "wins" the race depends on incidental per-process timing (JIT/interpreter
warm-up, OS scheduling, how much other work already ran in the same process), not on any genuine
semantic difference between invocation modes.

I also checked, per the delegation's specific list of suspects, for a **structural** (rather than
timing) leakage mechanism, since a prior documented run showed the opposite polarity (fails
alone/at file scope, passes in the full suite):

- **`get_theory` (bimodal)** — pure function, no `lru_cache`, no module-level mutable state; the
  `config` argument is accepted but entirely unused (see part 3). Confirmed no caching.
- **Settings merge (`BuildModule`/settings manager)** — `DEFAULT_EXAMPLE_SETTINGS` is a class
  attribute dict; the merge path builds new dicts per call rather than mutating the class dict in
  place. No cross-instance leakage found.
- **Z3 context/config** — no module-level `z3.Context()` or process-wide `z3.set_param()` that
  would make later solves faster/slower depending on prior Z3 usage in the same process; each
  `BuildExample.get_result()` solve runs against the timeout set from that example's own
  `max_time` (`models/structure.py` construction path), independently per call.
- **Model-level caching** — no memoized/cached solver keyed on something invocation-order could
  vary.

No state-leakage mechanism was found. The evidence is consistent with a plain timeout race: a
~1.7s solve against a 1s budget, with the specific pass/fail split across invocation contexts
being explained by ordinary per-process timing variance rather than hidden shared state.

## 3. What `get_theory(['extensional'])` (bimodal) actually returns, and whether the
   `model_found` expectation is sound

`code/src/model_checker/theory_lib/bimodal/__init__.py:76-97`:

```python
def get_theory(config=None):
    """Get bimodal theory configuration.
    Args:
        config: Optional configuration (currently unused)
    ...
    """
    return {
        "semantics": BimodalSemantics,
        "proposition": BimodalProposition,
        "model": BimodalStructure,
        "operators": bimodal_operators
    }
```

`config` (here `['extensional']`) is accepted but **completely ignored** — the docstring says so
explicitly ("currently unused"). The call always returns the full bimodal theory (all temporal
and modal operators, `bimodal_operators`), never a restricted "extensional-only" fragment. There
is no `['extensional']`-shaped restriction anywhere in bimodal's `get_theory`. This is why the
search space for a trivial-looking `A ⊨ B` example still spans world-histories and times
(`N=2, M=2`) rather than being flat propositional — and why the solve takes ~1.7s instead of
being near-instant.

Given what the body *actually* loads (full bimodal semantics, not a restricted extensional
fragment), the `model_found=True` expectation is **semantically sound**: `A` alone does not entail
`B` under bimodal semantics, and a genuine countermodel exists and is found once given enough
time (confirmed directly above). The only defect is the timeout budget, not the assertion itself.

## 4. Correct name for the test

The test does not exercise `logos` at all — it imports `get_theory` from
`model_checker.theory_lib.bimodal` and builds/solves a bimodal-theory example. The name
`test_logos_extensional_theory` is wrong on two counts: wrong theory (`bimodal`, not `logos`), and
implies a restricted "extensional" fragment that `get_theory` does not actually produce (part 3).

Recommended replacement, matching the sibling naming convention in this file
(`test_build_example_*`): **`test_build_example_bimodal_theory_countermodel`** — describes what is
actually built (a `BuildExample` over the bimodal theory) and what is actually asserted (a
countermodel is found). The docstring and in-body comments ("Test BuildExample with logos
extensional theory", "Simple example A premises, B conclusion - should find a countermodel")
should be updated to say "bimodal theory" and drop the "extensional"/"logos" framing, since
`get_theory`'s `config` argument has no effect.

## 5. Scope

The delegated `file_scope` is `code/src/model_checker/builder/tests/unit/test_example.py` only.
The fix that resolves both the flakiness/order-dependence and the misnaming is **entirely
containable within that file**:

- Rename `test_logos_extensional_theory` -> `test_build_example_bimodal_theory_countermodel`
  (and update its docstring/comments to match, per part 4).
- Add `"max_time": 10` (or similar headroom; other bimodal examples in
  `theory_lib/bimodal/examples.py` commonly use 5-30s for comparable N/M) to the `SIMPLE`
  example's settings dict, e.g. `{"N": 2, "max_time": 10}`, so the ~1.7s solve completes reliably
  regardless of machine speed or invocation context. This removes the timing race without
  touching any source outside the test file.

No source change outside `test_example.py` is required for *this* test's determinism fix.

**Out-of-scope observations, not required for this fix, flagged for a possible follow-up task**:

- `theory_lib/bimodal/__init__.py`'s `get_theory(config=None)` silently ignores `config`. If any
  other test or example in the codebase relies on `get_theory(['extensional'])` actually
  restricting the operator set, that expectation is currently false everywhere, not just in this
  test. This is a latent API/behavior gap in `bimodal.get_theory`, outside `test_example.py`.
- `test_find_next_model_basic` (same class, same file) exhibits a related but distinct failure at
  file scope and full-suite: `AttributeError: 'BuildExample' object has no attribute
  'find_next_model'`, and in the full-suite run instead fails with `Should find initial model for
  A` (also consistent with the same tight-`max_time`-vs-actual-solve-time pattern, since its `SAT`
  example likewise omits `max_time`). Not requested by this task, but the same root-cause pattern
  (missing `max_time` headroom on bimodal examples in this file) applies; worth a follow-up if the
  team wants this file's remaining flakiness addressed in one pass.
