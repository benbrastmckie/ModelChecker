# Research Report: Extend A2-triangle exhaustive grid to nb=nf=2

- **Task**: 193 - Extend A2-triangle encoding-completeness test's exhaustive grid to nb=nf=2
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T00:00:00Z
- **Effort**: ~1.5 hours (codebase reading + direct measurement scripts)
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` (module docstring)
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (`LabelledLasso`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`DEFAULT_EXAMPLE_SETTINGS`)
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` section 7.3
  - `code/docs/core/TESTING_GUIDE.md` section 8.11 (CI timeout guard)
  - `code/pyproject.toml` (`slow` marker registration)
  - Direct measurement: three ad hoc scripts run under `PYTHONPATH=code/src python3`, driving the
    real `Syntax -> ModelConstraints -> BimodalStructure` pipeline and a corrected candidate
    generator, to obtain exact candidate counts and wall-clock timings (not estimated from the
    existing docstring alone)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The current test hard-codes `back=mid=fwd=1`. Production's actual default settings
  (`BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` in `core.py:108-122`) are already
  `back=2, mid=1, fwd=2` — i.e. the historical bug's exact regime (`nb=2`) is what real runs use
  by default, and the existing test cannot regression-guard it.
- `_candidates()` in the test module hard-codes single-element tuples
  (`back=(back_label,)`, `mid=(mid_label,)`, `fwd=(fwd_label,)`) — this only produces valid
  `LabelledLasso` instances when `nb=nm=nf=1`. Extending the grid requires building
  segment tuples of length `nb`/`nm`/`nf` respectively (verified working via a generalized
  generator, below). `_expected_candidate_count`'s formula (`(2**closure_size)**(3*lassos) * ...`)
  is similarly hard-coded to the `nb+nm+nf=3` case and needs the exponent generalized to
  `slots_per_lasso * lassos` where `slots_per_lasso = nb+nm+nf` (== `len(target_window())` always).
- **Measured, not estimated**, real candidate counts and wall-clock times at `back=2, mid=1, fwd=2`
  for the three closures the existing test already covers:
  - `box_free_until` (closure size 3, 1 lasso, 0 boxes): 163,840 candidates, 926 accepted,
    Z3 SAT — **1.06s**. Affordable unconditionally (no `slow` marker needed).
  - `box_free_contra` (closure size 1, 1 lasso, 0 boxes): 160 candidates, 0 accepted,
    Z3 UNSAT — **~0s**. Affordable unconditionally.
  - `boxed` (`\Box A |- B`, closure size 3, 2 lassos, 1 box): **10,737,418,240 candidates**,
    extrapolated **~19 hours** at the measured ~6.4us/candidate re-check rate. Not affordable at
    any tier — see Finding below.
- **Governing constraint**: CI runs every test under `--timeout=300 --timeout-method=thread`
  (`code/docs/core/TESTING_GUIDE.md` section 8.11) — the `slow` marker does **not** exempt a test
  from this budget; it only controls local `-m "not slow"` deselection (`code/pyproject.toml:93`).
  This caps what "tier or mark it `slow`" can mean: `slow` buys headroom under 300s, not unbounded
  runtime.
- No genuine three-way (recheck / Z3-SAT) disagreement was found at `nb=nf=2` for any measured
  closure — all three agree with the existing `back=mid=fwd=1` verdicts' direction (SAT/UNSAT
  unchanged). This is expected: the specific historical defect (narrow-window local coherence) was
  already fixed at `task 184` phases 7-8 (`git log` on `witness_constraints.py`); this task adds
  forward regression coverage, it does not chase a currently-live bug.

## Context & Scope

Task 193 asks to extend `test_certificate_a2_triangle.py`'s Tier 1 exhaustive grid past
`back=mid=fwd=1` to `nb=nf=2`, motivated by `witness_constraints.py`'s module docstring: the
now-fixed narrow-window local-coherence bug required `nb=2` to manifest (slot `back[1]` recurring
at every odd-magnitude position), and the current test's `nb=1` grid is structurally blind to that
whole defect class. The dispatch explicitly requires measuring the `nb=nf=2` candidate count
*before* committing to unconditional execution, tiering/marking as needed, keeping the existing
three closures' coverage intact, keeping Tier 2's clean-skip discipline, and treating any genuine
three-way disagreement as a reportable finding rather than something to diagnose here.

## Findings

### 1. `_candidates()`'s tuple construction does not generalize past nb=nm=nf=1

`test_certificate_a2_triangle.py:122-131` builds each lasso as:

```python
LabelledLasso(back=(back_label,), mid=(mid_label,), fwd=(fwd_label,))
```

`LabelledLasso.nb`/`nm`/`nf` are `len(self.back)`/`len(self.mid)`/`len(self.fwd)`
(`certificate.py:86-95`), and `WitnessRegistry.wrap` (`witness_registry.py:112-118`) indexes
`back[t % nb]` etc. — so a `back` tuple of length 1 is only correct when the registry's own
`nb == 1`. At `nb=2`, each lasso needs a 2-element `back` tuple (independently chosen per slot),
not one label reused for both slots. This was verified directly: a corrected generator (below)
that builds `itertools.product(labels, repeat=nb)` / `repeat=nm` / `repeat=nf` per segment,
combined via `itertools.product` across the three segments, reproduces the closed-form candidate
count exactly (see Finding 2) and drives `recheck` to completion with plausible SAT/UNSAT verdicts.

### 2. `_expected_candidate_count`'s exponent is hard-coded to `3`

`test_certificate_a2_triangle.py:152-159` computes
`(2**closure_size) ** (3 * lassos) * (2**boxes) * target_window_len`. The `3` is `nb+nm+nf` at the
current `back=mid=fwd=1` fixture, not a general constant. The correct exponent is
`slots_per_lasso * lassos`, where `slots_per_lasso = registry.nb + registry.nm + registry.nf`
(`witness_registry.py:105-107`, exposed as `WitnessRegistry.slots_per_lasso`). Note the identity
`target_window_len == slots_per_lasso` always holds (`target_window()` is
`range(-nb, nm+nf)`, length `nb+nm+nf`) — the current code's use of the *separately computed*
`target_window_len` for the trailing multiplicand and a hard-coded `3` for the exponent silently
relied on this identity without naming it; genuinely generalizing the test should name it (e.g.
compute `slots_per_lasso` once and use it for both).

### 3. Measured candidate counts and timings (real runs, not estimates)

All measurements below ran the actual `Syntax -> ModelConstraints -> BimodalStructure` pipeline
(`_build`'s own construction order) with a corrected candidate generator, then timed the full
`recheck` loop exactly as `_run_exhaustive_triangle` does. Formula-derived totals
(`(2**|C|)**(slots*lassos) * 2**boxes * window`) matched the measured `total` in every case,
confirming Finding 2's generalized formula.

| Closure (premises/conclusions) | \|C\| | lassos | boxes | slots (nb+nm+nf) | total candidates | accepted | Z3 | wall time |
|---|---|---|---|---|---|---|---|---|
| `[] / (q \Until p)` (box-free, existing) | 3 | 1 | 0 | 3 (nb=mid=fwd=1) | 1,536 | 52 | SAT | <0.1s (existing) |
| `[] / (q \Until p)` at nb=2,mid=1,fwd=2 | 3 | 1 | 0 | 5 | **163,840** | 926 | SAT | **1.06s** |
| `A / A` (box-free, existing) | 1 | 1 | 0 | 3 | 24 | 0 | UNSAT | <0.1s (existing) |
| `A / A` at nb=2,mid=1,fwd=2 | 1 | 1 | 0 | 5 | **160** | 0 | UNSAT | **~0s** |
| `\Box A / B` (boxed, existing) | 3 | 2 | 1 | 3 (nb=mid=fwd=1) | 1,572,864 | 96 | SAT | 10.11s (measured; docstring says ~11s) |
| `\Box A / B` at nb=2,mid=1,fwd=2 | 3 | 2 | 1 | 5 | **10,737,418,240** | not run | — | **extrapolated ~19.2 hours** (6.4us/candidate x 10.7B) |
| `\Box A / A` (smaller boxed closure, new) | 2 | 2 | 1 | 5 (nb=2,mid=1,fwd=2) | **10,485,760** | 0 | UNSAT | **65.47s (measured, full run)** |

The two box-free closures are cheap at `nb=nf=2` (well under a second combined) and need no
`slow` marker to stay affordable. The existing boxed closure (`\Box A |- B`, closure size 3) is
categorically not affordable at `nb=nf=2`: even one-sided extension (`back=2, mid=1, fwd=1` only,
leaving `fwd=1`) computes to 134,217,728 candidates, extrapolated ~14.4 minutes (864s) — still
far past the CI per-test budget (see Finding 4). A smaller boxed closure (`\Box A |- A`, the T-axiom
shape, closure size 2 rather than 3) is fully exhaustively affordable at the full `nb=nf=2` grid:
measured at 65.47s wall clock for all 10,485,760 candidates, comfortably inside CI's 300s budget
even after accounting for the `slow`-marked precedent's own measured/actual variance (the existing
single-box case's docstring estimate of ~11s measured at 10.11s here — same order of magnitude).

### 4. CI's per-test 300s timeout is the binding constraint, not the `slow` marker

`code/pyproject.toml:93` registers `slow` as running "in the default suite" — `-m "not slow"` is
purely a *local* dev-loop deselection, not a CI exemption. `code/docs/core/TESTING_GUIDE.md`
section 8.11 documents CI passing `--timeout=300 --timeout-method=thread` on every test run,
independent of markers. This means the dispatch's instruction to "tier or mark the test
accordingly (the slow marker is already registered)" cannot rescue an exhaustive run past ~300s —
`slow` only signals "expensive but still bounded," it does not lift the hard per-test wall-clock
ceiling. This rules out extending the *existing* boxed closure's exhaustive grid to `nb=nf=2` (or
even one-sided `nb=2` alone) as a `slow`-marked test: both blow the 300s ceiling by 3-4 orders of
magnitude / ~3x respectively.

### 5. No disagreement found at nb=nf=2 (expected, not a live bug hunt)

All three measured `nb=nf=2` runs above agree in direction with their `nb=mid=fwd=1` counterparts
(`(accepted > 0) == z3_model_status` holds in every row). `git log --oneline -- witness_constraints.py`
shows the narrow-window fix landed at `task 184` phases 7-8 (commits `6d74e29f`, `8d493a17`) —
the module's own docstring already describes the fix as shipped, past tense. This task's grid
extension is therefore a regression guard against re-introducing that class of bug, not an attempt
to surface a currently-live one; finding no disagreement is the expected, correct outcome here.

## Decisions

None made in this research phase — the following are recommendations for the plan phase.

## Recommendations

1. **Generalize `_candidates()` and `_expected_candidate_count()`** to build/derive from
   `nb`/`nm`/`nf`-shaped tuples and `slots_per_lasso` rather than hard-coded length-1 tuples and a
   literal `3`, per Findings 1-2. This is required infrastructure regardless of which grid points
   are added.
2. **Add the two box-free closures at `nb=2, mid=1, fwd=2`** (matching production's actual
   default settings) as new, unconditional (non-`slow`) Tier 1 parametrize cases, using the
   measured exact counts from Finding 3's table (`total=163,840, accepted=926, sat=True` and
   `total=160, accepted=0, sat=False`). Combined wall time ~1.06s — negligible addition to the
   suite.
3. **Do not attempt to extend the existing boxed closure (`\Box A |- B`, closure size 3) to
   `nb=nf=2` exhaustively** — it is ~19 hours extrapolated, and even the smallest one-sided
   extension (~14.4 minutes) exceeds CI's 300s per-test timeout by ~3x. This is a hard infeasibility
   under the current CI harness, not a tuning problem.
4. **For box-carrying coverage at `nb=nf=2`, use a smaller boxed closure instead** (e.g.
   `\Box A |- A`, closure size 2, the reflexivity/T-axiom shape) as an *additional* `slow`-marked
   Tier 1 case, measured at 65.47s for the full exhaustive grid — comfortably inside the 300s
   budget. This keeps the box-guess and two-lasso dimensions covered at `nb=nf=2` without touching
   the existing size-3 boxed closure's coverage (per the dispatch's "keep the existing three
   closures' coverage intact"). Any other closure-size-2 boxed example with a different expected
   SAT/UNSAT verdict would also work, if the plan phase prefers exercising the SAT direction here
   too (the smaller closure explored above happened to be UNSAT/valid on both legs) — actual counts
   and timing should be re-measured for whichever specific formula is chosen, since exact
   `accepted` counts and SAT direction are formula-dependent even at matching `slots`/`lassos`.
5. **Leave Tier 2 (`TestBoundedLeanCrossCheck`) untouched.** Nothing above changes leg (ii)'s
   sampling discipline or its `skipif(SKIP_REASON)` clean-skip behavior; the dispatch's "keep
   Tier 2's clean-skip discipline" requirement needs no code change, only avoidance of
   accidentally coupling Tier 2's sample generation to whatever new candidate-generator shape
   Recommendation 1 introduces (verify `_sampled_candidates` still calls the generalized
   `_candidates()` correctly for the existing `nb=mid=fwd=1` closures it already covers).
6. **Update `ADEQUACY.md` section 7.3's prose** (lines 608-617) to note the additional `nb=nf=2`
   coverage once implemented, alongside the still-standing coverage gap for the size-3 boxed
   closure at that grid size — the section already states "the deciding test... standing in this
   repository's suite" and lists what the three existing closures cover; a one- or two-sentence
   addendum keeps the doc in sync with the strengthened test rather than leaving it describing
   only the narrower `back=mid=fwd=1` case.

## Risks & Mitigations

- **Risk**: choosing a different boxed formula (Recommendation 4) for the `nb=nf=2` box case might
  be read as "weakening" Tier 1's coverage rather than adding to it. **Mitigation**: keep the
  existing `\Box A |- B` (closure 3) case fully unchanged at `nb=mid=fwd=1`; the new smaller-closure
  case is purely additive, and the report above documents exactly why the original closure cannot
  be reused at this grid size (Finding 3-4).
- **Risk**: wall-clock measurements in this report are host-specific (single measurement each, no
  repeated trials). **Mitigation**: the measured single-box baseline (10.11s) closely matches the
  test module's own pre-existing docstring estimate (~11s), giving confidence the measurement
  methodology and this host's timing are consistent with what is already trusted in the suite;
  the new 65.47s figure has ~4.5x headroom under the 300s CI ceiling, tolerant of reasonable
  host-to-host variance.
- **Risk**: a future closure size or `max_witnesses` change could silently push the new `nb=nf=2`
  box-free or boxed cases' `expected_closure_size` assertion to fail (as the existing
  `_assert_exhaustive_triangle_agrees` already guards for the `nb=mid=fwd=1` cases). **Mitigation**:
  none needed beyond reusing the existing `expected_closure_size` assertion pattern for the new
  parametrize entries — already designed to fail loudly rather than silently drift.

## Appendix

- Formula validated: `total_candidates = (2**|C|) ** (slots_per_lasso * lassos) * 2**boxes *
  target_window_len`, with `slots_per_lasso == target_window_len == nb+nm+nf` always. Matched
  exactly against measured totals for all rows in Finding 3's table.
- `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` (`core.py:108-122`): `back=2, mid=1, fwd=2,
  max_witnesses=None, max_time=1, expectation=True, iterate=1, solver='z3'` — i.e. `nb=nf=2` is
  the framework's actual default, not an arbitrary choice for this task's grid extension.
