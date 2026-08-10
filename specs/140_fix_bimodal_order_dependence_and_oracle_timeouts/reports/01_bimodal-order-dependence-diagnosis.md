# Diagnosis: bimodal cross-example order dependence and oracle-suite residual RED

- **Task**: 140 — fix bimodal order dependence and oracle timeouts
- **Branch**: `task-140-fix-bimodal-order-dependence`
- **Commits**: `71d437bd` (root-cause fix + baseline-script repairs), `47911792` (BM_CM_4 A/B
  diagnosis), `7f7269d6` (xdist_serial markers)
- **Status of this report**: written retroactively. This task was created directly into
  `implementing` and never passed through research or planning, so no report existed while the
  work was done. The findings below are reconstructed from the implementation summaries, the
  orchestrator handoffs, the committed code and its inline documentation, and measurements taken
  directly during orchestration.

---

## 1. Summary

Two genuinely distinct defect classes were conflated under the label "order dependence". Keeping
them apart is the main analytical result of this task, because they have different mechanisms,
different evidence signatures, and different correct fixes.

| Class | Mechanism | Signature | Correct fix |
|---|---|---|---|
| **A. State leakage** | A process-global counter leaked run-order-dependent state across examples despite per-example Z3 `Context` isolation | Deterministic; reproducible from a seed value; independent of machine load | Fix the leak at its source |
| **B. CPU contention** | Genuine multi-second Z3 solves run near their budget and lose the race only under the gating suite's 6-way parallel pass | Nondeterministic; flips between runs; passes serially at every commit tested | Route to the contention-free serial pass; **never** widen the budget |

Class A was the real defect and is fixed. Class B was pre-existing, is not a regression, and was
addressed by scheduling rather than by relaxing any budget.

---

## 2. Root cause (class A): an unreset process-global bound-variable counter

`bimodal/operators.py` names every quantifier-bound Z3 `Int` via a module-global
`itertools.count()` (`_bound_var_counter`, backing `_fresh_bound_int`). The counter exists to
guarantee distinct bound-variable names within a Z3 `Context`, which is a real requirement — a
plain counter rather than `z3.FreshInt` is deliberate.

`isolated_z3_context()` gives each example a brand-new `z3.Context` and resets the similarly
process-global `AtomSort` cache alongside it — **but it did not reset this counter**. So the
numeric suffix baked into each bound variable's name still depended on how many prior examples in
the same process had called `_fresh_bound_int`.

That leaked suffix is not cosmetic. It is enough to change Z3's MBQI-driven quantifier
instantiation path, and thereby to flip an example's countermodel search between success and
failure purely as a function of how many examples ran before it.

### Evidence

The decisive measurement is a seed bisection, run outside pytest to remove the test harness as a
variable:

- Pre-seeding the counter at **17** — the exact value reached after `EX_CM_1`, `MD_CM_1..6`,
  `BM_CM_1`, `BM_CM_2` in `test_bimodal.py`'s fixed parametrize order — reproduces `BM_CM_4`'s
  failure **deterministically**.
- Every other seed tested (**0, 5, 10, 13, 15, 16, 18, 20, 25, 30**) passes.

A single-value cliff between 16 and 18 is the signature of a discrete state dependency. It is
inconsistent with a monotonic timing race, which would degrade gradually with load and would not
recover at 18 after failing at 17.

### Fix

`reset_bound_var_counter()` in `operators.py`, called from
`BimodalSemantics._reset_global_state()` — once per fresh `BimodalSemantics` instance.

This cannot reintroduce the aliasing bug the counter exists to prevent. That bug requires two
calls resolving to the same name *within one Context*; since each instance is built inside its own
fresh Context, a counter reset to 0 at the start of that Context's lifetime still hands out
strictly increasing, therefore distinct, suffixes for every call made against it.

Regression coverage: `bimodal/tests/unit/test_bound_var_counter_isolation.py` encodes the seed
reproduction so the mechanism cannot silently return.

### A competing hypothesis that was ruled out

An archived diagnosis of a superficially identical symptom
(`specs/archive/130_stabilize_order_dependent_builder_test/reports/01_order-dependent-test-diagnosis.md`)
concluded "a timeout race, not state leakage": a test silently inheriting
`BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS['max_time'] = 1` against a ~1.7s solve. That report
explicitly searched for and ruled out `get_theory` caching, settings-merge mutation, module-level
`z3.Context()`/`set_param()`, and memoized solvers — but it did not examine the bound-variable
counter.

It does not apply here: `BM_CM_4` carries an explicit `max_time=30` and inherits no tight default.
Both findings are correct about their own targets. The lesson is that "order-dependent bimodal
test" has at least two distinct causes in this codebase, and the archived report's suspect list,
though thorough, was not exhaustive.

**Note for future work**: task 130's recommended remedy was to add `max_time` headroom. That
remedy was unavailable here — this task's constraints forbid widening any timeout budget — and
that constraint is what forced the search to continue until the actual state leak was found. Had
budget-widening been permitted, the counter defect would plausibly still be latent.

---

## 3. Class B: contention, not correctness

Three `BM_CM_4`-named oracle tests began failing in the gating suite's parallel pass. Because they
appear in no previously recorded run, the serious hypothesis was that the class-A fix caused them:
the reset changes which counter value the oracle's `BM_CM_4` solves at, and the bisection above
proves that value matters.

A clean A/B settled it. All three run **serially**, inside `nix develop`:

| Commit | Result |
|---|---|
| HEAD (post-fix) | `3 passed in 59.55s` |
| `29e1fdec` (pre-fix, via throwaway `git worktree`) | `3 passed in 31.07s` |

Both pass. The failures are therefore artifacts of the `-n 6` parallel pass, not a regression.
Corroborating evidence: across gating runs the failing subset varied (3 failures, then 2, with
`test_countermodel_bm_cm4_at_example_settings` passing in the later run) — nondeterminism that a
genuine semantic failure would not exhibit.

`test_mixed_and_box_next` is the same class: a stable ~44–45s solve (44.16s, 44.82s measured
serially) against an unchanged 60000ms budget, ~25% headroom, failing only under contention.

### Fix, and what was deliberately *not* done

The established repo precedent for this profile (`test_mixed_or_diamond_prev`) was
`timeout_ms 60000→150000` **plus** `xdist_serial`. The budget half of that was declined by explicit
user decision; only the scheduling half was applied:

- `@pytest.mark.xdist_serial` on `test_mixed_and_box_next` and
  `test_countermodel_bm_cm4_at_example_settings`
- **Per-parameter** marks — `pytest.param(k, v, marks=pytest.mark.xdist_serial) if k == "BM_CM_4"`
  — on the two parametrized regression tests

The per-parameter form matters. A function-level marker on those two tests would have moved all
~42 parametrized cases in each file (~84 instances) into the serial pass, against roughly 130s of
remaining slack in its 900s budget. Test IDs were verified unchanged after the edit:
`[BM_CM_4-example_case9]` and `[BM_CM_4-example_case8]` still collect under exactly those names.

No budget, pin, conclusive floor, `xfail`, `strict=True`, assertion, or guard was weakened
anywhere. `verify-refactor.sh` and the 43-pass baseline were never touched.

---

## 4. The environment trap

Adjudication is only valid inside `nix develop`. Bare-PATH python (3.13.13) reports Step 4 as
298/298 green where the devShell (3.12.13) reliably failed.

The divergence is not only interpreter version. It includes **missing test plugins**:
`pytest-timeout` was installed on bare PATH but absent from the devShell, so
`compare_bimodal_baseline.sh`'s `--timeout=120` produced pytest exit code 4,
`unrecognized arguments`. Under `set -euo pipefail` that aborted the command substitution, and the
gate reported "compare_bimodal_baseline.sh reported regressions" when in fact **nothing had ever
been compared**.

This is the most transferable finding in the task: a green result whose provenance is a bare-PATH
run is not evidence, and a red result may be reporting a harness failure rather than a test
failure. `pytest-timeout` was added to `flake.nix` additively; `--timeout=120` was deliberately
retained, being a timeout budget under the no-weakening constraint.

---

## 5. Baseline-script defects repaired

`code/scripts/compare_bimodal_baseline.sh`:

1. **Masking** — pytest exit codes are now distinguished: 0/1 comparable and proceed, ≥2
   untrustworthy and a hard error with the tail of pytest output. The script also refuses to
   compare when `-v` output parses to zero result lines, rather than reporting a false "all tests
   missing".
2. **Stale default path** — the no-argument default pointed at
   `specs/097_optimize_build_frame_constraints/baseline_results.txt`, archived long ago; it now
   resolves to the archive location. (`verify-refactor.sh` was unaffected, passing the path
   explicitly.)
3. **"EXTRA tests" mislabelling** — root cause was not cosmetic: pytest restates `FAILED` lines in
   its "short test summary info" section, so every failing test was captured twice, desyncing the
   name lists and making `comm(1)` report a duplicate as new. Fixed by anchoring the grep to the
   `[ NN%]` per-test progress marker.

---

## 6. Verified results

All inside `nix develop` (python 3.12.13, z3 4.16.0, xdist 3.8.0).

**Model-checker side — green:**

| Invocation | Result |
|---|---|
| `test_bimodal.py` alone | `43 passed` ×3 (29.22s / 28.89s / 30.30s) |
| Full `bimodal/tests/` | `302 passed` ×2 (184.60s / 175.82s) |
| `compare_bimodal_baseline.sh` | `Baseline: 43 passed / Current: 43 passed, 0 failed` — `0 regressions` |
| `verify-refactor.sh --skip-oracle` | Steps 1–5, 7 OK; Step 4 green on first attempt (previously needed its documented retry) |

`BM_CM_4` now passes in isolation, within the full `test_bimodal.py` file, and within the full
`bimodal/tests/` directory. The previously recorded isolated-run failure is gone.

**Gating oracle suite (Step 6) — see section 7.**

---

## 7. Gating suite (Step 6): now GREEN, with one caveat that must not be lost

| Run | Pass 1 (`-n 6`, budget 1300s) | Pass 2 (serial, budget 900s) |
|---|---|---|
| Before any markers | `4 failed, 584 passed, 2 skipped, 4 xfailed in 551.00s` — FAILED | `10 passed in 795.70s` — PASSED |
| After `test_mixed_and_box_next` marker | `2 failed, 585 passed, 2 skipped, 4 xfailed in 517.32s` — FAILED | `11 passed in 770.48s` — PASSED |
| **After all three markers** | **`584 passed, 2 skipped, 4 xfailed in 802.93s` — PASSED** | **`14 passed, 592 deselected in 869.58s` — PASSED** |

The gating oracle suite is green end to end for the first time. Zero failures in either pass.

### The caveat: pass 2 is at 96.6% of its budget

`869.58s` against a `900s` ceiling leaves **30.4 seconds of slack**. This is the direct and
predicted cost of the marker-only approach: every test routed out of the contention-free parallel
pass lands in a serial pass whose budget was not (and, under this task's constraints, could not be)
raised to accommodate them.

The margin is load-sensitive, and the measurement above was *not* taken on a quiet machine — system
load rose from 6.48 at launch to 11.19 mid-run from unrelated concurrent work. For calibration, the
same pass took 770.48s with 11 tests under lighter load; the three added `BM_CM_4` cases account for
roughly 60s of the increase and contention for the remainder.

**This green should be expected to flake on a loaded machine.** It is a real green — nothing was
weakened to obtain it — but it is not a comfortable one, and treating it as settled would be a
mistake. See section 9.

Two symptoms recorded in the original task description did **not** reproduce and should be treated
as stale: `test_mixed_and_all_future_neg` (recorded as a pass-1 timeout) now passes, and
`test_temporal_propositional_interleaving`'s recorded 900s non-termination did not recur.

### End-to-end gate verification

A full `verify-refactor.sh` run (not `--skip-oracle`) confirms Step 6 against the real gate rather
than by composition:

| Step | Result |
|---|---|
| 1 — in-package bimodal collection | OK, 302 collected (baseline 289) |
| 2 — full in-package collection | OK, 2181 collected (baseline 2100) |
| 3 — oracle collection counts | **2 FAILED** (see below); total OK at 606; partition OK |
| 4 — bimodal in-package suite | OK, **green on first attempt** (no retry needed) |
| 5 — cross-oracle accommodation guard | OK |
| 6 — **gating oracle suite** | **OK, green across both passes** (a strict-xfail XPASS would have failed this run) |
| 7 — `compare_bimodal_baseline.sh` | OK, `0 regressions (matches baseline)` |

The two Step 3 failures are bookkeeping, not regression:

```
FAIL: oracle gating-parallel collection count is '590', expected exactly 594
FAIL: oracle xdist_serial collection count is '14', expected exactly 10
```

These are precisely the four relocated solves — four fewer in the parallel pass, four more in the
serial pass. The suite total is unchanged at 606 and the partition invariant still holds
(`590 + 14 + 2 = 606`). The pins are working exactly as intended: they detected a deliberate
redistribution and are asking to be told it was deliberate. The gate's own message prescribes the
remedy — "re-pin all four `BASELINE_ORACLE_*` values together".

Re-pinning was deliberately deferred rather than done here, for two reasons. First,
`verify-refactor.sh` is named in this task's no-weakening constraint, and the authorization
obtained covered the `xdist_serial` markers only. Second, and more practically: if the serial-pass
capacity decision (section 9) raises the budget, moves tests back out, or makes those solves fast
enough to return to the parallel pass, the distribution changes again — so pinning now would mean
pinning twice. The re-pin is therefore owned by the capacity follow-up, to be done once, after the
final distribution is known.

---

## 8. Standing cautions

1. **Re-measure before trusting any recorded failing set.** The failing set moved twice on an
   unchanged tree during this task. Figures in the task description were already stale when the
   work began (`2 failed, 41 passed` was recorded; `1 failed, 42 passed` was measured).
2. **Never adjudicate from a bare-PATH run.** See section 4.
3. **Distinguish class A from class B before choosing a fix.** Determinism under seed control is
   the discriminator: class A reproduces from a value, class B varies with load.
4. **Contention measurements require a quiet machine.** One diagnostic during this task was
   invalidated by CPU contention self-inflicted by launching a background suite run moments
   earlier, and was correctly discarded as a dead end rather than reported.

---

## 9. Recommended follow-up

The gating suite is green but pass 2 has 30.4s of slack against a 900s ceiling (section 7). Three
options exist, and the choice is a policy decision rather than a technical one:

1. **Raise `ORACLE_PASS2_TIMEOUT`.** Out of scope for this task by explicit constraint, and
   deliberately not done. It is the obvious remedy and should be considered on its merits by
   whoever owns that budget — the serial pass now legitimately carries more work than when its
   budget was set, so this would be an honest adjustment rather than a fudge to obtain green.
2. **Reduce what the serial pass carries.** The four `xdist_serial`-routed solves are genuinely
   slow (`test_mixed_and_box_next` ~44s; three `BM_CM_4` cases ~15–24s each). Making those solves
   faster attacks the cause rather than the symptom, but requires semantic work on the encoding.
3. **Accept and monitor.** Record that pass 2 is expected to flake under load, and treat a pass-2
   timeout as a capacity signal rather than a correctness regression.

Option 1 is the lowest-effort path to a durable green and is recommended, provided it is done as a
deliberate capacity decision with the reasoning recorded — not as an incidental fix during
unrelated work.

**Process note.** This task was created directly into `implementing`, skipping research and
planning. The costs were concrete: no phase checklist meant the orchestrator's drift detection
could not run and phase counts were self-reported (one handoff recorded
`"plan_markers_verified": false`); preflight failed with `No plan file found` on every cycle; and
outcomes had to be reconstructed from logs and git twice because dispatches left the orchestrator
handoff stale. The diagnostic nature of the work made a pre-written plan of limited value — three
successive hypotheses were wrong before the counter was found — but the artifact trail should have
been built incrementally rather than retroactively.
