# Research Report: Diagnose BM_CM_4 Deterministic Countermodel Failure

- **Task**: 188 - Diagnose BM_CM_4 deterministic countermodel failure
- **Started**: 2026-09-25T16:10:07Z
- **Completed**: 2026-09-25T17:05:00Z
- **Effort**: ~1 hour (research only; no source-tree edits)
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (UNSTABLE_EXAMPLES, KNOWN_TIMEOUT_EXAMPLES, the stale NOTE at line 69)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bound_var_counter_isolation.py`
  - `code/src/model_checker/theory_lib/bimodal/examples.py` (BM_CM_4_settings, lines 421-451)
  - `code/src/model_checker/theory_lib/bimodal/operators.py` (`_fresh_bound_int`, `reset_bound_var_counter`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` (`build_seriality_constraint`, `build_interpolation_constraint`, `build_frame_constraints`, `_reset_global_state`)
  - `code/docs/core/TESTING_GUIDE.md` sections 8.9 (`unstable`) and 8.14 (`development`)
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
  - Git history: `f9cc081e` (task 153 phase 4), `dd6af8f6` (task 153 phase 7), `a150f7cb` (task 153 phase 8), and `specs/archive/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/README.md`
  - Live empirical probes against the current committed tree (see Findings; no `core.py` edits made — monkeypatching confined to throwaway scratch scripts)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **Diagnosis settled: this is case (a), a pure solve-cost regression, not (b) unreachability or (c) a semantic failure.** BM_CM_4's countermodel genuinely exists and is found quickly by the current encoding; the deterministic failure is Z3 exhausting `max_time=120` before deciding, not a changed logical conclusion.
- **Root cause and culprit commit are already known and documented, just not propagated to BM_CM_4's own comments/markers.** Commit `f9cc081e` (task 153 phase 4, "implement and wire Skolemized Seriality/Interpolation") added `build_seriality_constraint`/`build_interpolation_constraint` to `build_frame_constraints`. Its own commit message and `specs/archive/153_.../baselines/README.md` already record BM_CM_4 regressing from a 4.07s decided `match` to `inconclusive` at 120s+, reproduced by four independent measurements at the time. Nothing has changed in `core.py`/`operators.py` since (confirmed: git log shows no touches after `3555a864`, and the adequacy-theorem commits `9f0c8ea0..10a30085` are confirmed by the task description to have left these files untouched).
- **Task 153 landed both axioms deliberately, with the regression accepted and the whole bimodal theory taken off the CI gate** via a theory-wide `development`-marker blanket (`bimodal/tests/conftest.py`'s `pytest_collection_modifyitems`, authorized as TESTING_GUIDE 8.14's one recorded exception). This is why the failure is real, deterministic, and reproducible today, yet invisible to gating CI: bimodal's own test tree is excluded from every gating `-m` expression. It is not, however, tracked as `unstable` for this specific example, and the per-example comments (BM_CM_4_settings, test_bimodal.py:69) are now stale/false, exactly as the dispatch states.
- **New finding this session: a purely cosmetic Z3-symbol rename inside `build_seriality_constraint`/`build_interpolation_constraint` recovers a fast, decided `match` for BM_CM_4** — consistently ~2s instead of timing out at the budget, reproduced 3/3 runs, and stable across all three bound-var-counter states the isolation test parametrizes (0, 17, 30). Renaming *either* axiom's symbols alone (keeping the other axiom's real, committed names) is independently sufficient to recover a decided result. This is Z3 MBQI/E-matching's documented sensitivity to incidental term construction (already flagged in task 153's own baseline README via the `serial_succ` vs `serial_succ_inline` discrepancy), not a semantic effect — the rename changes no logical content, only Z3 symbol identifiers.
- **The stale claims that must be corrected regardless of which remedy is chosen**: `BM_CM_4_settings`' comment ("The countermodel is still genuinely found on every probed seed") and `test_bimodal.py:69`'s NOTE ("BM_CM_1, BM_CM_2, BM_CM_4 now reliably find countermodels with corrected semantics") are both false as currently worded for BM_CM_4.

## Context & Scope

This is a research-only dispatch (`phase: research`); no `core.py`/`examples.py`/test-file edits were made. The task is to diagnose why `BM_CM_4` (`\Diamond A` / `\past A`, N=2, M=2, `max_time=120`) fails deterministically in `code/src/model_checker/theory_lib/bimodal/tests/`, distinguish (a) cost regression / (b) unreachable countermodel / (c) genuine semantic failure, and recommend a remedy consistent with TESTING_GUIDE.md 8.9. Per the dispatch's explicit scope boundary, the encoding-replacement (certificate-redesign) track is out of scope; this report hands off rather than attempts that track if warranted. It is not.

## Findings

### 1. Independent reproduction of the current failure

A direct, reduced-budget (`max_time=40`) probe against the unmodified, currently-committed `BimodalSemantics` methods reproduced the failure exactly:

```
check_result: "inconclusive", model_found: false, timeout: true, solving_time: 40.205s
```

This matches task 153's own 40.21s isolation-probe figure for the identical scenario (`specs/archive/153_.../baselines/README.md`, "Isolation ... 40s probe budget") to within measurement noise, corroborating that nothing has drifted since task 153 landed — the regression is exactly the one task 153 already characterized, not a new or different failure.

### 2. Bisection is unnecessary — task 153 already bisected and attributed this exactly

Git history for `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and `operators.py` shows no commits after `3555a864` (task 153 phase 6, docs only). The task 153 archive's own regression harness (`baselines/01_frame-axiom-regression-script.py`, `03_post-change-verdicts.json`, `README.md`) already ran the exact bisection this task's dispatch calls for:

- **Phase 1 (pre-change, before `f9cc081e`)**: BM_CM_4 decided `match` in ~18-20s (matching `152`'s recorded baseline), and a pre-Phase-4 git-blob reconstruction measured 4.07s decided `match`.
- **Phase 7 (post-change, after `f9cc081e`)**: BM_CM_4 goes `inconclusive` at 120.36s — four independent measurements, all consistent (isolated pytest run, direct call, full-suite run, 40s-budget probe).
- **Axiom isolation** (`bm_cm4_isolate.py`, cited in the README but not itself committed): with only `seriality` or only `interpolation` present, BM_CM_4 stays decided (9.27s / 6.33s respectively, both modestly slower than the 3.10s `neither` baseline); only with **both** axioms present does it go `inconclusive` at the 40s probe.

The culprit commit is therefore `f9cc081e` (task 153 phase 4, 2026-08-31), which is consistent with the task description's own observation that the adequacy-theorem commits (`9f0c8ea0..10a30085`) touched no semantic source file and therefore cannot be the cause.

### 3. Why "Z3 nondeterminism" is the wrong frame (confirms the dispatch's own point 1-3)

Task 153's own isolation table for `BM_CM_4` shows a monotonic, reproducible pattern (`neither` < `seriality_only` ≈ `interpolation_only` < `both`, with only `both` failing to decide within budget) — the opposite of noisy/nondeterministic behavior. The isolation test's three parametrized bound-var-counter states (0, 17, 30) failing uniformly (confirmed again this session at §5 below) is the signature of a deterministic dependency on the *current* symbol/constraint set, not of run-to-run solver variance. `BimodalSemantics._reset_global_state` (`semantic/core.py:118-122`) resetting `_bound_var_counter` via `reset_bound_var_counter()` is working correctly and is not implicated; it removes counter-*state* as a variable, which is exactly why the failure no longer varies with prior test order — it was never the cause of BM_CM_4's own failure, only of the counter-order-dependence bug the isolation test was originally written to catch (task 140, unrelated).

### 4. The regression is fully accounted for, deliberately landed, and already taken off the gate

Commit `f9cc081e`'s own message records: *"the full bimodal suite surfaced a genuine cost regression on BM_CM_4 ... 4.07s decided match pre-change to inconclusive at 120s max_time with both new axioms ... This is a cost regression, not a shown soundness/verdict flip."* Task 153 phases 7-8 (`dd6af8f6`, `a150f7cb`) then:

- Ran the full 52-example regression diff, confirming exactly 2/52 examples diverge (BM_CM_4 and BM_CM_1 — the latter explicitly out of this task's scope per the dispatch), all other examples unaffected.
- Took the user's landing decision to accept the regression and land both axioms as specified (no axiom dropped, no `max_time` raised, no example's `expectation` adjusted).
- To reconcile "accept a known-failing bimodal example" with "keep the release gate green," applied `@pytest.mark.development` to the **entire bimodal test tree** via a path-scoped `pytest_collection_modifyitems` hook in `bimodal/tests/conftest.py` — the one theory-wide blanket TESTING_GUIDE.md 8.14 authorizes, on the explicit ground that the whole theory (not a list of individually incomplete behaviours) is declared in development. This hook is still present and unchanged (confirmed by reading the current file).

This explains the dispatch's framing precisely: BM_CM_4 is not *literally* undocumented (task 153's summary, this git history, and TESTING_GUIDE 8.14 all record it), but it is **not tracked at the per-example granularity TESTING_GUIDE 8.9 requires** (no `UNSTABLE_EXAMPLES` entry, no corrected settings comment), and the theory-wide `development` blanket is precisely why a full run of `bimodal/tests/` — which does *not* pass `-m "not development"` — still shows the failure deterministically even though no gating CI invocation ever sees it. The 8.14 blanket quarantines *completeness* claims about bimodal from the *release gate*; it does nothing to make BM_CM_4 itself pass, nor does it substitute for 8.9's per-example bar, which is what this task's acceptable outcomes are measured against.

### 5. New empirical finding: a symbol rename recovers a decided countermodel

Given task 153's own baseline README flagged (but did not pursue against the real committed methods) that Z3's MBQI/E-matching is sensitive to "incidental symbol-naming/construction-order differences" — evidenced there by `serial_succ` vs `serial_succ_inline` alone flipping BM_CM_4 from 120s-`inconclusive` to 4.56s-`match` on a *structurally different* script reconstruction — this session tested that hypothesis directly against the real, currently-committed `build_seriality_constraint`/`build_interpolation_constraint`, monkeypatched in-process only (no source-tree edit):

| Probe (all `max_time=40`, budget-capped) | Result |
|---|---|
| Real committed methods, unmodified (baseline confirmation) | `inconclusive`, 40.205s (timeout) |
| Both axioms' Z3 symbols renamed (e.g. `serial_succ` → `serial_succ_r2`), logic byte-for-byte identical otherwise | `match`, 2.25s — repeated 3/3 runs, 2.00-2.25s each |
| Same renamed variant, bound-var counter poisoned to 0 / 17 / 30 (the isolation test's exact parametrize list) | `match` at all three: 2.06s / 1.99s / 1.97s |
| Only `build_seriality_constraint`'s symbols renamed, `build_interpolation_constraint` left at its real committed names | `match`, 1.09s |
| Only `build_interpolation_constraint`'s symbols renamed, `build_seriality_constraint` left at its real committed names | `match`, 2.63s |

All renamed variants are alpha-renamings only — same Skolem-function arity/sort signatures, same `ForAll`/`Implies`/`And` structure, same guard conditions, same `task_rel` calls — so no semantic content changes. This is consistent with, and considerably sharpens, task 153's own unresolved finding: it is not a specific name collision between the two axioms (renaming *either one alone* is independently sufficient), but a general sensitivity of Z3's quantifier-instantiation heuristics to the *particular* symbol identifiers/construction order the current committed code happens to use. The countermodel is not hard to find — it decides in ~2s once any of several innocuous constructions are used — which by itself settles the (a)/(b)/(c) question: (a).

### 6. ADEQUACY.md's soundness caveat does not apply here

The dispatch is right to flag that a known-unsound encoding's verdict is not self-certifying, but that concern is about a "no countermodel" (`mismatch`/failed-to-find) or an unexpected verdict flip, not about a `match` consistent with the documented `expectation: True`. Every decided draw obtained this session (renamed-symbol arm) returns `check_result: "match"` with `model_found: True`, i.e. the same expected verdict BM_CM_4 has always carried. Nothing here disputes or needs to re-litigate ADEQUACY.md's independent finding that the encoding cannot satisfy (SOUND) in general; it is simply not the operative issue for this specific failure.

### 7. Stale documentation identified

- `examples.py:436-446` (`BM_CM_4_settings` comment): "The countermodel is still genuinely found on every probed seed" is false as currently worded — with the current, real, committed code, zero of the measured draws (this session's 40s probe, task 153's four independent measurements, and the dispatch's own seven consecutive pre-existing failures) decide at all, let alone find a countermodel.
- `test_bimodal.py:69`: "NOTE: BM_CM_1, BM_CM_2, BM_CM_4 now reliably find countermodels with corrected semantics" is false for two of the three named examples (BM_CM_1, tracked separately as `unstable`; BM_CM_4, this task). BM_CM_2 is unaffected (not in the 2/52 divergence set from task 153's regression diff) and the claim remains accurate for it.
- Neither `UNSTABLE_EXAMPLES` (`test_bimodal.py`) nor any example-level marker currently names BM_CM_4, despite the theory-wide `development` blanket already existing at the conftest level. These are two independent tracking mechanisms with different granularity and different audiences (release-gate exclusion vs. per-example instability accounting); the theory-wide blanket does not substitute for the per-example bookkeeping 8.9 requires if BM_CM_4 is to be marked `unstable`.

## Decisions

- **Diagnosis is (a): a solve-cost regression caused by commit `f9cc081e`'s Seriality+Interpolation axioms, exacerbated by Z3 MBQI's sensitivity to the specific Z3 symbol identifiers used in their construction.** Not (b) — the axioms do not make the countermodel logically unreachable; renaming symbols with identical logic recovers it in ~2s. Not (c) — every decided draw returns the expected `match` verdict, so ADEQUACY.md's unsoundness caveat is not implicated.
- **No bisection work is needed beyond what task 153 already performed and recorded**; this report independently reproduced both the current failure and task 153's own pre-change reference numbers, closing the loop.
- **This task's scope (bimodal tests/examples.py/semantic edits, no encoding replacement) is sufficient** — the symbol-rename remedy is a small, local, non-semantic change to two existing methods, not encoding replacement, and stays entirely within `code/src/model_checker/theory_lib/bimodal/semantic/core.py`.

## Recommendations

Ranked per the dispatch's own preference order:

1. **Preferred: pursue the genuine fix (Acceptable Outcome 1).** Rename the Skolem functions and bound variables in `build_seriality_constraint` and `build_interpolation_constraint` (e.g. `serial_succ`/`serial_pred`/`serial_w`/`serial_x` and `interp_witness`/`interp_w`/`interp_v`/`interp_d1`/`interp_d2` to any collision-free alternative) — a zero-semantic-content change, already empirically shown (§5) to recover a fast decided `match` across 3 repeated runs and all three bound-var-counter states the isolation test checks. Before landing, the implementation phase must additionally:
   - Run the **full 52-example regression** (task 153's own harness pattern is reusable, `specs/archive/153_.../baselines/01_frame-axiom-regression-script.py`) against the renamed variant to confirm no other example (notably `BM_TH_3`/`BM_TH_4`, which the Skolemized-vs-nested-Exists choice was originally calibrated against) regresses.
   - Run the dispatch's required **>=20-seed sweep with no undecided draw** before treating BM_CM_4 as green — this session's 5 runs (3 unpoisoned + 2 counter-poisoned combinations, plus the two single-axiom-rename arms) are a strong signal but fall short of that bar.
   - Record explicitly, at the rename site, that the fix is empirically-motivated (Z3 MBQI sensitivity), not a principled encoding correction — flag as a known fragility that a future unrelated encoding change in this area could, in principle, re-trigger, and point to `oracle/bimodal_logic/`'s cross-oracle differential suite as the backstop that would catch any accompanying soundness regression (per §6, none is expected here).
   - Correct `examples.py`'s `BM_CM_4_settings` comment and `test_bimodal.py:69`'s NOTE to reflect the actual history (regression from `f9cc081e`, recovered by the rename) rather than deleting the history, per TESTING_GUIDE 8.9's promotion-path convention ("The history of what was tried and what finally worked is worth more than a clean diff").
2. **Fallback if the >=20-seed sweep or full regression surfaces further instability: Acceptable Outcome 3, an `UNSTABLE_EXAMPLES` entry.** Unlike the dispatch's concern that "BM_CM_4 currently cannot make that showing, because it has no decided draws at all," this report's §5 findings *do* now exhibit decided draws (with the renamed construction) — so entry criterion 2 ("demonstrably not semantic") becomes satisfiable if the rename is adopted even provisionally while a wider sweep is completed, or if the rename is judged too fragile to land as a "genuine fix" and is instead cited as the entry criterion 3 evidence ("genuine fix attempted... ") for an `UNSTABLE_EXAMPLES` entry that keeps the *original*, unrenamed axioms and documents the rename as a partial mitigation with a concrete, dated exit criterion (per 8.9's template already used for BM_CM_1).
3. **Not applicable: Acceptable Outcome 2** (correcting the expected verdict) — every decided draw obtained confirms `expectation: True` is correct; there is no evidence to justify changing it.
4. **Regardless of which of the above is chosen**, correct the two stale comments identified in Finding 7 as part of this task, and consider whether `UNSTABLE_EXAMPLES`'s docstring/BM_CM_4_settings should cross-reference `f9cc081e`/task 153 the way `BM_CM_1`'s entry already cross-references its own fix-attempt history, so a future reader does not have to re-derive this chain from git archaeology.

## Risks & Mitigations

- **Risk**: the symbol rename is an empirical mitigation of a Z3 heuristic sensitivity, not a structural fix; a future change to `build_frame_constraints` (new axiom, reordering) could reintroduce a similar pathology under the renamed symbols too. **Mitigation**: the full-regression-plus-seed-sweep gate recommended above is the correct backstop, and the rename should be documented as such (not oversold as "the bug is fixed").
- **Risk**: landing the rename without re-running the full 52-example suite could silently regress `BM_TH_3`/`BM_TH_4` or another example that was previously tuned around the specific committed symbol names. **Mitigation**: explicitly required as a precondition in Recommendation 1, using the already-built task 153 harness.
- **Risk**: this task could be perceived as duplicating task 153's already-thorough investigation. **Mitigation**: this report cites and builds directly on that investigation rather than re-deriving it, and its only genuinely new contribution is the targeted symbol-rename experiment (§5) task 153 did not run against the real committed methods.

## Appendix

- Commits: `f9cc081e` (introduces the regression), `dd6af8f6` (phase 7 full regression diff), `a150f7cb` (phase 8 landing decision + `development` blanket), `3555a864` (last `core.py`/`operators.py` touch prior to this task).
- Archive: `specs/archive/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/README.md` (primary source for the pre-existing regression characterization), `.../summaries/01_seriality-interpolation-axioms-summary.md`.
- `code/docs/core/TESTING_GUIDE.md` sections 8.9 (`unstable`, lines 926-1010) and 8.14 (`development`, lines 1358+).
- `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` — the currently-active theory-wide `development` blanket hook.
- Probe scripts (scratch, not committed): monkeypatch-based reproductions of `build_seriality_constraint`/`build_interpolation_constraint` with renamed Z3 symbols, run in-process via `model_checker.utils.testing.run_enhanced_test` inside `isolated_z3_context()`, mirroring task 153's own harness pattern. Not persisted as repository artifacts since no source change was made this session; the implementation phase should recreate an equivalent script under this task's own `baselines/` if it wants a rerunnable regression check.
