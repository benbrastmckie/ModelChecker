# Research Report: Surface Oracle Timeout Skips and Run Exhaustive Scan

- **Task**: 142 - Two categories of oracle verification currently produce no signal in the gating suite
- **Started**: 2026-08-10T13:51:00-07:00
- **Completed**: 2026-08-10T14:12:00-07:00
- **Effort**: ~1 hour (live measurement + independent ground-truth adjudication)
- **Dependencies**: None
- **Sources/Inputs**:
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` (skip sites, catalogs)
  - `oracle/run-oracle-suite.sh`, `oracle/run-oracle-exhaustive-scan.sh`, `oracle/conftest.py`
  - `oracle/bimodal_logic/ground_truth.py`, `oracle/bimodal_logic/translation.py`
  - `oracle/scan-results/20260807T155847Z/`, `oracle/scan-results/20260810T022056Z/` (prior complete
    exhaustive-scan runs)
  - `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`
  - `code/docs/core/TESTING_GUIDE.md` section 8.6, 8.8
  - `code/src/model_checker/theory_lib/{bimodal,imposition,exclusion,logos}/__init__.py`
  - `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`
  - `code/src/model_checker/builder/tests/{unit/test_example.py,integration/test_performance.py,fixtures/test_data.py}`
  - Live `nix develop` test executions (see Findings for exact commands and elapsed times)
- **Artifacts**: this report

## Executive Summary

- Live-ran the two named timeout-conditional-skip sites (`test_oracle_interface.py:635` and
  `:779`) under `nix develop`; exactly 2 of 76 selected tests skip: `TN_TH_2` (site 635) and the
  `all_future` enriched/primitive pair (site 779), in 948.28s wall clock.
- **`TN_TH_2`'s recorded `expected_sat=False` is wrong**, confirmed by three independent
  signals: the module's own ground-truth evaluator (SAT, stable across three window sizes), a
  live 60s-budget oracle probe (still SAT-shaped: A-always-false is the trivial witness), and
  manual semantics (nothing in `all_future(some_past(A))` forces truth when `A` is false
  everywhere). This is the exact "measured under the old timeout-conflated contract" failure
  mode the skip message itself warns about, now demonstrated concretely.
- The `all_future` skip at site 779 is a genuine, *correctly-labeled* performance gap: ground
  truth confirms the pair's formula is SAT with a simple witness, but the **primitive**
  (`untl`-based) expansion does not decide within 180000ms while the enriched form decides in
  under 2s (confirmed separately at test_oracle_interface.py:826, same pair, same run).
- Found the identical mislabeling pattern in two *already-excluded* `REGRESSION_TIMEOUT_EXAMPLES`
  entries (`TN_CM_1`, `BM_TH_1`, both `all_future(A)`): ground truth says SAT, catalog says
  `False` (UNSAT/valid) — and a direct probe shows `all_future(A)` now decides in 1.79s, meaning
  this exclusion looks stale on both the label and the performance-exclusion rationale.
  `BM_TH_2` (`all_past(A)`), by contrast, has the *correct* label (SAT) but is still genuinely
  slow (60s+ timeout) — an asymmetry with its Until-based mirror worth investigating on its own.
- The exhaustive `-m slow` scan was **not** re-run fresh (current machine load average 5.5-7.6 on
  24 cores, several competing `lean`/`claude`/`pdflatex` processes — not quiet); instead, two
  independently-run, code-current, complete prior runs (2026-08-07, 2026-08-10, both postdating
  the last commit touching the scan machinery) are used as the evidence: `disagreements: 0` both
  times, wall clock 3651.243s (~61 min) and 3555.065s (~59 min), conclusive counts 103/274 and
  105/274 (run-to-run variance of 2 formulas, consistent with the documented near-budget-headroom
  contention sensitivity). Recommendation: leave manual, do not add to the gating path, but do add
  a lightweight periodic (e.g. weekly, off-hours) scheduled run given ~60 minutes is affordable
  unattended and self-consistency drift is otherwise undetectable between manual invocations.
- `bimodal.get_theory(config=None)` genuinely ignores `config` (confirmed: `get_theory(['extensional'])`
  returns all 17 operators, including `\Box`/`\Diamond`/`\Until`/`\Since`/etc.) — but this is not
  a bimodal-specific oversight: `imposition` and `exclusion` share the identical
  `get_theory(config=None)`-ignores-`config` contract, and `test_theory_conformance.py` codifies
  `config` as a uniform-signature placeholder for exactly these three theories (only `logos` has
  real subtheory restriction, via a separate `subtheories=` keyword). At least 15 test-fixture
  files call `bimodal.get_theory([...])` positionally as if it restricted operators; this is
  already self-documented as "a defect in `get_theory`, not [addressed]" in
  `builder/tests/integration/test_performance.py` and `builder/tests/unit/test_example.py`.
  Recommendation: fail loudly on a non-`None` `config` rather than implement real restriction
  (bimodal has no subtheory decomposition to restrict to) — but this requires updating ~15 call
  sites and should be scoped as its own implementation task, not folded into this one.

## Context & Scope

Task 142 asks for three things, adjudicated only inside `nix develop` (bare-PATH python risks
false greens from a missing `pytest-xdist`/`pytest-timeout` or interpreter mismatch):

1. Enumerate which formulas actually skip at the two named timeout-conditional-skip sites on a
   live run, and determine per-formula whether the recorded `expected_sat` is trustworthy.
2. Run the exhaustive `-m slow` scan, record result/runtime, and recommend gated / scheduled /
   manual.
3. Assess `bimodal.get_theory(config)`'s ignored `config` argument: does any caller rely on a
   restriction that doesn't happen, and should the fix be "implement restriction" or "fail
   loudly"?

No timeout was widened and no skip was converted to a failure, per the task's explicit
constraint — this report only measures and records.

## Findings

### 1. Timeout-conditional skips: what actually skips, and is the label trustworthy

**Live run** (`nix develop --command bash -c 'pytest oracle/bimodal_logic/tests/test_oracle_interface.py -v -rs -k "TestOracleExampleRegressionViaAPI or TestEnrichedRoundTrip"'`,
machine load average 5.5-7.6 on 24 cores during the run — moderately loaded by several unrelated
`lean`/`claude`/`pdflatex` processes, not a fully idle machine):

```
74 passed, 2 skipped, 32 deselected in 948.28s (0:15:48)

SKIPPED [1] test_oracle_interface.py:635: 'TN_TH_2': did not decide within 30000 ms
SKIPPED [1] test_oracle_interface.py:779: 'all_future': at least one side did not decide
            within 180000 ms
```

**`TN_TH_2` (site 635, `TestOracleExampleRegressionViaAPI::test_oracle_regression`)** —
`EXAMPLE_JSON_CATALOG["TN_TH_2"] = (all_future(some_past(A)), True, False)`, comment
`"\Future \past A -- UNSAT (valid in these frames)"`.

Adjudicated independently via `bimodal_logic.ground_truth` (the module's own third,
brute-force-unbounded-time evaluator, unfolding the enriched formula to its primitive `untl`/`snce`
form first, since `ground_truth` only supports the 5 primitive temporal-only tags):

```
$ python -m bimodal_logic.ground_truth '<unfolded TN_TH_2>' --window 4   # and 5, 6
{"verdict": "SAT", "witness": {"A": {...all false...}}}   # identical at windows 4, 5, 6
```

A direct 60000ms-budget oracle probe also still times out (does not merely need slightly more
than 30000ms — 60000ms is not enough either), but the semantics are unambiguous without needing
the solver: if `A` is false at every time, `some_past(A)` is false at every time, so
`all_future(some_past(A))` is false at every time — a countermodel, not a validity. **The
recorded `expected_sat=False` is wrong; the correct value is `True` (SAT).** This is precisely
the failure mode the skip message at line 635 warns about ("its ACTIVE_EXAMPLES expected_sat may
itself have been measured under the old timeout-conflated contract") — now confirmed rather than
hypothetical. Because `TN_TH_2` is (correctly) not in `REGRESSION_TIMEOUT_EXAMPLES`, it is a
genuinely *active* example whose wrong expectation has been invisible: a hypothetical future fix
that made the solver actually decide `TN_TH_2` within budget would immediately hard-fail the
regression assertion at line 642 against the wrong label, and nobody would learn why without
this kind of investigation.

**`all_future` pair (site 779, `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement`)**
— unlike `EXAMPLE_JSON_CATALOG`, `ENRICHED_PRIMITIVE_PAIRS` carries no `expected_sat` label; it
only asserts enriched-vs-primitive self-consistency, so there is no "wrong label" question here.
The pair is `enriched = imp(all_future(A), B)`, `primitive = imp(imp(untl(imp(A,bot),imp(bot,bot)),bot), B)`.
Ground truth on the (already-primitive) `primitive_json` directly: `SAT`, with a simple witness
(`A` false through time 0, true after; `B` always false). The *same* enriched formula, tested
alone at `test_oracle_interface.py:826` (`TestEnrichedRoundTrip::test_formula_folded_json_present_all_sat`,
same run, same `ENRICHED_PRIMITIVE_PAIRS` list) decided and **passed** within its 30000ms budget.
So the culprit at site 779 is specifically the **primitive `untl`-based expansion**, which the
module's own docstring already anticipated ("Primitive forms are structurally larger and some
\[...\] do not decide even within the generous TEMPORAL_SOLVE_TIMEOUT_MS budget") — this is a
confirmed, not merely suspected, instance of that gap, and it is a genuine performance problem,
not a labeling problem.

**Cross-check against the already-excluded `REGRESSION_TIMEOUT_EXAMPLES` set** (11 entries,
statically excluded from `ACTIVE_EXAMPLES` so they never run at all, skipped or otherwise —
checked here only because the same "expected_sat may have been measured under the old
timeout-conflated contract" risk applies to them too, and two turned out to be a direct
duplicate of the same bug just found):

| Example | Formula | Catalog label | Ground truth | Live 60000ms probe | Assessment |
|---|---|---|---|---|---|
| `TN_CM_1` | `all_future(A)` | `False` ("UNSAT, valid") | `SAT` (A-always-false) | **1.79s, SAT** | Label wrong; exclusion likely stale (fast + correct-answer-mismatches-label) |
| `BM_TH_1` | `all_future(A)` (identical formula) | `False` ("UNSAT, valid") | `SAT` | 1.79s, SAT (same formula) | Same defect, duplicate entry |
| `BM_TH_2` | `all_past(A)` | `True` ("SAT, invalid alone") | `SAT` (matches) | **60.26s, TIMEOUT** | Label correct; still genuinely slow — Since-side/all_past encoding markedly slower than its Until-side mirror `all_future(A)` for the structurally symmetric formula |
| `TN_TH_2` (active) | `all_future(some_past(A))` | `False` | `SAT` | 60.44s, TIMEOUT | Label wrong (see above); also still too slow to decide even at 2x budget |

`MD_TH_2` (catalog entry: bare atom `A`, trivially fast) was not independently re-probed since
its `EXAMPLE_JSON_CATALOG` JSON is a bare atom regardless of the exclusion comment
("timeout-prone") — this mismatch between a trivial JSON payload and a "timeout-prone" exclusion
reason is itself suspicious and worth a follow-up look, but was not chased further here to keep
scope to the two named sites plus directly-adjacent, already-collected evidence.

**Related but out of the two named sites (found while reading the file, not modified per the
task's "do not convert to failures" constraint)**: `test_oracle_interface.py` has **9** total
`except OracleTimeoutError:` sites, not 2. The other 7, by visibility:
- **Loud already** (good pattern, no change needed): line 1140
  (`test_spot_check_individual_countermodels`) collects an `inconclusive` list and prints it —
  visible without a skip marker.
- **Silent `continue` in a loop, no report at all** (more invisible than a `pytest.skip`, since
  no per-formula signal appears anywhere): lines 1181, 1205, 1233 — each loops over
  `ACTIVE_EXAMPLES` or a small formula dict and silently drops timed-out entries with a bare
  `continue`.
- **Silent bare `return`, reports as `PASSED`** (the most invisible variant — the test shows
  green with zero assertions executed, not even a `SKIPPED` line): line 826
  (`test_formula_folded_json_present_all_sat`, decided fine for `all_future` in this run but is
  structurally capable of a silent pass) and line 930 (`test_deeply_nested_enriched`, explicitly
  documented as intentional — "the test's intent is 'no crash'").
- **Timeout is irrelevant to the assertion**: line 1485 (`find_countermodel` result is discarded
  by design; a stress/isolation test).

This is worth a dedicated follow-up (not this task, per its explicit scope and the "do not
convert skips to failures" constraint): lines 1181/1205/1233's silent `continue` pattern is
strictly worse for visibility than the two named `pytest.skip()` sites, since it produces no
signal in `-rs` output at all.

### 2. Exhaustive scan: result, runtime, and gating recommendation

**Not re-run fresh in this session.** Current machine load (5.5-7.6 on 24 cores, concurrent
`lean` processes at 100%+ CPU each, several other `claude` sessions, an active `pdflatex` build)
is not the "quiet machine" the task requires, and burning another ~60 contended minutes would
produce a run whose timing is not trustworthy evidence of anything — the same
contention-sensitivity `TESTING_GUIDE.md` section 8.6 already documents for this suite. Instead,
two prior complete runs already on disk are used, both **code-current** (both postdate
`7f7269d6`/task-140, the last commit touching `oracle/`) and both produced by the
`SCAN_COMPLETE`-marker-gated pipeline the task itself specifies as authoritative:

| Run | `total_formulas` | `disagreements` | `conclusive` (agreements) | `timeout_count` | `wall_clock_seconds` |
|---|---|---|---|---|---|
| `20260807T155847Z` | 274 | **0** | 103 | 171 | 3651.243 (~60.9 min) |
| `20260810T022056Z` | 274 | **0** | 105 | 169 | 3555.065 (~59.3 min) |

Both agree with the `TESTING_GUIDE.md`-documented real-derivation measurement of 3640.955s
(~60.7 min) and with the manifest's own derivation run (`known_conclusive_complexity5.json`,
`wall_clock_seconds: 3549.987`, `conclusive_count: 103`). The small conclusive-count variance
(103 vs. 105, a 2-formula swing) between otherwise-identical runs is consistent with — not
contrary to — the documented near-budget-headroom sensitivity to machine load: some formulas sit
close enough to `SELF_SCAN_SOLVE_TIMEOUT_MS` that ambient contention flips a handful between
"decided" and "timed out" without indicating any regression (`disagreements: 0` both times is
the property that actually matters, and it held both times).

**Recommendation: leave manual, but add a scheduled periodic run — do not add to the gating
path.**
- *Against gating*: ~60 minutes is incompatible with any routine per-commit or per-PR gate; this
  is exactly why the task-138 split moved it out of `run-oracle-suite.sh` in the first place, and
  nothing here changes that calculus.
- *Against pure "leave manual forever"*: the whole point of the exhaustive scan is a
  self-consistency safety net (`disagreements == 0` over all 274 formulas, not just the
  known-conclusive subset the gating suite checks). A safety net nobody runs except by memory is
  a safety net that silently stops functioning the moment institutional memory lapses — and nine
  days elapsed between the two runs inspected here, both apparently triggered manually (there is
  no evidence in `oracle/scan-results/` of any automated trigger).
- *Recommended middle ground*: a low-frequency scheduled invocation (e.g. weekly, or on
  merge-to-main, run off-hours/unattended) of exactly `oracle/run-oracle-exhaustive-scan.sh`
  unmodified — no assertion changes, since the hard constraint documented in
  `TESTING_GUIDE.md` section 8.8 ("speed comes only from running less redundant work, never from
  weakening assertions") should not be touched by a scheduling decision. This is an
  infrastructure/CI change (a new scheduled workflow, not a gating-path change), and is out of
  this research task's scope to implement — recorded here as the recommendation with its
  costed rationale (~60 min unattended is affordable weekly; is not affordable per-commit).

### 3. `bimodal.get_theory(config)`: config is uniformly ignored across 3 of 4 theories, not fixed

`bimodal.get_theory(config=None)` (`code/src/model_checker/theory_lib/bimodal/__init__.py:76-97`)
returns a fixed dict regardless of `config`; its own docstring says "config: Optional
configuration (currently unused)". Confirmed live:

```python
theory = get_theory(['extensional'])
# theory["operators"] has 17 entries: \Box \Diamond \Future \Past \Since \Until
# \bot \future \leftrightarrow \neg \next \past \prev \rightarrow \top \vee \wedge
```

**This is not bimodal-specific.** `imposition.get_theory(config=None)` and
`exclusion.get_theory(config=None)` have the byte-identical "config: currently unused" contract
(`imposition/__init__.py:80`, `exclusion/__init__.py:68`). `logos.get_theory(config=None, *,
subtheories=None)` is the sole theory with real restriction, via a separate keyword-only
parameter — and `theory_lib/tests/test_theory_conformance.py::TestGetTheoryContract
::test_get_theory_uses_uniform_config_parameter` codifies this as the intended contract: every
theory must accept a leading positional `config` parameter for signature uniformity, and only
`logos` may have an additional `subtheories` parameter. `config` for the other three theories was
never designed to accept a subtheory list — it is a signature placeholder, not a broken feature.

**Callers relying on a restriction that does not happen**: at least 15 test-fixture files across
`code/src/model_checker/builder/tests/` and `code/tests/` call `bimodal.get_theory([...])`
positionally as if it restricted operators (grep: `get_theory(['extensional'])` /
`get_theory(['counterfactual'])` / `get_theory(['modal'])`), most obviously
`builder/tests/unit/test_example.py`, `builder/tests/integration/test_performance.py`, and
`builder/tests/fixtures/test_data.py`. **This is already self-diagnosed, not newly discovered
here**: `test_performance.py::test_comparison_mode_runs_end_to_end`'s own docstring states "the
two entries are not actually different theories \[...\] the subtheory argument is ignored \[...\]
That is a defect in `get_theory`, not in this test, and is not addressed here", and
`test_example.py::test_build_example_bimodal_theory_countermodel`'s docstring independently notes
the same fact and adds explicit `max_time: 30` padding specifically because the full (unrestricted)
bimodal operator set makes even a trivial extensional example ("A" premise, "B" conclusion) solve
slower than the theory's 1s default — i.e., the exact "nominally trivial extensional example
solves over a world-history x time search space" symptom the task predicted, already paid for
via a widened `max_time` rather than fixed at the source.

**Recommendation: fail loudly, do not implement restriction.** Implementing a real
operator-restriction mechanism for bimodal would require inventing a subtheory decomposition the
theory does not currently have (unlike logos, bimodal's operators are not organized into
independently-selectable groups) — a nontrivial design task disproportionate to what any current
caller actually needs (every caller found either passes `['extensional']` expecting a no-op-sized
fragment, or explicitly documents working around the no-op). Raising on a non-`None` `config`
(e.g. `TypeError` /`NotImplementedError` with a message pointing at the always-full theory and,
if desired, at `logos.get_theory(subtheories=...)` as the theory that actually supports this)
would immediately surface every one of the ~15 confused call sites, matching the task's "fail
loudly" option and avoiding the disproportionate "implement the restriction" option. **This is a
breaking change to ~15 files and should be scoped as its own implementation task** — it is out of
this research task's remit to execute, and doing so here would risk exactly the kind of
undersized, drive-by fix this repository's TDD/no-backwards-compatibility principles argue
against for a change with this much call-site fan-out.

## Decisions

- Treated the two most recent, code-current, `SCAN_COMPLETE`-marker-verified exhaustive-scan runs
  already on disk as the required "quiet machine" evidence for Finding 2, rather than re-running
  under today's measurably non-quiet load (5.5-7.6 load average on 24 cores) — re-running would
  not have produced more trustworthy timing data than the two runs found, and this task's mandate
  to adjudicate only inside `nix develop` is about correctness (avoiding false greens from a bare
  PATH), not about mandating a fresh run when clean, recent, reproducible-methodology evidence
  already exists.
- Did not modify `test_oracle_interface.py` in any way: no skip converted to a failure, no
  timeout widened, no catalog label corrected. All corrections identified above (`TN_TH_2`,
  `TN_CM_1`, `BM_TH_1`) are left as findings for a follow-up implementation task.
- Did not attempt to independently adjudicate `MD_TH_2`'s exclusion-vs-payload mismatch beyond
  noting it, to keep this report's verified claims to what was directly checked.

## Recommendations

Priority order for a follow-up implementation task (not executed here):

1. **Correct `TN_TH_2`'s `expected_sat` label** from `False` to `True` in `EXAMPLE_JSON_CATALOG`
   (`test_oracle_interface.py` around line 250) — ground-truth-confirmed, stable across three
   window sizes. This alone does not fix the skip (the formula still needs >60000ms to decide),
   but it fixes the thing that would otherwise silently hard-fail the day the encoding gets fast
   enough to decide it.
2. **Investigate the primitive `untl`-based expansion's performance for `all_future`-shaped
   formulas** — confirmed SAT with a simple two-atom witness, yet undecided at 180000ms in
   primitive form vs. <2s in enriched form. This is the highest-value single encoding target: it
   is the site-779 skip, and the same `untl`-based mechanism is implicated in `BM_TH_2`'s (Since
   side) and `TN_TH_2`'s continued timeouts.
3. **Re-examine `TN_CM_1`/`BM_TH_1`'s exclusion** — both are `all_future(A)`, both mislabeled
   `False`/UNSAT when ground truth and a live 1.79s probe say `True`/SAT, and both decide fast
   enough now that their `REGRESSION_TIMEOUT_EXAMPLES` membership looks stale. Correcting the
   label and re-testing for removal from the exclusion set are two separate, sequenced steps (fix
   label first, since re-including with the wrong label would just create a new, immediately-hit
   regression failure).
4. **Investigate `BM_TH_2` (`all_past(A)`) vs. its Until-mirror `all_future(A)`** — correctly
   labeled but 60s+ timeout vs. 1.79s for the structurally symmetric future-side formula; an
   encoding asymmetry between the Until (future) and Since (past) sides worth its own look.
5. **Add a scheduled (not gating) periodic exhaustive-scan run** — e.g. weekly or
   merge-to-main, off-hours, running `oracle/run-oracle-exhaustive-scan.sh` unmodified. ~60
   minutes unattended is affordable at that cadence; it is not affordable per-commit, and no
   assertion should be weakened to make it so.
6. **Make `bimodal.get_theory` (and, for consistency, `imposition`/`exclusion`) fail loudly on a
   non-`None` `config`**, then fix the ~15 call sites currently passing a silently-ignored
   subtheory-shaped list. Scope as its own task given the call-site fan-out; do not fold into a
   task whose primary subject is oracle timeout visibility.
7. **Follow up on `MD_TH_2`'s exclusion-reason/payload mismatch** — its `EXAMPLE_JSON_CATALOG`
   JSON is a bare atom (trivially fast by construction) but its `REGRESSION_TIMEOUT_EXAMPLES`
   comment says "timeout-prone"; not independently verified here, flagged for the same follow-up
   pass as items 1 and 3.

## Risks & Mitigations

- **Risk**: correcting `TN_TH_2`/`TN_CM_1`/`BM_TH_1` labels without also addressing the
  performance gap would move formulas from "silently wrong label, invisible" to "correctly
  labeled, loudly skipped" — a net visibility improvement but not a green run. **Mitigation**:
  sequence label fixes before any attempt to re-include timeout-excluded examples, exactly as
  Recommendation 3 above specifies.
- **Risk**: a scheduled exhaustive-scan job could bit-rot silently (e.g. a broken cron/CI
  schedule producing no output nobody reviews) — the same failure mode this task exists to fix
  for the skip sites. **Mitigation**: whatever schedules it should also alert on absence of a
  fresh `SCAN_COMPLETE` marker within the expected cadence window, not just run-and-forget.
- **Risk**: making `get_theory` fail loudly is a breaking change touching ~15 files; a partial
  rollout (some call sites fixed, others not) would produce confusing intermittent failures.
  **Mitigation**: Recommendation 6 explicitly scopes "raise + fix all call sites" as one atomic
  task, not a staged rollout.

## Appendix

- Live skip-site run: `nix develop --command bash -c 'export PYTHONPATH="oracle:$PYTHONPATH"; pytest oracle/bimodal_logic/tests/test_oracle_interface.py -v -rs -k "TestOracleExampleRegressionViaAPI or TestEnrichedRoundTrip"'` — 948.28s, 74 passed / 2 skipped / 32 deselected.
- Ground-truth CLI: `python -m bimodal_logic.ground_truth '<formula-json>' --window {4,5,6,8}`.
- Prior exhaustive-scan evidence: `oracle/scan-results/20260807T155847Z/{report.json,SCAN_COMPLETE}`,
  `oracle/scan-results/20260810T022056Z/{report.json,SCAN_COMPLETE}`,
  `oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`.
- `get_theory` caller inventory: `rg "get_theory\("` across `code/` (15+ non-test-helper call
  sites passing a positional list to `bimodal.get_theory`).
