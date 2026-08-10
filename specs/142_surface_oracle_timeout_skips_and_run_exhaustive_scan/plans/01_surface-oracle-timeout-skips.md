# Implementation Plan: Surface Oracle Timeout Skips and Record Scan Cadence

- **Task**: 142 - Surface the two timeout-conditional pytest.skip sites, adjudicate wrong expected_sat labels, record exhaustive-scan cadence, address get_theory(config)
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/reports/01_oracle-timeout-skips-scan.md
- **Artifacts**: plans/01_surface-oracle-timeout-skips.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/no-task-references-in-deliverables.md
  - code/docs/core/TESTING_GUIDE.md (sections 8.6, 8.8)
- **Type**: python
- **Lean Intent**: false

## Overview

Two categories of oracle verification currently produce no actionable signal in the gating suite:
timeout-conditional `pytest.skip()` outcomes that are invisible because `run-oracle-suite.sh` never
passes `-rs`, and three `EXAMPLE_JSON_CATALOG` entries whose recorded `expected_sat` the research
proved wrong against the module's own ground-truth evaluator. This plan corrects the three wrong
labels, adds a reporting-only timeout-skip inventory that classifies every timeout skip as KNOWN /
NEW / RESOLVED and prints it loudly in both gating passes, records the exhaustive-scan cadence
decision with a staleness checker, and documents the `get_theory(config)` no-op contract without
changing its behavior. Definition of done: the gating suite still passes with the same green/red
verdict it has today, every timeout skip is named and annotated in the runner output, and the four
larger encoding/CI/API changes the research identified are recorded as scoped follow-ups rather
than started here.

### Research Integration

The research report is the sole evidence base and every one of its verified findings is honored:

- `TN_TH_2`'s `expected_sat=False` is wrong (ground truth SAT, stable across windows 4/5/6; manual
  semantics unambiguous: `A` false everywhere makes `all_future(some_past(A))` false). Corrected in
  Phase 2.
- `TN_CM_1` and `BM_TH_1` are the same defect on the identical formula `all_future(A)` (ground truth
  SAT, live probe 1.79s SAT, catalog says `False`). Labels corrected in Phase 2; their
  `REGRESSION_TIMEOUT_EXAMPLES` membership is deliberately **not** touched, per the research's
  explicit sequencing instruction (fix label first; re-inclusion is a separate step).
- The site-779 `all_future` skip is a genuine, correctly-labeled performance gap in the primitive
  `untl`-based expansion, not a labeling problem. It stays a skip; only its visibility changes.
- The exhaustive scan was adjudicated from two code-current, `SCAN_COMPLETE`-marker-verified prior
  runs (`disagreements: 0` both, ~59-61 min). Recommendation "scheduled periodic, never gating"
  plus the research's own stated mitigation (alert on absence of a fresh marker) is implemented as
  documentation + a freshness checker in Phase 5.
- `get_theory(config)` ignoring `config` is a uniform 3-theory signature-placeholder contract
  codified by `test_theory_conformance.py`, not a bimodal bug, and the fail-loudly fix touches ~15
  call sites. Phase 6 documents the contract; the breaking change is a scoped follow-up.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` in the delegation context).

## Goals & Non-Goals

**Goals**:
- Make both timeout-conditional skip sites (`test_oracle_interface.py:635`, `:779`) visible in every
  gating run, with a per-formula annotation stating what is known about each and what to do next.
- Detect and loudly report drift in both directions: a NEW timeout skip nobody has adjudicated, and
  a RESOLVED entry that used to skip and now decides (the signal that a label or an exclusion is
  ready to be revisited).
- Correct the three ground-truth-contradicted `expected_sat` labels (`TN_TH_2`, `TN_CM_1`,
  `BM_TH_1`) and guard them with a test so the corrections cannot silently regress.
- Record the exhaustive-scan cadence decision (scheduled, off-hours, never gating) in
  `TESTING_GUIDE.md` section 8.8, and ship the staleness check the research required as its
  mitigation.
- Document the `get_theory(config)` no-op contract at all three affected theories so the ~15
  confused call sites have something authoritative to read, without breaking any of them.
- Leave the repository green: the gating suite's pass/fail verdict must be unchanged by this work.

**Non-Goals**:
- Converting any `pytest.skip()` into a failure. No strict/fail-on-new-skip mode is added, not even
  opt-in — the classification banner is the actionability mechanism.
- Widening any solve budget (`30000`, `180000`, `TEMPORAL_SOLVE_TIMEOUT_MS`,
  `SELF_SCAN_SOLVE_TIMEOUT_MS`, `ORACLE_PASS1_TIMEOUT`, `ORACLE_PASS2_TIMEOUT`) or lowering any
  conclusiveness floor.
- Changing `REGRESSION_TIMEOUT_EXAMPLES` membership (adding or removing entries).
- Making `get_theory` raise, or implementing real operator restriction for bimodal.
- Improving the primitive `untl`/`snce` encoding performance.
- Running a fresh exhaustive scan, or adding a scheduled CI workflow.
- Touching the 7 other `except OracleTimeoutError:` sites (silent `continue` at lines 1181/1205/1233,
  silent `return` at 826/930, and the by-design sites at 1140/1485).

### Scope Boundary: This Task vs. Spawned Follow-Ups

The research's next-action list has five separable pieces plus two smaller flags. Explicit split:

| Research item | Disposition | Rationale |
|---|---|---|
| Correct `TN_TH_2` label | **This task** (Phase 2) | Single-line data fix, ground-truth-confirmed, guarded by a new test |
| Correct `TN_CM_1`/`BM_TH_1` labels | **This task** (Phase 2) | Same defect, same file, same evidence; label-only, no exclusion-set change |
| Surface the two named skip sites | **This task** (Phases 3-4) | The task's primary subject |
| Record exhaustive-scan cadence | **This task** (Phase 5) | "Decide/record" is documentation + the required staleness mitigation |
| Investigate primitive `untl` expansion perf (site-779 root cause) | **Follow-up** | Encoding/solver research; unbounded scope; the research names it the highest-value single encoding target but does not scope it |
| Re-include `TN_CM_1`/`BM_TH_1` after label fix | **Follow-up** | Research explicitly sequences this *after* the label fix as a separate step; requires fresh multi-run timing evidence on an idle machine |
| `BM_TH_2` (`all_past`) vs `all_future` encoding asymmetry | **Follow-up** | Same encoding-research class as the item above |
| Scheduled CI exhaustive-scan workflow | **Follow-up** | Runner-capacity and cadence-owner decisions the research costed but did not resolve; ~60 min job on shared CI needs its own evaluation |
| `get_theory` fail-loudly + fix ~15 call sites | **Follow-up** (Phase 6 documents only) | Research: breaking change across 3 theories and ~15 files, "should be scoped as its own implementation task, not folded into this one" |
| Surface the 7 other `OracleTimeoutError` sites | **Follow-up** | Research: "worth a dedicated follow-up (not this task)"; the silent-`continue` sites are strictly worse than the two named ones and deserve their own design |
| `MD_TH_2` exclusion-reason/payload mismatch | **Follow-up** | Not independently verified by the research; needs its own adjudication pass |

Phase 7 records these as concrete follow-up recommendations in the implementation summary and the
orchestrator handoff. No follow-up task is created by this plan's execution.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Correcting `TN_TH_2` moves it from "silently wrong label" to "correctly labeled, still loudly skipped" — a visibility win but not a new green | L | H | Expected and intended; the research predicted exactly this. Phase 2 verifies the outcome is still SKIPPED, never FAILED, and Phase 7 states it plainly in the summary |
| The RESOLVED classification misfires under the two-pass runner (a known skip belonging to pass 1 looks "resolved" in pass 2's session) | H | H | Derive the session's collected set from the reports actually seen in this session, not from a static list; only classify RESOLVED for node ids that ran in *this* session. Specified in Phase 3 and unit-tested |
| The conftest hook behaves differently under `-n 6` (pass 1) than serial (pass 2) | M | M | Collect from `pytest_runtest_logreport` in the controller, which receives worker reports identically under xdist and serial. Phase 4 verifies both passes empirically |
| Skip-reason substring matching silently stops matching if a skip message is reworded | M | L | Match on the stable shared substring `did not decide within`, present in both skip messages; add a unit test asserting both real messages match, so a reword breaks the test rather than the report |
| A conftest change perturbs collection or exit status for the whole `oracle/` tree | H | L | Hooks are report/summary-only, add no markers, and never touch `session.exitstatus`. Phase 4 compares full-suite exit status against a Phase 1 baseline |
| Verification wall clock is inflated by a loaded machine, misread as a regression | M | M | Record machine load alongside every timing; compare verdicts (pass/fail, skip/no-skip), never wall clock, when judging correctness. Never widen a budget to clear a contended run |
| Editing deliverable files adds ephemeral task-number citations | L | M | New comments/docs cite durable anchors (file + section names) only, per `.claude/rules/no-task-references-in-deliverables.md`. Applies to all edits outside `specs/**` |
| Doc edits to `TESTING_GUIDE.md` weaken the section 8.8 hard constraint | H | L | Cadence text is additive; the "speed comes only from running less redundant work, never from weakening assertions" paragraph is left byte-identical |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 5, 6 | -- |
| 2 | 2, 4 | 1, 3 |
| 3 | 7 | 2, 4, 5, 6 |

Phases within the same wave can execute in parallel. Wave 2's phase 2 depends on 1; wave 2's
phase 4 depends on 3. Territory is disjoint within each wave: phase 1/2 own
`test_oracle_interface.py`, phase 3/4 own `oracle/conftest.py` + `oracle/run-oracle-suite.sh`,
phase 5 owns `oracle/check-scan-freshness.sh` + `TESTING_GUIDE.md` section 8.8, phase 6 owns the
three theory `__init__.py` files.

**Environment constraint (all phases)**: every verification command runs inside the devShell —
`nix develop --command bash -c '...'`. A bare-PATH python risks a false green from a missing
`pytest-xdist`/`pytest-timeout` or an interpreter mismatch.

---

### Phase 1: Baseline capture and adjudication guard test (RED) [COMPLETED]

- **Goal:** Independently re-confirm the research's ground-truth verdicts, capture a pre-change
  behavioral baseline, and write the failing test that will pin the corrected labels.
- **Tasks:**
  - [x] Re-confirm the three adjudications with the module's own evaluator, unfolding each enriched
        formula first via `bimodal_logic.translation.unfold_formula` (`ground_truth` supports only
        the 5 primitive temporal tags):
        `nix develop --command bash -c 'export PYTHONPATH="oracle:$PYTHONPATH"; python -c "..."'`
        driving `bimodal_logic.ground_truth.ground_truth_verdict` for `all_future(some_past(A))`
        (`TN_TH_2`) and `all_future(A)` (`TN_CM_1`, `BM_TH_1`) at windows 4, 5, and 6. Expect `SAT`
        at every window for all three. **If any verdict disagrees with the research, stop and record
        the discrepancy rather than proceeding to Phase 2.**
  - [x] Capture a baseline of current behavior into `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/baselines/`:
        the targeted run `pytest oracle/bimodal_logic/tests/test_oracle_interface.py -rs -k
        "TestOracleExampleRegressionViaAPI or TestEnrichedRoundTrip"` (expect 74 passed / 2 skipped /
        32 deselected, ~950s under moderate load), saving stdout plus `uptime` output before and
        after so the run's machine load is on record.
  - [x] Add `TestCatalogLabelAdjudication` to `test_oracle_interface.py` with a test asserting the
        adjudicated `expected_sat` for the three entries directly against `EXAMPLE_JSON_CATALOG`
        (including the two that live in `REGRESSION_TIMEOUT_EXAMPLES` and therefore never run as
        regression cases — the catalog is still wrong data today, and this test is what makes it
        visible). Docstring records the provenance: ground-truth evaluator verdict, window stability,
        and the manual-semantics argument, citing `bimodal_logic/ground_truth.py` by name (never a
        task number).
  - [x] Confirm the new test FAILS for all three entries (RED), naming each mismatch explicitly.
- **Timing:** ~1 hour (dominated by the baseline run; the ground-truth probes take seconds)
- **Depends on:** none
- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` — new `TestCatalogLabelAdjudication` class
  - `specs/142_.../baselines/` — new baseline capture (task-scoped, per project convention)
- **Verification:**
  - Ground-truth verdicts are `SAT` for all three formulas at windows 4, 5, 6.
  - New test fails with three distinct assertion messages; no other test's outcome changes.

---

### Phase 2: Apply the three label corrections (GREEN) [COMPLETED]

- **Goal:** Correct the ground-truth-contradicted `expected_sat` values and confirm the corrections
  neither break the suite nor change any skip into a failure.
- **Tasks:**
  - [x] `EXAMPLE_JSON_CATALOG["TN_TH_2"]`: `False` -> `True`; rewrite the inline comment from
        "`\Future \past A` -- UNSAT (valid in these frames)" to state SAT with the witness
        (`A` false at every time makes `some_past(A)` false at every time), and note the verdict is
        ground-truth-derived, not solver-derived (the solver still does not decide it at 60000ms).
  - [x] `EXAMPLE_JSON_CATALOG["TN_CM_1"]`: `False` -> `True`, comment updated the same way for
        `all_future(A)`.
  - [x] `EXAMPLE_JSON_CATALOG["BM_TH_1"]`: `False` -> `True`, comment updated; note it is the same
        formula as `TN_CM_1`.
  - [x] Leave `REGRESSION_TIMEOUT_EXAMPLES` byte-identical. Re-inclusion of `TN_CM_1`/`BM_TH_1` is a
        separate, sequenced follow-up (see Scope Boundary).
  - [x] Confirm `test_active_example_count`'s invariants (`total == 52`,
        `active == total - excluded`) still hold — labels changed, membership did not.
  - [x] Run the targeted regression case and confirm `TN_TH_2` still reports SKIPPED (budget
        outcome), never FAILED:
        `pytest 'oracle/bimodal_logic/tests/test_oracle_interface.py::TestOracleExampleRegressionViaAPI::test_oracle_regression[TN_TH_2]' -rs`
- **Timing:** ~45 minutes
- **Depends on:** 1
- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` — three catalog tuples and their comments
- **Verification:**
  - `TestCatalogLabelAdjudication` passes (GREEN).
  - `TestOracleExampleRegressionViaAPI::test_active_example_count` passes.
  - `TN_TH_2` outcome is `SKIPPED`, with the existing "did not decide within 30000 ms" reason.
  - `git diff` touches only the three tuples, their comments, and nothing in
    `REGRESSION_TIMEOUT_EXAMPLES`.

---

### Phase 3: Timeout-skip inventory hook in oracle/conftest.py [COMPLETED]

- **Goal:** Collect every timeout-caused skip during a pytest session and classify it, with no
  effect on any test's outcome or the session exit status.
- **Tasks:**
  - [x] Add a `_TIMEOUT_SKIP_SIGNATURE = "did not decide within"` constant — the stable substring
        shared by both skip messages (site 635: `'{name}': did not decide within {timeout} ms`;
        site 779: `'{name}': at least one side did not decide within {timeout} ms`).
  - [x] Add `_KNOWN_TIMEOUT_SKIPS`: a mapping from node-id fragment to a short adjudication note,
        seeded with exactly the two confirmed entries — `test_oracle_regression[TN_TH_2]`
        ("label corrected to SAT from the ground-truth evaluator; the solver still does not decide
        it at 2x budget") and `test_enriched_vs_primitive_sat_agreement[all_future]` ("primitive
        untl-based expansion does not decide; the enriched form decides in under 2s — a performance
        gap, not a disagreement"). Notes cite file/section anchors, never task numbers.
  - [x] Implement `pytest_runtest_logreport(report)`: record every report's node id into a
        session-scoped *seen* set, and when `report.skipped` and the extracted reason contains the
        signature, record the node id into a *timeout-skipped* set with its reason. Extract the
        reason from `report.longrepr` (a `(path, lineno, "Skipped: <reason>")` tuple for an
        in-body `pytest.skip()`), falling back to `str(report.longrepr)`. Deriving the seen set from
        reports — rather than from a collection hook — makes the behavior identical under `-n 6`
        (controller receives worker reports) and serial, which is required because the gating runner
        uses both.
  - [x] Implement `pytest_terminal_summary(terminalreporter)`: print a clearly delimited
        `== ORACLE TIMEOUT-SKIP INVENTORY ==` section listing, one line each:
        `[KNOWN]` (skipped and in `_KNOWN_TIMEOUT_SKIPS`, with its note),
        `[NEW]` (skipped, unrecognized — the loud drift signal, with explicit "adjudicate this
        formula's expected_sat against bimodal_logic/ground_truth.py before assuming the label is
        right" guidance), and
        `[RESOLVED]` (in `_KNOWN_TIMEOUT_SKIPS`, present in this session's seen set, and *not*
        skipped — the formula now decides; go re-check its label and its exclusion-set membership).
        A known entry absent from the seen set is not this session's business and is omitted
        entirely — this is what keeps the two-pass runner from reporting pass 1's skips as
        "resolved" during pass 2.
  - [x] Print a footer stating the standing constraints: never widen a solve budget to clear an
        entry, and see `code/docs/core/TESTING_GUIDE.md` sections 8.6 and 8.8.
  - [x] Opt-in machine-readable artifact: when `ORACLE_SKIP_REPORT` names a path, also write the
        inventory as JSON (`{known: [...], new: [...], resolved: [...]}`), mirroring the existing
        `ORACLE_JUNIT_DIR` opt-in idiom. Unset (the default) changes nothing.
  - [x] Never mutate `session.exitstatus` and never add a marker or a failure. Print the section
        even when empty (a single "no timeout skips in this session" line) so silence is never
        ambiguous.
  - [x] Add `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py` covering: both real skip
        messages match the signature; a non-timeout skip reason does not; KNOWN/NEW/RESOLVED
        classification including the "known but not in this session's seen set is omitted" case; and
        the JSON artifact shape when `ORACLE_SKIP_REPORT` is set.
- **Timing:** ~1.5 hours
- **Depends on:** none
- **Files to modify:**
  - `oracle/conftest.py` — new constants and three hooks (existing
    `pytest_configure`/`pytest_collection_modifyitems` behavior unchanged)
  - `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py` — new unit tests
- **Verification:**
  - New unit tests pass.
  - `pytest 'oracle/bimodal_logic/tests/test_oracle_interface.py::TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement' -rs`
    prints the inventory with `[KNOWN] ...[all_future]` and no `[NEW]`/`[RESOLVED]` lines.
  - A deliberately narrow selection that collects neither known entry prints the empty-inventory
    line and no spurious `[RESOLVED]`.

---

### Phase 4: Wire skip surfacing into the gating runner [COMPLETED]

- **Goal:** Make the inventory and pytest's own skip reasons appear in every gating invocation, in
  both passes, without changing the runner's pass/fail semantics.
- **Tasks:**
  - [x] Add `-rs` to both pytest invocations in `oracle/run-oracle-suite.sh`, placed before `"$@"`
        so a caller can still override. This is the missing primitive: today the gating suite never
        prints a skip reason at all.
  - [x] Add an `ORACLE_SKIP_REPORT_DIR` opt-in that sets `ORACLE_SKIP_REPORT` per pass to
        `skip-report-pass1.json` / `skip-report-pass2.json` — one file per pass so pass 2 cannot
        clobber pass 1, exactly matching the existing `ORACLE_JUNIT_DIR` treatment. Unset by default.
  - [x] Extend the script's trailing summary block with a short pointer stating that each pass
        printed its own timeout-skip inventory, that `[NEW]` and `[RESOLVED]` lines are the
        actionable ones, and that a skip is a budget outcome that is never cleared by widening a
        budget.
  - [x] Update the script's header comment to describe the surfacing behavior, citing
        `oracle/conftest.py` and `code/docs/core/TESTING_GUIDE.md` section 8.8 as anchors — no task
        numbers in new content.
  - [x] Leave `pass1_timeout`/`pass2_timeout` defaults, both `-m` expressions, `-n 6`, and the
        `_classify`/exit-code logic untouched.
- **Timing:** ~45 minutes
- **Depends on:** 3
- **Files to modify:**
  - `oracle/run-oracle-suite.sh` — `-rs` on both passes, `ORACLE_SKIP_REPORT_DIR` opt-in, summary
    text, header comment
- **Verification:**
  - `nix develop --command bash -c 'ORACLE_SKIP_REPORT_DIR=$(mktemp -d) bash oracle/run-oracle-suite.sh'`
    completes; both passes print an inventory section; both JSON files exist and parse.
  - The parallel pass (`-n 6`) and the serial pass produce structurally identical inventory sections
    — the xdist-vs-serial equivalence Phase 3 was designed for.
  - Script exit status matches the Phase 1 baseline verdict; no pass is newly `FAILED` or
    `TIMED OUT`.

---

### Phase 5: Record the exhaustive-scan cadence decision and ship the staleness check [COMPLETED]

- **Goal:** Turn the research's cadence recommendation into a recorded decision plus the freshness
  alerting it named as the mandatory mitigation, without adding the scan to any gating path.
- **Tasks:**
  - [x] Add a subsection to `code/docs/core/TESTING_GUIDE.md` section 8.8 recording the decision:
        the exhaustive scan stays **out of the gating path** (~60 min is incompatible with
        per-commit gating) and is run on a **low-frequency schedule, off-hours, unattended**
        (weekly or merge-to-main), invoking `oracle/run-oracle-exhaustive-scan.sh` **unmodified**.
        State the evidence: two independent code-current runs, 3651.243s and 3555.065s wall clock,
        `disagreements: 0` both times, conclusive 103 and 105 of 274 — and that the 2-formula
        conclusive-count swing is the documented near-budget-headroom contention sensitivity, not a
        regression, since `disagreements == 0` is the property that matters.
  - [x] Record the standing constraint explicitly: a cadence decision never licenses an assertion
        change, and the section's existing "speed comes only from running less redundant work,
        never from weakening assertions" paragraph is left byte-identical.
  - [x] Record the mitigation the research required: a scheduled scan that bit-rots silently is the
        same failure mode this work exists to fix, so absence of a fresh `SCAN_COMPLETE` marker must
        itself be alertable.
  - [x] Add `oracle/check-scan-freshness.sh`: scans `oracle/scan-results/*/SCAN_COMPLETE`, reports
        the newest run's timestamp, its age in days, and its `report.json` `disagreements` /
        `conclusive` / `wall_clock_seconds`; exits non-zero when the newest marker is older than a
        cadence window (default 7 days, overridable via `ORACLE_SCAN_MAX_AGE_DAYS`) or when no
        marker exists at all. Marker existence — never PID or process liveness — is the only
        completion signal, matching the contract in section 8.8.
  - [x] Point `oracle/run-oracle-exhaustive-scan.sh`'s summary block at the freshness checker so an
        operator learns of it at the natural moment. Do not otherwise modify that script.
  - [x] Note in the docs that wiring the schedule into CI is deliberately not done here — it needs
        its own runner-capacity evaluation (recorded as a follow-up in Phase 7).
- **Timing:** ~1 hour
- **Depends on:** none
- **Files to modify:**
  - `code/docs/core/TESTING_GUIDE.md` — additive subsection under 8.8
  - `oracle/check-scan-freshness.sh` — new script (executable)
  - `oracle/run-oracle-exhaustive-scan.sh` — one added summary pointer line
- **Verification:**
  - `nix develop --command bash oracle/check-scan-freshness.sh` reports the newest on-disk run
    (`20260810T022056Z`) with its real metrics.
  - `ORACLE_SCAN_MAX_AGE_DAYS=0` forces the stale path and exits non-zero with a clear message.
  - A run against an empty/absent `scan-results` directory exits non-zero rather than reporting a
    false fresh state.
  - `git diff code/docs/core/TESTING_GUIDE.md` shows only additions; the hard-constraint paragraph
    is unchanged.

---

### Phase 6: Document the get_theory(config) no-op contract [COMPLETED]

- **Goal:** Make the silently-ignored `config` argument self-documenting at all three affected
  theories, with zero behavior change and zero call-site breakage.
- **Tasks:**
  - [x] Expand the `get_theory` docstring in
        `code/src/model_checker/theory_lib/bimodal/__init__.py` from "Optional configuration
        (currently unused)" to state the actual contract: `config` is a **signature-uniformity
        placeholder** required by the `TestGetTheoryContract` conformance test, it is accepted and
        ignored, passing a subtheory-shaped list has **no effect** (the full operator set is always
        returned), and `logos.get_theory(subtheories=...)` is the only theory offering real
        restriction. Note that bimodal returns all operators including the modal and temporal ones,
        so a nominally "extensional" example still solves over the full world-history-by-time search
        space — the reason some callers pad `max_time`.
  - [x] Apply the equivalent docstring clarification to `imposition/__init__.py` and
        `exclusion/__init__.py`, which carry the byte-identical contract.
  - [x] Change no signature, no return value, and no runtime behavior. Do not add a raise, a warning,
        or a deprecation.
  - [x] Cite durable anchors only (`theory_lib/tests/test_theory_conformance.py`,
        `logos.get_theory`) — no task numbers, per the deliverables rule.
- **Timing:** ~30 minutes
- **Depends on:** none
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/__init__.py`
  - `code/src/model_checker/theory_lib/imposition/__init__.py`
  - `code/src/model_checker/theory_lib/exclusion/__init__.py`
- **Verification:**
  - `nix develop --command bash -c 'PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_theory_conformance.py -v'`
    passes, including `TestGetTheoryContract::test_get_theory_uses_uniform_config_parameter`.
  - `PYTHONPATH=code/src python -c "from model_checker.theory_lib import bimodal;
    print(len(bimodal.get_theory(['extensional'])['operators']))"` still prints `17` — behavior
    provably unchanged.
  - `git diff` on the three files shows docstring lines only.

---

### Phase 7: Full-suite verification, documentation, and follow-up recording [COMPLETED]

- **Goal:** Prove the combined change leaves the gating verdict unchanged, document the new
  surfacing behavior where operators will find it, and record the scoped follow-ups.
- **Tasks:**
  - [x] Run the full gating suite inside the devShell with the skip report enabled:
        `nix develop --command bash -c 'ORACLE_SKIP_REPORT_DIR=... bash oracle/run-oracle-suite.sh'`,
        recording `uptime` before and after. Compare the verdict (not the wall clock) against the
        Phase 1 baseline.
  - [x] Confirm the inventory names exactly the two known entries as `[KNOWN]`, with no `[NEW]` and
        no `[RESOLVED]` lines. Any `[NEW]` line is a real finding to record, not a defect in the
        tooling — investigate and document it before declaring the phase done.
  - [x] Add a short subsection to `code/docs/core/TESTING_GUIDE.md` (adjacent to 8.6/8.8) describing
        the timeout-skip inventory: what `[KNOWN]`/`[NEW]`/`[RESOLVED]` mean, that skips are budget
        outcomes and are never cleared by widening a budget, and where the adjudication notes live
        (`oracle/conftest.py`).
  - [x] Write `specs/142_.../summaries/01_surface-oracle-timeout-skips-summary.md` covering: the
        three corrected labels with their ground-truth provenance; the surfacing mechanism; the
        cadence decision and the freshness checker; the `get_theory` documentation-only outcome; and
        the explicit statement that `TN_TH_2` remains skipped (correctly labeled now, still
        undecided at 2x budget) — a visibility improvement, not a new green.
  - [x] Record the seven follow-up recommendations from the Scope Boundary table in the summary and
        in the orchestrator handoff's `next_action_hint`, each with a one-line rationale, in the
        research's priority order.
  - [x] Confirm no deliverable file outside `specs/**` gained a task-number citation:
        `git diff` review against `.claude/rules/no-task-references-in-deliverables.md`.
- **Timing:** ~1.5 hours (the gating suite alone is ~18 minutes measured on an idle machine)
- **Depends on:** 2, 4, 5, 6
- **Files to modify:**
  - `code/docs/core/TESTING_GUIDE.md` — timeout-skip inventory subsection
  - `specs/142_.../summaries/01_surface-oracle-timeout-skips-summary.md` — new
  - `specs/142_.../.orchestrator-handoff.json` — final handoff
- **Verification:**
  - Gating suite verdict matches the Phase 1 baseline (no newly failing or timed-out pass).
  - Inventory output contains exactly two `[KNOWN]` lines across the two passes.
  - Both skip-report JSON files parse and agree with the printed sections.
  - Summary and handoff exist and enumerate the follow-ups.

---

## Testing & Validation

- [x] Ground-truth verdicts for `all_future(some_past(A))` and `all_future(A)` are `SAT` at windows
      4, 5, and 6 (Phase 1) — the evidence the label corrections rest on.
- [x] `TestCatalogLabelAdjudication` fails before Phase 2 and passes after (RED -> GREEN).
- [x] `TestOracleExampleRegressionViaAPI::test_active_example_count` passes; `total == 52` and
      `active == total - excluded` are unchanged.
- [x] `TN_TH_2` reports `SKIPPED`, never `FAILED`, after the label correction.
- [x] `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py` passes, including the
      known-but-not-collected-in-this-session omission case.
- [x] Both real skip messages match the timeout signature; a non-timeout skip reason does not.
- [x] `oracle/run-oracle-suite.sh` prints an inventory section in both the `-n 6` pass and the serial
      pass, with structurally identical formatting.
- [x] Full gating suite verdict is unchanged from the Phase 1 baseline.
- [x] `oracle/check-scan-freshness.sh` reports the newest on-disk `SCAN_COMPLETE` correctly, and
      exits non-zero for both the stale and the no-marker cases.
- [x] `test_theory_conformance.py` passes; `bimodal.get_theory(['extensional'])` still returns 17
      operators.
- [x] No solve budget, pass budget, exclusion-set membership, conclusiveness floor, or assertion was
      weakened anywhere in the diff.
- [x] No task-number citation appears in any changed file outside `specs/**`.

## Artifacts & Outputs

- `oracle/bimodal_logic/tests/test_oracle_interface.py` — three corrected catalog labels plus
  `TestCatalogLabelAdjudication`
- `oracle/conftest.py` — timeout-skip inventory collection, classification, terminal summary, and
  opt-in JSON artifact
- `oracle/bimodal_logic/tests/test_timeout_skip_inventory.py` — new unit tests for the hook
- `oracle/run-oracle-suite.sh` — `-rs` on both passes, `ORACLE_SKIP_REPORT_DIR` opt-in, summary text
- `oracle/check-scan-freshness.sh` — new `SCAN_COMPLETE` staleness checker
- `oracle/run-oracle-exhaustive-scan.sh` — summary pointer to the freshness checker
- `code/docs/core/TESTING_GUIDE.md` — exhaustive-scan cadence decision and timeout-skip inventory
  subsections
- `code/src/model_checker/theory_lib/{bimodal,imposition,exclusion}/__init__.py` — `get_theory`
  contract docstrings
- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/baselines/` — pre-change baseline
  capture with machine-load context
- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/summaries/01_surface-oracle-timeout-skips-summary.md`
- `specs/142_surface_oracle_timeout_skips_and_run_exhaustive_scan/.orchestrator-handoff.json`

## Rollback/Contingency

- Every phase is an independent, revertible commit; nothing here is a data migration or a schema
  change, so `git revert` of any single phase restores prior behavior exactly.
- **Phase 2 contingency**: if the Phase 1 ground-truth re-confirmation disagrees with the research
  for any of the three entries, stop before editing the catalog, record the discrepancy, and leave
  that entry's label untouched. A label change is only justified by a reproduced verdict.
- **Phase 3/4 contingency**: if the conftest hooks perturb collection, exit status, or xdist
  behavior in any way, revert those two phases alone. The label corrections (Phases 1-2), the
  cadence work (Phase 5), and the docstrings (Phase 6) are independent and stand on their own.
- **Phase 4 fallback**: if the inventory proves unreliable under `-n 6`, keep the `-rs` flag —
  pytest's native skip-reason reporting alone already delivers a large share of the visibility goal —
  and revert only the conftest hook.
- **Never roll back by widening a budget or weakening an assertion.** If a verification run is red
  because the machine is loaded, re-run when idle; a contended run is not evidence of a regression
  and is never grounds for changing a timeout.
