# Research: unstable-watch classifier laundering-guard fix

## Scope

This report grounds the four required fixes in the current state of the three in-scope files
and answers the two "choose with reasons recorded" design questions the task poses. It does
**not** re-derive the root cause (verified in the task description) or re-open any closed lead
(`xdist_serial`, `MIN_CONCLUSIVE_GATING_FORMULAS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS` values,
the collection-crash fix from the archived `unstable_watch_workflow_failures` task).

Files read: `.github/scripts/unstable_watch_classify.py` (321 lines, current),
`code/tests/ci/test_unstable_watch_classifier.py` (324 lines, current, 16 tests all pass),
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (`_assert_scan_report` at line
748, `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment block at lines ~97-217,
`TestGatingConclusiveScan` at line ~2387), `.github/workflows/unstable-watch.yml`,
`code/docs/core/TESTING_GUIDE.md` section 8.9, and prior task 160's plan
(`specs/160_verify_bimodal_oracle_budget_and_watch_unstable_marker/plans/01_unstable-marker-and-watch-classifier.md`)
for the design history of the module this task extends.

## 1. Empirical confirmation of the root cause (against the *current* code, not a hypothesis)

Reproduced independently, without touching the real oracle module: wrote a throwaway two-
assertion fixture matching `_assert_scan_report`'s exact shape (a passing
`disagreements == 0` assert whose f-string source contains `"Self-comparison produced "`,
followed by a failing floor assert), ran it under real pytest with
`-o junit_logging=system-out --junitxml=out.xml`, then fed the resulting JUnit XML through the
*actual* `parse_junit` + `classify` from `.github/scripts/unstable_watch_classify.py`:

```
has floor sig:              True
has disagreements=0:        True
has disagreement guard sig: True   # <-- false positive: matches the SOURCE LISTING, not a real disagreement
classify:                    NEW   # <-- should be TIMING
```

The `<failure>` element's text pytest emits for a failure at the *second* of two sequential
asserts includes the full function body up to and including the failing line — which means the
*first* (passing) assert's literal f-string source, `f"Self-comparison produced
{report['disagreements']} disagreements among "`, is present verbatim in the traceback. This
confirms the task description's root cause against the current classifier, not just in the
abstract.

Confirmed the proposed minimal regex discriminates correctly:

```python
>>> re.search(r"Self-comparison produced \d+ disagreements", source_line)
None      # source has "{report['disagreements']}", never a literal digit
>>> re.search(r"Self-comparison produced \d+ disagreements", rendered_line)
<Match>   # a real rendered failure has "3 disagreements", etc.
```

## 2. Remedy choice for the laundering guard: (a), not (b) — reasons recorded

**Recommendation: (a) MINIMAL** — replace the `DISAGREEMENT_SIGNATURE in failure_text` bare
substring check with an anchored regex requiring a digit between "produced" and "disagreements":
`re.search(r"Self-comparison produced \d+ disagreements", failure_text)`.

Reasons, weighed against (b) DURABLE (emit a machine-readable `UNSTABLE-SIGNATURE: ...` line and
stop parsing prose):

- **Blast radius.** `_assert_scan_report` (`oracle/bimodal_logic/tests/test_cross_oracle_differential.py:748`)
  is a shared helper called from many places beyond the gating test: `TestFullScanReport`
  (~line 2043, 2060), `TestGatingConclusiveScanMechanism` (~line 2506 — asserts
  `pytest.raises(AssertionError, match="disagreements")` directly against its output text),
  `TestBimodalHarnessIntegration`-adjacent tests (~line 2109), and the standalone
  `test_self_agreement_report_has_zero_disagreements`/`test_...` group (~line 1977-2111) that
  pins its exact message shape. Changing what `_assert_scan_report` prints/asserts (remedy b)
  touches every one of these call sites' assumptions about message text; changing only the
  classifier's own regex (remedy a) touches nothing outside
  `.github/scripts/unstable_watch_classify.py`.
- **Verified sufficiency.** The one and only place a source-listing echo currently produces a
  false positive is the `DISAGREEMENT_SIGNATURE` negative guard (see the survey in §3 below —
  neither `has_zero_disagreements` nor `FAILURE_SIGNATURE` shares this exposure against the
  *current* two functions). A narrow fix that closes the one live hole is proportionate; (b)
  solves a bug class that, right now, has exactly one instance.
- **Project convention.** This module's own docstring and TESTING_GUIDE.md 8.9 already commit to
  "stdlib only" and a specific additive pattern (`GATING_FLOOR_NODEID_FRAGMENT`/
  `GATING_FLOOR_SIGNATURE` style constants) for new signatures; `re` is stdlib, explicitly
  pre-approved by the task's hard constraints ("`re` is stdlib and fine").
- **Cost.** (a) is a one-line change plus a docstring update; (b) requires a new print-format
  contract in `_assert_scan_report`, its own dedicated tests, and revalidating every existing
  test that already exercises that function's message text.

**Record this decision at the `DISAGREEMENT_SIGNATURE` definition site** (currently
`unstable_watch_classify.py:60-62`) and in the module's `classify()` docstring
(currently lines 116-137), replacing the "negative guard" prose to describe matching the
*rendered* count rather than the source, and note (b) as a considered-and-declined alternative
with a one-sentence pointer to this report so a future investigator does not re-litigate the
choice from scratch. Do not delete the existing reasoning about *why* the guard exists (a
`disagreements != 0` failure must never launder into TIMING) — only how it discriminates.

**`has_zero_disagreements` — must move with the chosen remedy, per the task's explicit
instruction, even though it is not exposed to the identical defect.** Surveyed independently:
`_assert_scan_report`'s `print()` f-string source is `f"disagreements={report['disagreements']} "`
— the literal substring `"disagreements=0"` never appears in the *source listing* because the
value is interpolated, not written literally (confirmed: `grep -c "disagreements=0"` against the
real JUnit XML from §1's repro hits exactly once, inside `<system-out>`, never inside
`<failure>`). So this check does **not** reproduce the source-echo bug today. It is still a bare,
unanchored substring match sharing the general brittleness class (nothing pins it to the "scan
report:" line specifically). Recommend tightening it alongside the (a) fix for consistency
within the same function — e.g. `re.search(r"scan report:.*disagreements=0", failure_text)` —
rather than leaving one check as a regex and the sibling check as a bare substring test with no
stated rationale for the asymmetry.

**`FAILURE_SIGNATURE` (`"Test failed for example:"`, BM_CM_1 branch) — surveyed, found safe,
record why rather than leaving it merely assumed.** Its source is
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:125`:
`assert result, f"Test failed for example: {example_name}"` — a *single* assertion, the *last*
statement in `test_example_cases`. Verified empirically (a two-line fixture: an early exception
in a helper, followed by an unreached assert) that pytest's traceback for a failure raised
*before* reaching a later line does **not** include that later line's source — pytest shows each
frame's source only up to the point of failure, not the whole function body. Two consequences:
(1) there is no earlier, textually-preceding *sibling* assertion whose source could leak this
string into an unrelated failure (unlike `_assert_scan_report`'s two-assert shape), and (2) if
`run_test(...)` raises before the assert, the signature correctly fails to appear, so the branch
conservatively falls through toward `NEW` rather than falsely confirming TIMING. `FAILURE_SIGNATURE`
is a *positive* confirmation signature, not a *negative* guard against a co-located different
failure mode, which is the structural distinction that makes `DISAGREEMENT_SIGNATURE` dangerous
and this one not. Record this finding as a comment near `FAILURE_SIGNATURE`'s definition
(`unstable_watch_classify.py:51`) so the survey the task requested is preserved, not just
performed once and forgotten.

## 3. The real-pytest regression test (non-negotiable half)

Verified the approach works end-to-end (§1): `subprocess.run([sys.executable, "-m", "pytest",
str(fixture_path), "-o", "junit_logging=system-out", f"--junitxml={xml_path}"], ...)` against a
small fixture file reproducing `_assert_scan_report`'s exact two-assertion shape produces a real
JUnit XML whose `<failure>` text contains the source-listing echo, and driving it through the
real `parse_junit` + `classify` reproduces the documented false positive (`NEW` instead of
`TIMING`) against the current guard.

Design recommendations for `code/tests/ci/test_unstable_watch_classifier.py`:

- **Fixture content**: a small, self-contained module — do NOT import the real
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` or `bimodal_logic` package into
  this fixture. That would drag a Z3 dependency and the full oracle harness into
  `code/tests/ci`, which is meant to run in the lighter general-tests job. Instead, copy the
  exact literal assertion text from `_assert_scan_report` into the fixture — following the
  existing convention this file already uses for `FLOOR_ASSERTION_MESSAGE`/`DISAGREEMENT_MESSAGE`
  ("Exact strings, copied verbatim from source rather than retyped").
- **Invocation**: `subprocess.run([sys.executable, "-m", "pytest", ...])`, not a bare `pytest`
  string — portable across the nix sandbox and CI without relying on `pytest` being first on
  `PATH`.
- **Assertions**: drive `classify_mod.parse_junit(xml_path)` then
  `classify_mod.classify(GATING_NODEID_or_a_realistic_stand-in, duration, failure_text)` and
  assert the result is `TIMING` after the fix. Before the fix, this new test must fail with the
  literal `NEW` (documented RED state, already reproduced in §1) — write it so it fails for that
  specific reason, not by construction error.
- **Also cover the disagreement case through the same real-pytest path**: a second fixture
  variant where the *first* assert (disagreements) is the one that fails should still classify
  `NEW` — this is the "genuine soundness bug must never launder" case, and running it through
  real pytest (rather than only the existing synthetic `DISAGREEMENT_MESSAGE` test) closes the
  same coverage gap for the positive-guard direction, not just the false-positive direction.
- **Do not remove the 16 existing synthetic tests** — the task is explicit these remain valid
  characterization, just not sufficient alone.
- **Runtime cost**: the subprocess pytest invocation measured ~0.3-0.5s locally; acceptable for a
  unit test in this suite.

## 4. Per-test promotion streak (item 3) — recommend fixing, not just documenting

Confirmed the defect as described: `run()` (lines 191-309) sets `any_failure = True` globally
across **both** trees' testcases combined (line 217, inside the shared loop over
`(code_junit_path, oracle_junit_path)`), and `compute_promotion_streak` (lines 161-188) computes
one streak from that single boolean plus job-level historical conclusions — there is no
per-nodeid dimension anywhere in the pipeline. Since the oracle gating test fails deterministically
(96/103 every run, per the five-run incident record), `any_failure` is true essentially every
night, so the *global* streak can never reach 20 regardless of how clean BM_CM_1 becomes — this
was flagged as a known, deliberately-deferred limitation in task 160's plan ("Building a true
per-test promotion streak (would require downloading prior runs' `unstable-watch-record.jsonl`
artifacts). Out of scope; the residual limitation is documented instead.") and is now the
concrete blocker the task description describes.

The per-run artifact (`unstable-watch-record-${run_id}`, uploaded unconditionally via
`actions/upload-artifact@v4` in the workflow's last step) already carries exactly what's needed:
each JSONL line has `nodeid` and `classification`. What task 160 deferred as requiring artifact
downloads is now buildable:

**Recommended design**: for each of the currently-marked node ids
(`sorted(set(MAX_TIME_BY_NODEID_FRAGMENT.keys()) | {GATING_FLOOR_NODEID_FRAGMENT})` — already
computed at line 275-277), download and parse the last ~25 completed runs'
`unstable-watch-record-<id>` artifacts (via `gh run download <id> -n
unstable-watch-record-<id> -D <tmp>`, or `gh api .../actions/artifacts` + zip download — both use
the already-present `gh` CLI, no new third-party dependency), extract that specific nodeid's
`classification` from each, and compute a **per-nodeid** streak with the same honesty rule
`compute_promotion_streak` already implements (any failure — TIMING or NEW — for *that* nodeid
zeroes *that* nodeid's streak). `READY TO PROMOTE` should then name only the nodeid(s) that
individually reached 20, not the whole `currently_unstable` set at once (this also fixes a related
inaccuracy: today's notice already names every marked test even when only one earned it, per the
task description's parenthetical in item 3).

**Scope-bounding to keep this tractable**: only the current, small membership set (2 node ids
today) needs history, not an unbounded set of past node ids — this keeps the added artifact-download
volume to `O(2 x 25)` per nightly run, not unbounded.

**Trade-offs to weigh in planning**: this adds `gh run download`/`gh api` network calls and JSONL
parsing per marked test per run (a real but bounded cost — the workflow already tolerates `gh`
CLI dependency and network flakiness via its existing try/except around `gh run list`), and a
larger diff than remedy (a) above. If the planner judges this cost disproportionate for this
task's phase budget, the task's own fallback ("or record explicitly why it stays per-run") is
legitimate — but if taken, the "Promotion-streak limitation" paragraph in TESTING_GUIDE.md 8.9
(current text, ~lines 970-978) needs a substantive rewrite: it currently frames the limitation as
a *historical-component-only* residual ("cannot be retroactively corrected... out of scope for
the mechanism as it stands"), which reads as a minor caveat. It must instead say plainly that the
*global* per-run design couples every marked test's promotion path to every other marked test's
failures, that this is now actively blocking BM_CM_1 (not hypothetical), and give the same
reasoning recorded here for accepting that coupling rather than fixing it. Given the concrete,
present impact, this report's recommendation leans toward attempting the fix; the final call
belongs to planning given the cost trade-off above.

## 5. `xdist_serial` lead: closed twice over, record at `GATING_RECHECK_SOLVE_TIMEOUT_MS` (item 4)

Confirmed against `.github/workflows/unstable-watch.yml`: the "Install test dependencies" step
installs `z3-solver networkx pytest pytest-timeout typing-extensions` — no `pytest-xdist` — and
the oracle-tree pytest invocation (`PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m
unstable -v -o junit_logging=system-out --junitxml=/tmp/watch-oracle.xml`) carries no `-n` flag
at all. This is single-process execution with zero sibling pytest workers of any kind — a
strictly *stronger* isolation than `@pytest.mark.xdist_serial` provides (that marker only
isolates marked tests from *each other*; it does not prevent *other*, unmarked tests from running
concurrently in sibling `-n` workers on the same runner, which is the "shared/virtualized-neighbor
contention" the existing comment block's hypothesis (1) still calls "live"). Five consecutive
nightly runs (33091941820, 33193518591, 33250263772, 33306220265, 33386925098) under this true
single-process condition reproduced the identical 96/103 conclusive, 7-timeout shortfall.

The existing comment block's item (3) already closes the `xdist_serial`-vs-`differential-tests.yml`
angle ("this class has carried `@pytest.mark.xdist_serial` since 2026-08-06 ... pytest-xdist
sibling-worker contention was never live for either recorded shortfall run"), but that closure was
scoped to `differential-tests.yml`'s invocation specifically, and its own hypothesis (1) still
calls the *general* shared-host contention question "still-live... which no marker change can
test." unstable-watch.yml's five identical runs are new evidence bearing directly on that still-
live line: even under the *strongest possible* isolation (true single-process, no xdist installed
at all, zero sibling workers of any kind on the runner), the shortfall persists unchanged.
Recommend appending a new dated note to the `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment block
(after item (3), or as a new item (3b)) recording: the five unstable-watch run IDs/dates, the
byte-identical 96/103/7-timeout result under zero-contention single-process execution, and that
this retires the "sibling-worker contention" sub-hypothesis specifically (leaving pure
runner-hardware capacity, per hypothesis (1)'s original framing, as the sole remaining
explanation — nothing here reopens or resolves that broader hardware question). Also record the
duration drift as a one-sentence observation, not an action: 761.61s (08-27) -> 898.78s (08-30) ->
808.64s (08-31), against the job's `timeout-minutes: 20` (1200s) — real headroom today (worst
case ~75% of budget), but worth a sentence for the next investigator, not a change to any budget
or timeout value per the hard constraints.

## 6. `code/docs/core/TESTING_GUIDE.md` — targeted updates, not a rewrite

Section 8.9 ("The `unstable` Marker") is the only relevant section. Current state read in full
(lines 902-1000). Two specific updates, both narrowly scoped:

- **"Promotion-streak limitation" paragraph** (current text starts "`unstable-watch.yml`'s
  step-summary streak counter's historical component..."): update to match whichever of §4's two
  outcomes planning selects — either describe the new per-test mechanism (if built), or rewrite
  the limitation as active/blocking rather than theoretical (if the fallback is taken), per §4's
  detail above.
- **New one- or two-sentence caution near the existing "classifier lives in an importable module,
  not YAML" paragraph** (current text ends "...following the pattern the
  `GATING_FLOOR_NODEID_FRAGMENT`/`GATING_FLOOR_SIGNATURE` constants establish, plus tests"):
  record the general, reusable lesson this incident surfaced for whoever adds a *third* `unstable`
  marking — a negative/guard signature must match the *rendered* failure text (a regex anchored to
  a concrete rendered shape, or a `<system-out>`-only structured line), never a bare substring
  that could also appear verbatim in the assertion's own source listing when a JUnit `<failure>`
  echoes a function body containing more than one assertion. This is the generalizable takeaway
  from §1-§2 above and belongs in the guide, not only in the code comment, since it is exactly the
  kind of "gap between synthetic fixture and real pytest output" this incident's own root cause
  documents as unlikely to be caught by more synthetic tests alone.

No other subsection of TESTING_GUIDE.md needs touching for this task (8.6, 8.8, 8.10, 8.11 are
all unrelated to the laundering guard, the streak, or the xdist finding).

## Summary of recommendations for planning

1. Laundering guard: remedy (a), anchored regex on `DISAGREEMENT_SIGNATURE`'s match, with
   `has_zero_disagreements` tightened alongside it for consistency (not because it shares the
   exact defect); `FAILURE_SIGNATURE` left unchanged but with its safety survey recorded as a
   comment.
2. New regression test: real-pytest-subprocess-driven, self-contained fixture (no oracle/Z3
   import), covering both the floor-only-failure-is-TIMING and the
   disagreements-failure-is-still-NEW directions through the real JUnit path; keep all 16
   existing synthetic tests.
3. Per-test promotion streak: recommend attempting the fix (bounded to the current 2-member
   marked set, via `gh run download`/`gh api` artifact parsing already available through the
   existing `gh` CLI dependency); accept the task's documented-fallback escape hatch only if
   planning judges the cost disproportionate, in which case TESTING_GUIDE.md's limitation
   paragraph needs a substantive (not cosmetic) rewrite to reflect the now-active impact.
4. Record the unstable-watch.yml zero-contention-confirms-shortfall finding at
   `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s comment block (new dated item), plus a one-sentence
   duration-drift observation; no budget/timeout value changes.
5. TESTING_GUIDE.md: two targeted edits to section 8.9 only (promotion-streak paragraph,
   plus a new caution sentence near the classifier-module paragraph); no other section changes.

All four items are additive/corrective within the existing file_scope; none require touching
`MIN_CONCLUSIVE_GATING_FORMULAS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`'s value, the `unstable`
marker itself, or the workflow's non-gating trigger/branch-protection contract.
