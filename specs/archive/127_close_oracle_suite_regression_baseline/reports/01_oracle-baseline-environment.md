# Research: Closing the Oracle Suite Regression Baseline

## Summary

Every blocker named in the task description is resolvable in this sandbox today. `pytest-xdist`
is already built and importable via the project's own `flake.nix` devShell — no network install
needed, and network to PyPI is in fact reachable right now anyway. The full 550-test oracle suite
requires a sibling checkout (`bimodal_harness`) that already exists on disk at the path
`flake.nix` expects. The existing partial baseline artifact is not a dead end: it already covers
~97% of the suite (535/550 outcomes) including its two `F`s, both of which decode to
already-documented, independently-root-caused CPU-contention flakes from a prior task's oracle
disposition work — not new regressions. The one live risk is real and was observed directly
during this research: another session's pytest process was running concurrently in this same
sandbox while these checks were performed, reproducing the exact contention mechanism blamed for
the original kill.

## 1. Is pytest-xdist actually unavailable?

Not for this project's own environment. Two separate facts:

- **The generic system Python cannot get it via pip right now**: `/home/benjamin/.nix-profile/bin/python3`
  (3.13.13, the interactive shell default) has no `xdist` module, and `pip install --dry-run
  pytest-xdist` fails immediately with `ERROR: Can not perform a '--user' install. User
  site-packages are not visible in this virtualenv.` — a sandboxing artifact of this Python, not
  a network problem.
- **The project's own dev environment already has it, pre-built**: `flake.nix:71-72` declares
  `pytest` and `pytest-xdist` as members of `devPython` (the package set for `devShells.default`),
  and `flake.nix:113` already uses `-n 6` for the in-package bimodal suite's Nix check. The
  resulting derivation is already realized in the Nix store —
  `/nix/store/kykgmi6vxjzw76miazjf3yfn59kp7phd-python3-3.12.13-env` — and
  `.../bin/python3 -c "import xdist; print(xdist.__version__)"` succeeds, printing `3.8.0`.
- **The "package index unreachable" premise is also stale as of right now**: `curl -sI
  https://pypi.org/simple/pytest-xdist/` returns `HTTP/2 200` from this sandbox. Whatever was
  unreachable during the original attempt is not unreachable now (transient network state, not a
  structural sandbox restriction) — but this doesn't matter for the fix, since the Nix-provided
  interpreter needs no install at all.

**Conclusion**: run the oracle suite through the Nix-provided interpreter (either `nix develop
--command pytest ...` or directly via the store path found above) rather than fighting the bare
system Python's `pip --user` restriction.

## 2. Wall-clock cost, and can it be chunked?

- **The sibling checkout is required for collection to succeed at all**: `oracle/bimodal_logic/tests/test_oracle_interface.py:37-38`
  imports `from bimodal_harness.oracle.protocol import OracleProvider` (and `.registry`), and
  `flake.nix`'s `shellHook` documents this as `bimodalHarnessSrc = "../BimodalHarness/src"`, an
  "optional sibling checkout used only by the oracle differential suite... The dev shell surfaces
  it on PYTHONPATH when present." It is present: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness`
  exists on disk. Running `pytest --collect-only` on the oracle suite with only `code/src` on
  `PYTHONPATH` (no `bimodal_harness`) collects 550 anyway (collection doesn't touch that import
  path at module level for most files), but a live *run* of `test_oracle_interface.py` fails to
  even import without it. The correct invocation is:
  `PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src` — or simply enter `nix develop`,
  whose `shellHook` sets this automatically since the directory exists.
- **Live-benchmarked serial rate**: I ran `oracle/bimodal_logic/tests/test_oracle_interface.py -m
  "not slow"` (58 tests) to completion under the Nix devPython interpreter, serially: **4m44s**,
  all green (0 failures) — about **4.9s/test** average for this file. Extrapolating to the full
  550-test suite (which also includes the heavier Z3-differential-scan tests in
  `test_cross_oracle_differential.py`) lands in the same 45-90 minute range the task description
  already cites; this benchmark neither contradicts nor tightens that estimate, it corroborates
  the order of magnitude.
- **`-n 6` does help, but sublinearly**: a 9-test slice (`TestCIGate` + `TestKnownFormulaBaseline`
  classes from the differential file) took 87.85s wall-clock under `-n 6` (`3m24s` of *user* time
  spread over 6 workers). These are single-threaded Z3-solve-bound tests, so expect roughly a
  4-6x real speedup rather than 6x — i.e., a full `-n 6` run should land around **15-25 minutes**
  wall-clock, well under the serial estimate and short enough to not need chunking/resuming.
  `--junitxml=` combines fine with `-n 6`; xdist merges shard results into one XML.
- **Chunking is available as a fallback but shouldn't be needed**: `pytest --lf` (rerun only the
  two known-flaky tests below in isolation, per the Category C precedent) plus `-k` splitting by
  test class both work if `-n 6` still proves impractical, but given the 15-25 minute estimate,
  a single `-n 6` invocation is the simpler and recommended path.

## 3. The existing partial baseline is not empty — decode it before rerunning

`specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt` (committed at
`b40179c9`, "record partial oracle suite run and close out baseline pinning") already contains
535 of the ~550 dot/x/F outcome characters — the run that was killed got through roughly 97% of
the suite, not merely "about 91%" as the commit message estimated (91% was the last *percentage
marker* pytest printed; more output followed before the kill).

I mapped the two `F` positions in that partial output against a fresh `--collect-only -q` listing
(ordering is deterministic — no `pytest-randomly`/`-order` plugin is installed or configured
anywhere in the repo, confirmed via grep) to identify exactly which tests failed:

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent`
- `oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary`

Both of these are named, by exact test-id, in
`specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/oracle-suite-disposition.md`
under **"Category C (resolved as contention flakes, NOT genuine, NOT xfailed): 7 tests"** — e.g.
`test_all_sat_task_relation_ternary (60.9s contended -> PASSED isolated; this test itself allows
up to 60000ms timeout for depth>0 formulas, so even its own generous budget was exceeded only
under contention)`. This is the same finding the phase-2 commit message speculated about
("consistent with the documented CPU-contention flake category from a prior task's oracle
disposition work") — this research confirms it by exact test-id match, not just category
resemblance. The 9 `x` marks visible in the partial output are a mix of the suite's other
(non-pinned) xfails plus some of the 5 pinned strict-xfail differentials; none XPASSed.

**Practical implication**: a clean full rerun should pass all 550 with zero failures if it avoids
concurrent-session contention (see risk below). If the same two tests flake again under `-n 6`
or serial contention, that is the known Category C signature, not a new regression — rerun just
those two in isolation to confirm before treating it as a blocker.

## 4. Pinned facts verified clean

- **Collection count**: `PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src pytest
  oracle/bimodal_logic/tests/ --collect-only -q` → `550 tests collected` — exact match to
  `verify-refactor.sh`'s `BASELINE_ORACLE_COUNT=550` and `baselines/collection-counts.txt`.
- **xfail(strict=True) locations**: `grep -n 'xfail(' oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  → lines `767 942 1020 1133 1431` — exact match to `verify-refactor.sh`'s `XFAIL_LINES` array
  and the plan's line 151 risk-table entry.

Both are already independently verified per the Phase 2 commit message ("verified clean via three
separate `--skip-oracle` verify-refactor.sh runs across phases 7-9"); this research reproduces
the same result from scratch as a second, independent confirmation.

## 5. `code/scripts/verify-refactor.sh` — what Step 6 and `--skip-oracle` do

Read in full (183 lines). Structure:

- **Step 1-2**: collection-count floor checks for the in-package bimodal suite (`>=289`) and full
  in-package suite (`>=2100`) — unrelated to the oracle blocker.
- **Step 3**: oracle collection count must equal exactly `550` (not just `>=`) — already green.
- **Step 4**: runs the in-package bimodal suite with one retry allowed for a documented flake —
  unrelated to the oracle blocker.
- **Step 5**: static check that the 5 `xfail(strict=True)` lines in
  `test_cross_oracle_differential.py` are unchanged — already green, no suite execution needed.
- **Step 6**: `if [ "$SKIP_ORACLE" = true ]` → prints "SKIPPED"; else runs
  `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -q
  >/tmp/verify-refactor-oracle.txt 2>&1` and fails the whole script (increments `FAILURES`) if
  that pytest invocation is non-zero. **This is the actual regression gate for the oracle suite**;
  everything else in the script is inference from static/collection-only signals.
- **Step 7**: `compare_bimodal_baseline.sh` against the task-097 archived baseline — unrelated to
  the oracle blocker.
- Script `set`s `-uo pipefail` (not `-e`), accumulates a `FAILURES` counter, and exits 1 if
  nonzero at the end.

**Two things to note for the implementer**:

1. `--skip-oracle`'s Step 6 branch uses the bare system `python -m pytest` (no `bimodal_harness`
   on `PYTHONPATH`, no Nix interpreter reference) — so running it *without* `--skip-oracle` as-is,
   from a plain shell, will hit the same `ModuleNotFoundError: No module named 'bimodal_harness'`
   this research hit initially, unless invoked from inside `nix develop` (which sets `PYTHONPATH`
   to include the sibling checkout via its `shellHook`) or with `PYTHONPATH` set explicitly before
   invoking the script.
2. **The script does not emit `--junitxml`** for either the bimodal or oracle suite — it only
   redirects to `/tmp/verify-refactor-*.txt`. The existing `baselines/junit-bimodal.xml` was
   therefore produced by a *separate*, ad hoc `pytest --junitxml=...` invocation outside this
   script (confirmed: no `junitxml` string appears anywhere in `verify-refactor.sh` or
   `compare_bimodal_baseline.sh`; `junit-bimodal.xml`'s git history shows no accompanying script
   change). The same pattern applies to `baselines/junit-oracle.xml`: it needs its own explicit
   `pytest oracle/bimodal_logic/tests/ --junitxml=.../junit-oracle.xml` run (ideally the *same*
   invocation that also redirects `-q` text output to `oracle-run.txt`, e.g. via `tee`), separate
   from (but consistent with) the final `verify-refactor.sh` (no `--skip-oracle`) run the task
   description also requires.

## 6. Refactor plan Phase 2 heading location

`specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md`:

- Line 4 (top status line): `- **Status**: [PARTIAL] (25/26 phases COMPLETED; Phase 2 is PARTIAL
  -- the full serial 550-test ...` — spans lines 4-8, describing the contention-kill and the
  fact that all other Phase 2 evidence is clean.
- Line 216 (section heading): `### Phase 2: Pin Verification Baselines and Build the Regression
  Gate [PARTIAL]`
- Two body references also carry the `[PARTIAL]` framing and will read stale once the full run
  lands: line 1575 ("A full serial oracle run remains the Phase 2 PARTIAL gap") and line 1695
  ("... the full 550-test serial run per Phase 2's PARTIAL status ...") and line 1712 ("Phase 2
  PARTIAL gap, unchanged by this phase").

All four locations need the `[PARTIAL]` → `[COMPLETED]` flip (heading + status line), and the
three body cross-references should be updated to reflect the gap being closed (not merely deleted
— per `.claude/rules/no-task-references-in-deliverables.md`, no task-number citation is needed;
a plain "closed" framing referencing the baseline artifacts by filename is sufficient and durable).

## 7. Where the baseline artifacts belong

Task 127's own `state.json` entry (`file_scope`) already answers this explicitly:
`specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/` — **not** a new
`specs/127_.../baselines/` directory. This matches CLAUDE.md's "baselines, recorded per task (not
a shared top-level directory)" wording read narrowly (baselines belong to the *task whose plan
they gate*, i.e. task 126's refactor plan, even though task 127 is the one closing the gap) and
matches the fact that the placeholder `oracle-run.txt` already lives there, alongside
`bimodal-run.txt`, `junit-bimodal.xml`, and `collection-counts.txt`. `junit-oracle.xml` does not
yet exist in that directory and must be created there (see Step 6 note above — it needs its own
`--junitxml=` invocation, the script alone won't produce it).

## 8. Live risk observed directly during this research

While benchmarking (a serial run of one oracle test file), a **second, independent pytest
process from a different session** was observed actively running concurrently in this same
sandbox (`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion/tests/unit/...
code/src/model_checker/theory_lib/bimodal/tests/unit/...`, PID 569220). This is not a
hypothetical risk — it is the exact resource-contention mechanism the Phase 2 commit blamed for
the original kill, reproduced live during this very research pass. **Recommendation for the
implementer**: before starting the full-suite run (serial or `-n 6`), confirm no other test-heavy
session is active in this sandbox (`ps aux | grep pytest`), and prefer the `-n 6` path specifically
*because* its shorter (~15-25 min vs ~45-90 min) wall-clock window reduces the exposure window to
a collision with another concurrent session, not just because it's faster in isolation.

## Recommended path for implementation

1. Confirm no other pytest/z3-heavy process is running (`ps aux | grep pytest`).
2. From the Nix devPython interpreter (`nix develop --command ...`, or the discovered store path
   directly), run once with both a text tee and junit output:
   `PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src pytest
   oracle/bimodal_logic/tests/ -n 6 -q --junitxml=specs/126_.../baselines/junit-oracle.xml
   | tee specs/126_.../baselines/oracle-run.txt`
3. If either of the two Category-C-flake tests fails, rerun just those two in isolation
   (`-p no:xdist` or `-n0`) to confirm the isolated-pass precedent still holds before treating it
   as a genuine regression.
4. Flip Phase 2's heading (line 216) and status line (line 4) from `[PARTIAL]` to `[COMPLETED]`
   in the refactor plan; update the three stale body cross-references (lines 1575, 1695, 1712).
5. Re-run `bash code/scripts/verify-refactor.sh` **without** `--skip-oracle` (with `PYTHONPATH`
   including the `bimodal_harness` sibling checkout, or from inside `nix develop`) to get a full,
   independent green confirmation of Step 6, then commit the two baseline artifacts plus the plan
   edits together.
