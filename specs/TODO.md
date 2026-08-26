---
next_project_number: 171
---

# TODO

## Task Order

*Updated 2026-08-26. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 152,161,167,170 | -- | testing, semantics, release-engineering |
| 2 | 153,158 | 152,161 | semantics, release-engineering |
| 3 | 154,168 | 153,158 | semantics, release-engineering |

**Grouped by Topic** (indented = depends on parent):

### Testing

167 [IMPLEMENTING] — Fix flaky TestMixedFormulas failures in oracle/bimodal_logic/test
170 [NOT STARTED] — Two open CI-budget questions left deliberately unresolved when th

### Semantics

152 [NOT STARTED] — AUDIT ONLY -- no semantics change, no constraint change, no examp
  └─ 153 [NOT STARTED] — Bring `BimodalSemantics`'s frame class up to the JPL paper's `def
    └─ 154 [NOT STARTED] — THE PAYOFF, and the one task in this group where OVER-CLAIMING is

### Release Engineering

161 [BLOCKED] — Make TestPyPI publishing succeed at all: fix the TestPyPI trusted
  └─ 158 [NOT STARTED] — Harden the release CI pipeline so TestPyPI becomes a real verific
    └─ 168 [NOT STARTED] — Build a systematic PyPI install and full-CLI verification CI pipe

## Tasks

### 170. Resolve xdist worker count and differential oracle floor
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None

**Description**: Two open CI-budget questions left deliberately unresolved when the max_time floor and the specs/** paths-ignore landed. (A) XDIST WORKER COUNT: .github/workflows/tests.yml and flake.nix both run the parallel gating pass at -n 6 on a 4-vCPU ubuntu-latest runner -- six workers over four cores, which is what pushed contention-sensitive Z3 solves past budget. -n 4 would match the runner, but it is NOT obviously safe: reducing worker count changes which examples run concurrently and therefore the ambient load each solve sees, so it must be verified that no example flips outcome (in particular that no countermodel-expected example stops finding one) rather than assumed monotone. The -n 6 value is load-bearing and documented -- it was chosen over xdist's auto mode because auto reproduced a bimodal contention flake -- so any change must preserve that reasoning and stay textually in sync across both files (code/tests/ci/test_workflow_parity.py enforces the sync). Measure, do not assume. (B) DIFFERENTIAL ORACLE FLOOR: oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent has failed on all six runs the workflow has ever had, always with the same shortfall (96 of 103 formulas conclusive against MIN_CONCLUSIVE_GATING_FORMULAS=100, 0 disagreements). The GATING_RECHECK_SOLVE_TIMEOUT_MS widening from 20000 to 40000ms on 2026-08-12 did NOT move the number -- 96/103 with 7 timeouts both before and after, with step wall clock rising 744s to 1103s -- so the seven timing-out formulas are not merely near-budget and doubling again is unlikely to help. That constant's own comment block records the widening as never CI-verified and names marking the test `unstable` as the documented fallback. Identify the seven formulas, determine whether their cost is a genuine property of the population or a regression, and decide between a measurement-backed remedy and the unstable route under section 8.9's four entry criteria. The floor itself must NOT be lowered -- that is the assertion-weakening the existing comment block explicitly forbids. (C) RESIDUAL TIGHT BUDGETS OUTSIDE LOGOS: an AST survey found 20 example settings dicts still at max_time 2 and 2 at max_time 3 in theory_lib/bimodal, exclusion, and imposition. These are the same latent hazard the logos floor corrected but have not been observed failing, and bimodal's budgets were deliberately calibrated per-example (see the BM_CM_1/BM_CM_4 recalibration record). Decide whether to extend code/tests/ci/test_example_budget_floor.py's _COVERED list to them, backed by measurement rather than by pattern-matching the logos change. (D) PYTHON 3.12 XDIST WORKER CRASH -- the one CI failure the max_time floor did NOT resolve, and a different mechanism entirely from a solve-budget overrun. On run 32910478240 (commit 653d5bef, the first run carrying the 10s floor), Python 3.10, 3.11, and nix flake check all went green -- zero constitutive failures, where all four jobs had previously failed on CL_TH_12/CL_TH_13 -- but Python 3.12 failed with '[gw2] node down: Not properly terminated', 'replacing crashed worker gw2', on theory_lib/bimodal/tests/unit/test_frame_class_mapping.py::TestFrameClassDeclarationConsistency::test_three_taskframe_axioms_present_in_frame_constraints. A worker dying mid-test is a segfault or OOM in the Z3 native layer, not a timeout: no max_time or max_rlimit value affects it, and the test named in the failure is whichever one the worker happened to be running, not necessarily the cause. Python 3.12 has prior form here -- run 32897405646's 3.12 job reached 94% progress, produced zero output for 17 minutes, and was killed by the job-level timeout-minutes: 20 backstop with orphaned pytest workers in the cleanup log, which is the same shape (worker wedged or dead rather than slow) and is what motivated the --timeout-method=thread guard. Determine whether this is a Z3/Python 3.12 ABI issue, a memory ceiling on the 16GB runner under six workers, or a genuine bimodal bug; note that it may interact with item (A), since fewer workers means more memory headroom per worker.

---

### 168. Pypi install and full cli verification ci
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: Task 158

**Description**: Build a systematic PyPI install and full-CLI verification CI pipeline: parameterize the pytest packaging suite's installed_venv fixture over install source (locally built wheel, TestPyPI, or PyPI), add a TestPyPI pre-publish gate and a post-publish PyPI confirmation matrix to release.yml, and add a dispatchable plus scheduled pypi-smoke.yml workflow with opt-in tmate SSH debugging so the published package can be verified end-to-end from a NixOS development host

---

### 167. Flaky testmixedformulas failures
- **Status**: [IMPLEMENTING]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [167_flaky_testmixedformulas_failures/reports/01_flaky-testmixedformulas-root-cause.md]
- **Plan**: [167_flaky_testmixedformulas_failures/plans/01_deterministic-mixed-formula-budgets.md]

**Description**: Fix flaky TestMixedFormulas failures in oracle/bimodal_logic/tests/test_oracle_interface.py - test_mixed_or_diamond_prev and test_mixed_and_all_future_neg both fail in some pytest runs and pass in others (test_mixed_and_all_future_neg was observed failing in one full-file run and passing in the next with no code change), so determine whether the nondeterminism comes from Z3 solver behavior, test ordering/state leakage, or a genuine semantics defect, then make the outcomes deterministic

---

### 161. Fix testpypi trusted publisher
- **Status**: [BLOCKED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: None
- **Research**: [161_fix_testpypi_trusted_publisher/reports/01_fix-testpypi-trusted-publisher.md]
- **Plan**: [161_fix_testpypi_trusted_publisher/plans/01_fix-testpypi-trusted-publisher.md]
- **Summary**: [161_fix_testpypi_trusted_publisher/summaries/01_fix-testpypi-trusted-publisher-summary.md]

**Description**: Make TestPyPI publishing succeed at all: fix the TestPyPI trusted-publisher registration and make future OIDC mismatches diagnosable in one glance. SCOPE IS DELIBERATELY NARROW -- this is the unblock prerequisite carved out of the larger release-CI hardening task (`harden_release_ci_testpypi_gate`), which now declares this task as a dependency. Everything about PROMOTING TestPyPI to a gate (dropping `continue-on-error`, adding a `verify-testpypi` install-and-smoke-test job, preflight assertions, human confirmation gates) belongs to that task and MUST NOT be done here.

SYMPTOM, AND WHY IT IS STILL OPEN. The "Publish to TestPyPI" job in `.github/workflows/release.yml` fails at the OIDC token exchange with:

    invalid-publisher: valid token, but no corresponding publisher
    (Publisher with matching claims was not found)

This first appeared on the v1.3.0 tag push and RECURRED UNCHANGED on the v1.3.1 tag push -- i.e. the registration was never fixed in between. It has not blocked a release only because the job currently carries `continue-on-error: true`; that tolerance is exactly what the dependent task will remove, so this must be fixed first.

CLAIMS PRESENTED BY THE v1.3.1 RUN (the diff target -- whatever is registered on test.pypi.org must match these exactly):

    sub                : repo:benbrastmckie/ModelChecker:environment:testpypi
    repository         : benbrastmckie/ModelChecker
    repository_owner   : benbrastmckie
    repository_owner_id: 64314593
    workflow_ref       : benbrastmckie/ModelChecker/.github/workflows/release.yml@refs/tags/v1.3.1
    job_workflow_ref   : benbrastmckie/ModelChecker/.github/workflows/release.yml@refs/tags/v1.3.1
    ref                : refs/tags/v1.3.1
    environment        : testpypi

(1) USER-ONLY: REGISTER OR CORRECT THE TRUSTED PUBLISHER ON test.pypi.org. PyPI and TestPyPI are entirely separate registries with separate trusted-publisher configs and separate accounts; a publisher registered on pypi.org does nothing for test.pypi.org. No agent can perform this -- it is web-UI work. Surface it as an explicit user gate and do not attempt to work around it.

  Go to test.pypi.org -> the `model-checker` project -> Publishing (or, if the project does not yet exist there, "Add a pending publisher"), and confirm all four fields:
      Owner            : benbrastmckie
      Repository       : ModelChecker
      Workflow name    : release.yml       (the filename, not the workflow's display name)
      Environment name : testpypi          (must match the job's `environment:` exactly; NOT `pypi`)

  The three failure modes to check for, in likelihood order: (a) the publisher was registered on pypi.org rather than test.pypi.org; (b) the Environment field is `pypi`, or blank, rather than `testpypi`; (c) the Workflow field holds a display name ("Release") rather than the filename (`release.yml`). Also confirm the TestPyPI project name matches the distribution name actually being uploaded -- a pending publisher registered under a differently-spelled project name will not match.

(2) ADD AN OIDC-CLAIMS DIAGNOSTIC STEP TO release.yml. Agent-authorable. In the publish-testpypi job, BEFORE the upload action runs, mint the Actions OIDC token for the PyPI audience and print its DECODED claims -- at minimum `sub`, `repository`, `workflow_ref`, and `environment`. This turns the next `invalid-publisher` from a guess into a two-second diff against the registration screen.

  HARD CONSTRAINT: never print the token itself, and never echo it into a step output, artifact, or log. Print only the decoded claim fields named above. The step must not fail the job if minting fails -- it is a diagnostic, not a gate (the gating decision belongs to the dependent task).

(3) VERIFY ON A REAL TAG PUSH. The only true verification is a `v*` tag push in which publish-testpypi completes green and the artifact appears on test.pypi.org. USER-ONLY per .claude/rules/pr-prohibition.md: `git push`, `git tag`, `/tag`, `/merge`, and any twine upload are user-initiated. An agent may author and commit the workflow change; it may not exercise it. If a real tag is not wanted purely for verification, note that `workflow_dispatch` cannot substitute unless the workflow already exposes it AND the trusted publisher's claims would still match -- a non-tag ref changes `ref` and `workflow_ref`, so a dispatch-based rehearsal may fail for reasons unrelated to the registration. Prefer verifying on the next genuine release tag.

DONE MEANS: publish-testpypi completes green on a real tag push, the diagnostic step is in place and redacting correctly, and the dependent hardening task is unblocked. It does NOT mean TestPyPI is a gate -- that is explicitly out of scope here.

FILE OVERLAP: this task and `harden_release_ci_testpypi_gate` both edit `.github/workflows/release.yml`. They MUST NOT run concurrently. This task runs FIRST; the other re-reads the file afterward rather than working from a stale copy.

---

### 160. Verify bimodal oracle budget and watch unstable marker
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: Task 159
- **Research**: [160_verify_bimodal_oracle_budget_and_watch_unstable_marker/reports/01_gating-floor-unstable-marker-and-xdist-lead.md]
- **Plan**: [160_verify_bimodal_oracle_budget_and_watch_unstable_marker/plans/01_unstable-marker-and-watch-classifier.md]
- **Summary**: [160_verify_bimodal_oracle_budget_and_watch_unstable_marker/summaries/01_unstable-marker-and-watch-classifier-summary.md]

**Description**: Follow-up to task 159 (fix_bimodal_flake_and_unstable_category). That task's repair-first
attempts did not fully close either defect: BM_CM_1 was quarantined (no available encoding fix),
and the oracle floor's budget widening landed but is NOT YET VERIFIED on real CI (agents cannot
push or trigger workflow_dispatch). This task starts from that frontier -- it must NOT repeat
work already ruled out.

(1) WHICH TESTS ARE MARKED unstable AND WHY.
`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` is marked `pytest.mark.unstable`
(see `UNSTABLE_EXAMPLES` in
code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py). Its written exit
criterion, quoted verbatim from the marker site: "the marker comes off when EITHER 20 consecutive
unstable-watch runs record zero failures (nightly cadence, ~3 weeks), OR a genuine encoding fix
collapses the tail across a >= 20-seed sweep with no undecided draw at max_time = 60. A single
green CI run never qualifies." This task's job regarding BM_CM_1 is to watch for that exit
criterion being met (via unstable-watch.yml's automated READY TO PROMOTE surfacing) and, if met,
carry out the mechanical promotion steps in TESTING_GUIDE.md section 8.9 -- NOT to re-attempt a
fix from scratch without first reading item (5) below.

(2) STANDING VERDICT ON BM_CM_1 -- DO NOT RE-TUNE max_time.
BM_CM_1_settings' comment in examples.py records the standing, twice-affirmed verdict: no budget
closes the divergent-draw tail. A third recalibration would re-learn what is already documented.
Any future work on BM_CM_1 must target a genuine encoding or algorithmic change, evaluated across
a real seed sweep, never a bigger max_time number.

(3) ORACLE FLOOR MEASUREMENTS AND THE DO-NOT-LOWER-THE-FLOOR INSTRUCTION.
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` in
oracle/bimodal_logic/tests/test_cross_oracle_differential.py failed on real CI at 96/103 (run
31628414697, 7 timeouts) and 95/103 (run 31628228088, 8 timeouts), both against floor=100, both
with 0 disagreements. The identical test passed 103/103 locally, twice, both unrestricted on 24
cores (194.64s) and CPU-restricted to 2 cores via `taskset -c 0,1` (176.06s, no degradation).
`GATING_RECHECK_SOLVE_TIMEOUT_MS` was widened 20000 -> 40000ms in response (see that constant's
full justification comment), and `differential-tests.yml`'s `--timeout` was raised 900 -> 1500 in
the same commit. `MIN_CONCLUSIVE_GATING_FORMULAS` was deliberately NOT lowered (stays 100) -- it
encodes a real quality property. This instruction carries forward unchanged: do not lower the
floor to reach green; investigate and re-measure instead.

(4) CI VERIFICATION OBLIGATION -- DISCHARGED 2026-08-25, RESULT NEGATIVE. DO NOT RE-VERIFY.
The widened GATING_RECHECK_SOLVE_TIMEOUT_MS=40000ms HAS now been exercised on real CI, on the
Differential Oracle Tests workflow at commit 93cda5b9. Result:
`scan report: agreements=96 disagreements=0 timeout_count=7 conclusive=96/103` against floor=100
-- byte-for-byte identical to the pre-widening 20000ms measurement already recorded in item (3)
(run 31628414697: 96/103, 7 timeouts, 0 disagreements). Doubling the budget 20000 -> 40000ms
bought exactly ZERO additional conclusive formulas. Do not widen it a third time and do not
re-run this verification expecting a different answer: identical counts at 2x budget indicate the
7 shortfall formulas are budget-INDEPENDENT in this range on CI hardware, not marginally over the
line -- which is what the constant's own comment block already predicted ("conclusiveness is
essentially budget-independent in this range... not a tuning artifact of the budget chosen").
The floor stays at 100 (item (3)'s do-not-lower instruction is unchanged and now doubly earned).
The documented fallback is therefore UNBLOCKED and is this task's remaining primary job: mark
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` `unstable` under the
same four entry criteria used for BM_CM_1 (see TESTING_GUIDE.md section 8.9 and test_bimodal.py's
UNSTABLE_EXAMPLES block for the pattern to follow), which routes it to unstable-watch.yml where it
stays observed rather than silently dropped. Worth confirming while doing so, since the report
gives only counts: whether the SAME 7 formulas time out across runs. If they are the same 7, that
is a stable, nameable subset worth recording at the marker site rather than an ambient-load story.
One open lead the widening never tested: this test is not `xdist_serial`-marked, so
oracle/run-oracle-suite.sh's -n 6 pass runs it alongside five other workers on a 4-vCPU runner --
serial isolation is a distinct remedy from budget widening and has not been tried.

(5) WHAT IS ALREADY RULED OUT -- START FROM THIS FRONTIER.
For BM_CM_1 / the Future-operator quantifier family: z3.FreshInt substitution (regresses even
non-aliased single-instance formulas -- deterministic, not seed noise); explicit
ForAllTime/ExistsTime pattern/trigger hints (Z3 rejects the only syntactically-discoverable
candidate at construction; ExistsTime's candidate is provably inert post-Skolemization); finite
unrolling of ForAllTime/ExistsTime over the statically-known time domain (helps 5 of 7 seeds,
regresses 2 of 7 from deciding to undecided -- inconclusive-to-negative on net; see operators.py's
`_fresh_bound_int` docstring for the full measurement table). For the oracle floor: 2-core local
CPU restriction via `taskset` does NOT reproduce the CI shortfall (103/103 conclusive either way)
-- ruling out genuine harness cost growth as the explanation and pointing at CI
hardware/contention (GitHub's 4 vCPU/16GB standard runners vs. the 24-core/30GB derivation host)
as the live hypothesis the widened budget targets.

(6) THE unstable-watch.yml PROMOTION PATH AND THE 20-RUN THRESHOLD.
`.github/workflows/unstable-watch.yml` runs nightly (`0 5 * * *`) plus `workflow_dispatch`,
selects `-m unstable` across both the code/ and oracle/ trees, classifies each failure as TIMING
(the documented signature -- duration >= 0.8x max_time and the expected assertion message) or NEW
(anything else, which fails the job loudly), and emits a `READY TO PROMOTE` notice once the
consecutive-green streak reaches 20 (queried via `gh run list`, no committed state). This task
should monitor that surfacing rather than manually counting runs, and follow TESTING_GUIDE.md
section 8.9's mechanical promotion steps once triggered.

task_type: python. file_scope: the bimodal theory package
(code/src/model_checker/theory_lib/bimodal/), its tests, and the oracle bimodal tree
(oracle/bimodal_logic/).

---

### 158. Harden release ci testpypi gate
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: Task 161

**Description**: Harden the release CI pipeline so TestPyPI becomes a real verification gate before production PyPI, and close the friction points observed during the 1.3.0 release run (2026-08-12, Actions run 31628414655). The 1.3.0 publish SUCCEEDED -- this task is about making the next one safer and less manual, not about fixing a broken release.

(1) HEADLINE: MAKE TESTPYPI A GATE, NOT A SOFT CANARY. Today `.github/workflows/release.yml`'s publish-testpypi job carries `continue-on-error: true` and publish-pypi merely `needs: [build, publish-testpypi]`, so a TestPyPI failure is invisible to the gate. During the 1.3.0 run publish-testpypi FAILED with `invalid-publisher: valid token, but no corresponding publisher (Publisher with matching claims was not found)` and the pipeline proceeded to publish to production PyPI anyway. That is exactly the shape of failure the rehearsal job exists to catch. Three layers, in order of value:

  (a) Drop `continue-on-error: true` so an upload failure blocks. Note the tradeoff the current comment documents: this was deliberate so an unconfigured TestPyPI never blocks production. Preserve an explicit escape -- e.g. a `workflow_dispatch` boolean input `skip_testpypi` (default false) -- rather than silently tolerating failure. Deliberate-and-visible beats silent.

  (b) Add a `verify-testpypi` job between publish-testpypi and publish-pypi that INSTALLS the just-uploaded artifact from TestPyPI and smoke-tests it. Upload success alone proves only that bytes moved. Required details:
      - TestPyPI does not mirror dependencies, so z3-solver must resolve from real PyPI:
        `pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ "model-checker==${VERSION}"`
      - TestPyPI index propagation lags upload; wrap the install in a bounded retry (e.g. 10 attempts, 15s apart) rather than a bare install that flakes.
      - Smoke test at minimum: import the package, assert `model_checker.__version__` equals the tag version, and run `model-checker --help`. Extend to the four-theory golden path once item (4) below makes that scriptable.
      - Gate publish-pypi on this job, not merely on the upload job.

  (c) Consider a human confirmation gate: adding a required-reviewer protection rule to the `pypi` GitHub Environment makes publish-pypi wait for an explicit click after TestPyPI verification passes, with zero workflow code. Both `pypi` and `testpypi` Environments currently exist with NO protection rules. Evaluate whether this is wanted -- it trades automation for control, and may be redundant once (b) exists.

(2) MOVED OUT -- DO NOT EXECUTE HERE. Fixing the TestPyPI trusted-publisher registration and adding the OIDC-claims diagnostic step is now owned by the separate unblock task `fix_testpypi_trusted_publisher` (a declared dependency of this task; see the DEPENDENCY note at the end). It was split out because it is a PREREQUISITE, not a peer: item (1)(b)'s `verify-testpypi` job cannot be built or exercised while TestPyPI uploads are rejected at the OIDC token exchange, and the registration itself is user-only web-UI work with no agent-authorable component. Treat a working TestPyPI upload as an INPUT to this task. If that dependency has not completed, do not attempt to re-derive or re-fix the registration here -- stop and report.

(3) ADD A CHEAP FAIL-FAST PREFLIGHT JOB. The 1.3.0 run spent the entire 9-job matrix (ubuntu/macos/windows x py3.10-3.12) plus the build before any publish was attempted. A preflight job costing seconds should run first and assert:
    - the tag version matches `code/pyproject.toml` version, `flake.nix:25`, and `flake.nix:137` (three literals that can drift independently; `model_checker.__version__` derives via importlib.metadata so it is not a fourth)
    - `code/CHANGELOG.md` has a non-empty entry for the version being released
    - the tag is an annotated tag on a commit reachable from the default branch
  Each of these was verified BY HAND during 1.3.0 and each is mechanically checkable.

(4) MAKE PROJECT GENERATION NON-INTERACTIVE (blocks CI smoke testing). `model_checker/builder/project.py:159,165,706` call `input()` with no non-interactive escape, and `__main__.py`'s `--load_theory/-l` routes through `ask_generate()`. The golden path therefore CANNOT be scripted: during 1.3.0 verification a non-interactive run died with `EOFError: EOF when reading a line` and produced a false 0/4 failure that took several passes to distinguish from a real defect. Worse, `-l <theory> <dir>` silently ignores the directory argument and prompts for a name anyway. Add a non-interactive path -- e.g. `--yes/-y` plus a project-name argument, or honor the positional directory -- and make it exit non-zero on any prompt that would block. This is a prerequisite for putting the four-theory golden path into item (1)(b), and is a user-facing usability fix in its own right.

(5) VERIFY PUBLICATION VIA THE JSON API, NOT THE SIMPLE INDEX. Post-publish, `pip index versions model-checker` still reported 1.2.12 as latest for a noticeable window while `https://pypi.org/pypi/model-checker/json` already showed 1.3.0 -- simple-index CDN caching. A verification step that polls the simple index will produce false negatives. Use the JSON API (with bounded retry) for any automated post-publish confirmation, and correct any documentation in `.github/RELEASE_SETUP.md` or the checklist template that recommends `pip index versions` as the authoritative check.

(6) GITIGNORE THE ORCHESTRATOR RUNTIME FILES. `specs/.orchestrator-multi-state*.json` and `specs/.return-meta-multi-*.json` are ephemeral per-session runtime state but are NOT gitignored, so they accumulate as untracked files and dirty the working tree. This directly blocked `/tag`'s clean-tree precondition during the 1.3.0 release and forced a housekeeping commit (e6ab4868) between the rehearsal-evidence commit and the tag. Add them to `.gitignore` alongside the already-ignored `.orchestrator-loop-guard`. Confirm the exclusion set in `.claude/context/standards/orchestrator-runtime-files.md` agrees.

(7) GUARD THE WORKFLOW-FILE ORDERING HAZARD. At tag time `.github/workflows/release.yml` had an uncommitted-then-unpushed fix (`pip install build twine` -> `... wheel`) while origin carried the older copy. Because Actions runs the workflow as it exists AT THE TAGGED COMMIT this resolved correctly, but only because the branch was pushed before the tag. Make the ordering explicit in `.github/RELEASE_SETUP.md`, and consider a preflight assertion (item 3) that the tagged commit's release.yml matches the default branch's.

(8) AUTOMATE THE REHEARSAL-EVIDENCE FRESHNESS CHECK. The publish checklist carries a manual instruction: re-run `code/scripts/release-verify.sh --ref <prev>` if any commit touched `code/src` since the evidence was captured. This is a `git log <evidence-commit>..HEAD -- code/src` one-liner and should be mechanical -- either a preflight assertion or a line in release-verify.sh that records the commit it was run against and a companion check that validates it.

INCIDENTAL, CONFIRM DO NOT ACT: pip resolved z3-solver 5.0.0.0 against the `>=4.8.0` floor and all four theories ran clean from the published 1.3.0 wheel (4/4 exit 0, real countermodel output). No upper pin is warranted. Re-confirm on the next release; only constrain if something actually breaks.

AGENT CONSTRAINT: per .claude/rules/pr-prohibition.md, `git push`, `git tag`, `/merge`, `/tag`, and any twine upload remain USER-ONLY. Trusted-publisher registration and GitHub Environment protection rules are web-UI work no agent can perform -- surface them as user gates. Workflow changes can be authored and committed by an agent but are only exercised by a user-initiated tag push.
=== ADDENDUM (added after reviewing the v1.3.0 Actions runs) ===

The v1.3.0 tag push fired FOUR workflows over the same commit; two failed. Neither gated the release (Release itself concluded success and published cleanly), but both need treatment and one was already fixed.

(9) ALREADY FIXED, VERIFY ONLY -- duplicate workflow runs on tag pushes. `tests.yml` and `packaging.yml` carried an unqualified `on: push`, and `differential-tests.yml`'s `paths` filter is NOT applied by GitHub to tag pushes, so a release tag re-ran the entire regression suite that `release.yml`'s own 3-OS x 3-Python `test-and-release` matrix had already run. Fixed in commit b3822ac7 by adding `tags-ignore: ['**']` to all three push triggers. This task should VERIFY the fix held on the next release tag (expect: only `Release` appears in the Actions list for a `v*` ref) and should NOT redo it.

(10) HARDEN OR QUARANTINE THE Z3 DIVERGENT-DRAW FLAKE. `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` failed in the tag-triggered Tests run (1 failed, 1999 passed, 254 skipped) while PASSING in release.yml's own matrix on the identical commit and on the immediately preceding master push. Do NOT treat this as a budget miscalibration: `examples.py`'s BM_CM_1_settings comment already records a 15->60s recalibration and states explicitly that a divergent draw was measured undecided at 600s (~64x median) and that "the divergent-draw residual is accepted and recorded: no budget closes it". Raising `max_time` again is therefore known-ineffective. The fix belongs at the test/CI layer, not the budget layer. Options to evaluate: pin `smt/sat.random_seed` for this example in CI to make it deterministic (must select a known-decided seed, and costs draw diversity); adopt bounded automatic reruns for the known-divergent examples only (e.g. pytest-rerunfailures scoped by marker, never suite-wide); or mark it with an explicit flaky marker that keeps it visible but non-gating. Whichever is chosen must NOT silently hide a genuine future regression in this example -- the divergent tail is a solver property, an actual semantic break would look different and must still fail loudly.

(11) INVESTIGATE THE ORACLE CONCLUSIVE-POPULATION SHORTFALL (PRE-EXISTING, NOT RELEASE-CAUSED). `oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` fails with "Only 96 of 103 formulas were conclusive (floor=100); this is a budget/performance regression to investigate, not a semantic one." Confirmed pre-existing and NOT caused by this release: the same test failed at 95/103 on the master push at 18:33, two minutes BEFORE the tag push, and the workflow has been failing on master repeatedly since at least 2026-08-10. The shortfall is consistent (95-96 vs floor=100) on GitHub shared runners, i.e. the same shared-tenancy contention class as item (10). DO NOT lower the floor to make the red go green -- the assertion encodes a real quality property and its own message names it a regression to investigate. Determine whether the shortfall is (a) genuine cost growth in the oracle harness, (b) shared-runner contention that a larger per-formula budget would absorb, or (c) a floor set from quiet-host measurements that was never valid on CI hardware. Only after that diagnosis is it legitimate to adjust either the budget or the floor, and any floor change must be justified in-comment the way BM_CM_1's budget recalibration was.

(12) DECIDE WHETHER THE ORACLE SUITE SHOULD GATE ANYTHING. The oracle tree is excluded from the wheel, so its suite has no bearing on a published artifact, yet it runs ~12 minutes per trigger and has been red on master for days. Either fix it to green and keep it gating, or make its non-gating status explicit -- a permanently-red required-looking workflow trains everyone to ignore the Actions list, which is precisely what let items (10) and (11) go unnoticed until a release surfaced them.
=== SUPERSESSION NOTE (items 10-12) ===

Items (10), (11), and (12) above are SUPERSEDED by the bimodal-flake task (`fix_bimodal_flake_and_unstable_category`) and MUST NOT be executed here. Do not treat them as open scope; they are retained above only because they carry the evidence and the do-not-do-the-obvious-wrong-thing warnings that task inherits.

  - Item (10) (harden/quarantine the BM_CM_1 flake) -> that task's phases (1) and (3). Its framing is stronger than item (10)'s: FIX the tail first, quarantine only the residue.
  - Item (11) (oracle conclusive-population floor) -> that task's phase (2), with the same do-not-lower-the-floor instruction.
  - Item (12) (should the oracle suite gate anything) -> answered by that task's phases (4)-(5): the suite keeps gating, minus any member marked `unstable`, with a non-gating scheduled watch workflow keeping the quarantined set observed.

Item (9) is unaffected and remains verify-only (the duplicate-tag-trigger fix landed in commit b3822ac7).

CONCURRENCY: this task and the bimodal-flake task overlap on `.github/workflows/tests.yml`, `.github/workflows/release.yml`, and `.github/workflows/differential-tests.yml`. They MUST NOT run concurrently -- both edit the same pytest selection expressions. Run one, then re-read its outcome before starting the other. This task's headline TestPyPI-gate work (items 1, 3-8) is otherwise fully independent of the bimodal defects and is the higher-priority half.

=== DEPENDENCY: fix_testpypi_trusted_publisher (see `dependencies` in state.json) ===

That task must COMPLETE before this one starts, for two independent reasons:

  (i) SEQUENCING. Its output -- a TestPyPI upload that actually succeeds -- is the precondition for item (1)'s entire gate story. Promoting `continue-on-error: true` to a hard gate (1)(a) while the trusted publisher is still misconfigured would convert a silent canary failure into a HARD BLOCK on every production release. Do not land (1)(a) before the dependency is verified green on a real tag push.

  (ii) FILE OVERLAP. Both tasks edit `.github/workflows/release.yml` -- the dependency adds a diagnostic step to the publish-testpypi job, this task restructures that same job and its `needs:` edges. Serialize; re-read the file after the dependency lands rather than working from a stale copy.

Evidence the dependency is real and still open: the `invalid-publisher` failure recurred on the v1.3.1 tag push, after the 1.3.0 run that originally motivated this task. The registration has NOT been fixed in the interim.

---

### 154. Extension certified search over small bimodal models
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: Task 152, Task 153

**Description**: THE PAYOFF, and the one task in this group where OVER-CLAIMING is the principal risk. With the frame axioms in place, the paper's `thm:extension` becomes applicable to bimodal countermodels: every partial history the solver finds is a fragment of a genuine total world history in $H_\F$. Use that to move work out of the solver -- but only the half the theorem actually covers.

WHAT THE THEOREM BUYS. Today the solver is made to approximate totality inside the search: `world_interval_constraint` gives each world a time interval, `lawful` chains unit steps across it, and the `capped_skolem_abundance_constraint` / `depth_bounded_skolem_abundance_constraint` family manufactures time-shifted copies. The extension theorem says the interval-and-shift scaffolding is not needed in order to KNOW that a found history is realizable: any partial assignment consistent with the frame axioms already lies inside some total history. So the solver may search genuinely small partial structures -- fewer worlds, narrower windows, no shift closure -- with totality discharged afterwards.

WHAT IT DOES NOT BUY. This must be stated in the code and in the summary, not only here. `thm:extension` is EXISTENTIAL. It certifies that a witness exists; it says nothing about universal obligations. Truth of `\Box \phi` quantifies over all of $H_\F$, and truth of `\Future \phi` and `\Past \phi` over all of $\D$, whereas `NecessityOperator.true_at` currently quantifies over the solver's finite world set and the tense operators over the bounded window. The abundance constraints approximate that second column and the extension theorem DOES NOT REPLACE THEM. Any design that drops abundance wholesale and cites `thm:extension` as cover is wrong. The preceding audit's baseline records exactly which examples this bites; use it.

DELIVERABLE 1 -- POST-HOC CERTIFICATION. After extraction, take the countermodel's partial histories and produce the finite lasso witness of BimodalLogic 441 (prefix plus cycle, forward and backward), verify that it satisfies the frame axioms and agrees with the extracted window, and attach it to the model structure. This is the concrete, checkable form of the claim "this bounded history is a fragment of a possible world", and it replaces the prose assurance currently carried in the `task_restriction` soundness comment.

DELIVERABLE 2 -- SPLIT THE CONSTRAINT SET BY POLARITY. Formulas whose falsification obligations are purely existential -- no `\Box` or universal tense operator in a verifying position -- need no abundance closure and can be searched at smaller `M` with fewer worlds. Formulas carrying universal obligations keep the current treatment. Drive this off the EXISTING `temporal_depth` machinery, which already performs depth-aware abundance selection, rather than adding a second parallel mechanism beside it.

DELIVERABLE 3 -- MEASURE IT. The claim here is a performance claim as well as a soundness claim. Report solve times against the audit baseline for the examples in each polarity class, and report honestly if the win turns out to be small or absent. A correct-but-slower result is a legitimate outcome and should be reported as such rather than tuned until it looks good.

DELIVERABLE 4 -- SURFACE THE CERTIFICATE. A user who gets a bimodal countermodel should be able to see the extension witness, not just the bounded window. Fit this to the existing output conventions rather than inventing a new output channel.

DEPENDENCIES. The frame-axiom task (without *Seriality* and interpolation the extension theorem does not apply at all), the audit task (baseline), and BimodalLogic 441 (the lasso construction and the agreement lemma, including its explicit statement of what does not transfer).

---

### 153. Assert missing frame axioms in bimodal semantics
- **Status**: [NOT STARTED]
- **Task Type**: z3
- **Topic**: semantics
- **Dependencies**: Task 152

**Description**: Bring `BimodalSemantics`'s frame class up to the JPL paper's `def:frame`, so that `thm:extension` becomes applicable to its countermodels. Today it is not: two of the paper's four frame axioms are missing, and they are precisely the two the extension proof consumes.

DELIVERABLE 1 -- *SERIALITY*. Assert that for every world state `w` and every valid non-negative duration `x` there exist `u` and `v` with `task_rel(w, x, u)` and `task_rel(v, x, w)`. Over the finite state space `BitVec[N]` this is a bounded obligation. PREFER a grounded or Skolemized encoding over a nested `ForAll`/`Exists`: the source comment on the disabled `task_restriction` documents that `ForAll`/`Exists` alternation causes MBQI timeouts at `M >= 3`, and that lesson applies directly here. Benchmark before and after; do not land an encoding that reintroduces the timeout the disabled constraint was disabled for.

DELIVERABLE 2 -- INTERPOLATION (the missing half of *Compositionality*). The paper's axiom is a biconditional; only composition is currently asserted. The direct fix is `task_rel(w, d1+d2, v) -> exists u . task_rel(w, d1, u) and task_rel(u, d2, v)` under the existing duration guards.

EVALUATE THIS ALTERNATIVE FIRST, it is strongly preferred if it measures acceptably: instead of asserting both halves of a biconditional over an unconstrained ternary predicate, DEFINE `task_rel(w, d, v)` as the `d`-step reachability of a single unit relation `R`. Under that definition *Compositionality* holds in both directions BY CONSTRUCTION, interpolation included, and `converse` and `nullity_identity` become theorems rather than assertions. That trades the five quantified variables of `build_forward_comp_constraint` for a definitional encoding, and may be a net solver win as well as a soundness win. Measure it honestly; if it loses badly, fall back to asserting the missing half directly and record the measurement so the question is not reopened blind.

DELIVERABLE 3 -- RECORD, DO NOT ASSERT, THE TWO FREE AXIOMS. *Spherical* holds because `WorldState = BitVec[N]` is finite -- cite BimodalLogic's `spherical_of_finite` and the corresponding paper corollary rather than re-deriving. *Limit* follows from the already-asserted `nullity_identity` biconditional over a discrete duration order -- cite BimodalLogic's `TaskFrame.limit_of_succOrder`, whose hypothesis is exactly that biconditional. Put the result in `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` as a frame-class table distinguishing the four ASSERTED axioms from the two FREE ones, with the citation for each. The current docstring in `build_frame_constraints` claims a three-axiom TaskFrame correspondence that this task supersedes; update it rather than leaving two accounts in the tree.

DELIVERABLE 4 -- THE DURATION-DOMAIN HONESTY ITEM. The paper requires $\D$ to be a nontrivial totally ordered abelian GROUP; `is_valid_duration` bounds durations to the open interval from `-M` to `M`, which is not a group. Either state and justify the embedding -- the finite structure determines a frame over $\D = \Z$ by taking `task_rel` to be the reachability relation of the unit relation, which is defined at every integer duration -- or record it explicitly as an open gap. Do not leave it unstated: it is load-bearing for the follow-on certification work, which claims things about total histories over all of $\Z$.

VERIFICATION. The full bimodal suite must stay green, and the baseline from the preceding audit must be used to detect verdict flips. A verdict flip is NOT automatically a regression here -- adding a missing frame axiom legitimately shrinks the frame class and can turn a SAT into an UNSAT -- but every flip must be explained individually in the summary, never absorbed silently.

DEPENDENCIES. The bimodal frame-class audit (baseline and ledger) and BimodalLogic 440 (the citation backing Deliverable 3).

---

### 152. Audit bimodal frame class and verdict dependence
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: semantics
- **Dependencies**: None

**Description**: AUDIT ONLY -- no semantics change, no constraint change, no examples change. Produce the soundness ledger and the regression baseline that the two follow-on tasks need, because both alter the frame class the solver searches and neither can be landed safely without knowing which existing verdicts depend on what.

WHAT IS ALREADY ESTABLISHED (verified 2026-08-11; do not re-derive, but DO re-resolve the code references, which will drift):

  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py::build_frame_constraints` asserts eleven constraints, three of which are billed as TaskFrame axioms: `nullity_identity` (a biconditional, `task_rel(w,0,u) <-> w=u`), `converse` (a guarded biconditional), and `forward_comp`.

  - `forward_comp` is ONLY the right-to-left half of the JPL paper's *Compositionality*, which is a BICONDITIONAL: "$w \Rightarrow_{x+y} v$ if and only if $w \Rightarrow_x u$ and $u \Rightarrow_y v$ for some $u \in W$" (`def:frame`). The left-to-right (interpolation) half is asserted nowhere.

  - *Seriality* is asserted nowhere. `grep -rn "serial" semantic/` returns nothing.

  - Those two missing axioms are EXACTLY the two the paper's `lem:constraint` consumes -- *Seriality* for the one-sided case and interpolation for the flanked case (the Lean formalization names the corresponding steps `nonempty_fib_of_serial` and `nonempty_seg_of_interpolates`). Consequence: `thm:extension` cannot currently be invoked on a ModelChecker countermodel at all. This is the single most important fact in this audit.

  - `operators.py::NecessityOperator.true_at` quantifies over `is_world(other_world)` -- the finite set of world IDs the solver chose -- not over $H_\F$. `FutureOperator` and `PastOperator` quantify over the bounded time window, not over $\D$.

  - `task_restriction`, which would ground every `task_rel` triple in a concrete world history, is written but DISABLED for solver-performance reasons, with a soundness analysis in the source comment that this audit should assess rather than accept.

  - The extension theorem itself is NOT missing upstream: it is fully proved and axiom-clean in the BimodalLogic Lean repository at `FormalSystem/Semantics/Extension/`. The gap is entirely on this side.

DELIVERABLE 1 -- THE LEDGER. A report under `specs/{NNN}_{SLUG}/reports/` separating the semantics' obligations into two columns:
  (a) obligations discharged by an EXISTENTIAL witness -- a countermodel to `\Box \phi`; a witness time falsifying `\Future \phi`;
  (b) obligations requiring a UNIVERSAL guarantee -- truth of `\Box \phi` across all of $H_\F$; truth of `\Future \phi` across all of $\D$.
`thm:extension` addresses only column (a). State plainly that the `capped_skolem_abundance_constraint` / `depth_bounded_skolem_abundance_constraint` shift-closure family is the current approximation of column (b) and that NO theorem in the paper replaces it. This distinction is the thing the follow-on work is most likely to blur, so make it hard to miss.

DELIVERABLE 2 -- THE BASELINE. Classify every example in `code/src/model_checker/theory_lib/bimodal/examples.py` by whether its expected verdict depends on the abundance approximation. Method: re-run each example with the abundance constraints removed and record which verdicts flip. Record results under `specs/{NNN}_{SLUG}/baselines/` per the project's per-task baseline convention. This is the regression net for both follow-on tasks, and without it neither can distinguish a legitimate frame-class narrowing from a genuine regression. Note that BM_CM_1 example_case7 has a documented Z3 timing flake under CPU contention -- run on a quiet host and record the condition.

DELIVERABLE 3 -- THE `task_restriction` VERDICT. State whether the disabled `task_restriction` becomes unnecessary once interpolation and seriality are asserted, or whether it remains an independent gap. Its stated purpose (grounding every `task_rel` triple in a world history) overlaps with what interpolation plus the extension theorem provide, and that overlap should be settled on paper here rather than discovered during implementation. Do NOT enable it in this task.

NON-GOALS. No change to `core.py`, `operators.py`, or `examples.py`. This task ends with two documents and a baseline.
