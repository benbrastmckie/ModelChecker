---
next_project_number: 168
---

# TODO

## Task Order

*Updated 2026-08-25. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 152,160,161,167 | -- | testing, semantics, release-engineering |
| 2 | 153,158 | 152,161 | semantics, release-engineering |
| 3 | 154 | 153 | semantics |

**Grouped by Topic** (indented = depends on parent):

### Testing

167 [NOT STARTED] — Fix flaky TestMixedFormulas failures in oracle/bimodal_logic/test

### Semantics

152 [NOT STARTED] — AUDIT ONLY -- no semantics change, no constraint change, no examp
  └─ 153 [NOT STARTED] — Bring `BimodalSemantics`'s frame class up to the JPL paper's `def
    └─ 154 [NOT STARTED] — THE PAYOFF, and the one task in this group where OVER-CLAIMING is

### Release Engineering

160 [NOT STARTED] — Follow-up to task 159 (fix_bimodal_flake_and_unstable_category). 
161 [NOT STARTED] — Make TestPyPI publishing succeed at all: fix the TestPyPI trusted
  └─ 158 [NOT STARTED] — Harden the release CI pipeline so TestPyPI becomes a real verific

## Tasks

### 167. Flaky testmixedformulas failures
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None

**Description**: Fix flaky TestMixedFormulas failures in oracle/bimodal_logic/tests/test_oracle_interface.py - test_mixed_or_diamond_prev and test_mixed_and_all_future_neg both fail in some pytest runs and pass in others (test_mixed_and_all_future_neg was observed failing in one full-file run and passing in the next with no code change), so determine whether the nondeterminism comes from Z3 solver behavior, test ordering/state leakage, or a genuine semantics defect, then make the outcomes deterministic

---

### 166. Unstable watch workflow failures
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: release-engineering
- **Dependencies**: None
- **Research**: [166_unstable_watch_workflow_failures/reports/01_root-cause-and-fix-recommendation.md]
- **Plan**: [166_unstable_watch_workflow_failures/plans/01_guard-bimodal-harness-import.md]
- **Summary**: [166_unstable_watch_workflow_failures/summaries/01_guard-bimodal-harness-import-summary.md]

**Description**: Research and fix recurring unstable-watch.yml GitHub Actions failures reported at https://github.com/benbrastmckie/ModelChecker/actions/runs/32813308100 - systematically diagnose the root cause of the reported errors, evaluate long-term solutions, and design a high-quality fix before implementing

---

### 165. Improve py spec for haskell port
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [165_improve_py_spec_for_haskell_port/reports/01_haskell-porting-readiness.md]
- **Plan**: [165_improve_py_spec_for_haskell_port/plans/02_py-spec-port-improvements.md]
- **Summary**: [165_improve_py_spec_for_haskell_port/summaries/02_py-spec-port-improvements-summary.md]

**Description**: Improve haskell/py-spec/ so it is sufficient as a porting specification for a Haskell reimplementation of the ModelChecker. The QC review linked on this task found the tree architecturally accurate but shallow: it maps control flow, not content. Three P0 port-blockers: (1) no operator anywhere has its truth condition stated -- 03-operators.md gives method signatures only, for negation through the counterfactual; (2) the semantic helper predicates the modal/counterfactual operators depend on (is_alternative, maximal, compatible, max_compatible_part) and the exact exhaustive frame-constraint list are never given; (3) the exclusion theory Skolem witness-predicate mechanism -- the hardest part of unilateral truthmaker semantics to implement correctly, ~870 lines of source -- is reduced to a five-word phrase in one table cell. P1: add a worked end-to-end trace (valid + countermodel, with actual constraints and verifier/falsifier output) to serve as a golden test; survey the error/exception taxonomy against the strict/absorb/warn policy with an N=0 / empty-premises / malformed-input case table; state the determinism and ordering contract for verifier/falsifier sets; fix 08-iteration.md (cite iterate/constraints.py directly for defect #1; correct "blind to proposition valuations" -- the data is computed then discarded, not never computed). P2: compress 13-examples-and-cli.md project-generation/Jupyter/packaging tail by ~two thirds and cut the entry-points paragraph; compress 09-output-and-display.md stdout-identity detail by ~a third; add a glossary. The 14-document decomposition by pipeline stage is sound and must NOT be reorganized -- this is one new operator-semantics document, one worked-trace artifact, targeted expansion of the exclusion treatment, and compression elsewhere. Discipline for the truth-condition tables: theory-agnostic mathematical notation following the existing 05-state-encoding.md table style, never Python transliteration.

---

### 164. Populate py spec python architecture
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [164_populate_py_spec_python_architecture/reports/01_python-architecture-spec.md]
- **Plan**: [164_populate_py_spec_python_architecture/plans/01_py-spec-document-tree.md]
- **Summary**: [164_populate_py_spec_python_architecture/summaries/01_py-spec-document-tree-summary.md]

**Description**: Populate haskell/py_spec.md with a concise description of the core architecture for the Python implementation of the ModelChecker, including the modular compiler design for generating SMT-LIB constraints from sentences expressed in an extensible DSL and the host of features and tools for adjusting and evaluating the countermodels that the ModelChecker finds

---

### 163. Full cli suite against installed wheel
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [163_full_cli_suite_against_installed_wheel/reports/01_installed-cli-verification.md]
- **Plan**: [163_full_cli_suite_against_installed_wheel/plans/01_installed-cli-test-mode.md]
- **Summary**: [163_full_cli_suite_against_installed_wheel/summaries/01_installed-cli-test-mode-summary.md]

**Description**: Run the full CLI test suite against a pip-installed wheel, not just the source tree. Every CLI test in code/tests/cli/ funnels through one helper, run_cli_command (code/tests/utils/helpers.py:14), which hardcodes both the `python -m model_checker` invocation and the PYTHONPATH injection pointing at code/src. Parametrise that single helper over MODELCHECKER_CLI_TEST_MODE = source | installed | installed-module so the entire existing suite -- including its parser-derived completeness gate (test_flag_matrix.py::test_every_registered_flag_is_covered_or_excluded) -- runs unchanged against a pip-installed console script. Default stays `source`, so the developer loop is unaffected; `installed-module` additionally yields console-script vs `python -m` parity across the whole suite, where packaging tests currently check it only for --version/--help.

MANDATORY GUARD: add a test asserting model_checker.__file__ contains site-packages when a non-source mode is active. If code/src reaches sys.path in the verification environment, imports silently resolve to the working tree and the whole suite passes without ever touching the wheel -- a silent vacuous pass that would make this entire change worthless.

MOTIVATION (NixOS blind spot): the packaging suite passes locally only because code/tests/packaging/conftest.py repairs the dynamic linker via LD_LIBRARY_PATH -- the pip-installed z3-solver wheel cannot otherwise find its bundled libz3.so on a non-FHS host. Local green therefore cannot distinguish "works everywhere" from "works because we patched it". This host also runs glibc 2.42, newer than any mainstream distro (Debian 12: 2.36, Ubuntu 22.04: 2.35, Ubuntu 20.04: 2.31), so it is the most permissive possible target and cannot detect low-end linkage breakage. Verification must therefore happen in a real distro container; a Nix FHS sandbox is NOT an acceptable substitute (you choose targetPkgs yourself so it cannot discover a missing library, it serves the same glibc 2.42, it bind-mounts real /home and /tmp so ~/.cache/pip can produce a false green, and it cannot move to CI).

ALSO IN SCOPE: (a) a small code/scripts/verify-installed-cli.sh wrapping a podman invocation for the local debug loop (requires virtualisation.podman.enable, user action); (b) attempt to retire the sole _EXCLUDED_FLAGS entry, load_theory, by piping input="y\n" through run_cli_command`s existing input parameter -- if that works the completeness gate covers the full registered flag set with no exclusions. If it does not work, leave the exclusion and its comment intact.

SCOPE BOUNDARY -- DO NOT TOUCH .github/workflows/release.yml. That file is owned by harden_release_ci_testpypi_gate, which already owns adding a post-build verification job, and which is itself blocked on fix_testpypi_trusted_publisher (user-only web-UI OIDC work). Claiming release.yml here would auto-serialise this task behind a blocked one for no reason -- this task has no dependency of its own and can start immediately. The CI wiring is recorded as recommendation R4 in the research report, with exact YAML, for that task to adopt.

REPORT FINDING WORTH ESCALATING to harden_release_ci_testpypi_gate: its item (1)(b) proposes gating on a TestPyPI install. Gating on the `dist` build artifact instead is equal or better fidelity (byte-identical wheel), avoids the cross-index nondeterminism of --extra-index-url (TestPyPI mirrors neither z3-solver nor networkx), avoids retry-flake from index propagation lag, and crucially is NOT blocked by the OIDC registration. The two are complementary, not exclusive -- artifact-gating proves the wheel works, TestPyPI verification proves upload/index metadata work -- but artifact-gating should not wait behind the other.

DO FIRST, SEPARATELY: `nix flake check` is red on master at the released commit (test_example.py::TestBuildExampleIntegration::test_iteration_via_iterate_api, "Should find initial model for A", 1 failed / 2012 passed, Actions run 31654864134). It sits exactly on the seam this task concerns: flake.nix builds against nixpkgs-native z3 and strips the PyPI dependency (pythonRemoveDeps = [ "z3-solver" ]), while users get the PyPI z3-solver wheel. Diagnose whether it is a divergent draw or a genuine version sensitivity before relying on either environment as an oracle.

DEFERRED, NOT IN SCOPE: executable documentation -- executing extracted doc commands (rather than only checking flag tokens against the parser) against an installed package, reusing test_docs_flag_matrix.py`s extractor plus this task`s installed mode. Worth its own task after this one lands.

---

### 162. Fix nonexistent cli flags in docs
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [162_fix_nonexistent_cli_flags_in_docs/reports/01_nonexistent-cli-flags-audit.md]
- **Plan**: [162_fix_nonexistent_cli_flags_in_docs/plans/01_nonexistent-cli-flags-fix.md]
- **Summary**: [code/tests/cli/test_docs_flag_matrix.py]

**Description**: Audit and fix nonexistent CLI flags documented across user-facing docs. Verified against the live argparse parser (model_checker.__main__.ParseFileFlags): the real flag set is --align_vertically --contingent --cvc5 --disjoint --load_theory --maximize --non_empty --non_null --print_constraints --print_impossible --print_z3 --save --sequential --upgrade --version --z3 plus short forms -a -c -d -e -i -l -m -n -p -q -s -u -v -z. Docs reference flags that do not exist and fail with "unrecognized arguments": (1) --subtheory / -st, 17 occurrences in docs/usage/WORKFLOW.md, docs/usage/TOOLS.md, docs/usage/PROJECT.md, docs/installation/GETTING_STARTED.md - replace with the real Python idiom logos.get_theory(subtheories=[...]), rewriting the surrounding prose about automatic dependency loading rather than doing a token swap; (2) --verbose, 4 occurrences in docs/architecture/PIPELINE.md, docs/architecture/ITERATE.md, docs/architecture/SETTINGS.md, docs/usage/OUTPUT.md, docs/usage/TOOLS.md; (3) --output-dir and --format, 6 occurrences in docs/usage/OUTPUT.md and docs/architecture/PIPELINE.md; (4) code/src/model_checker/settings/README.md has an entire "Theory-Specific Flags" section inventing --coherence-check, --witness-optimization, --imposition-depth, --state-modification, --save-output, and -M/--M (12 occurrences) - needs a decision on whether these were planned-and-dropped or never real before rewriting. Add a regression guard so docs cannot drift again: a test that extracts flag tokens from markdown code blocks and asserts each is registered on the parser. Already fixed separately and out of scope: the swapped --non_null/--non_empty help strings in __main__.py, and hyphenated long-flag spellings in docs/usage/{SETTINGS,SEMANTICS,TOOLS,README,PROJECT}.md and logos/docs/USER_GUIDE.md.

---

### 161. Fix testpypi trusted publisher
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: None

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: Task 159

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

(4) OUTSTANDING CI VERIFICATION OBLIGATION (this task's primary job).
The widened GATING_RECHECK_SOLVE_TIMEOUT_MS=40000ms has NOT been verified on real CI. This
requires a human to push and dispatch `.github/workflows/differential-tests.yml` via
`workflow_dispatch` 2-3 times (agents cannot push or trigger workflow_dispatch per
.claude/rules/pr-prohibition.md) and observe the results. Success looks like >= 100 of 103
conclusive on every dispatched run, with 0 disagreements. If it still falls short after a
genuinely widened and CI-verified budget: do NOT lower the floor a second time. The documented
fallback, only then, is marking
`TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` `unstable` under the
same four entry criteria used for BM_CM_1 (see TESTING_GUIDE.md section 8.9 and
test_bimodal.py's UNSTABLE_EXAMPLES block for the pattern to follow).

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

### 159. Fix bimodal flake and unstable category
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: release-engineering
- **Dependencies**: None
- **Research**: [159_fix_bimodal_flake_and_unstable_category/reports/01_bimodal-flake-and-unstable-category.md]
- **Plan**: [159_fix_bimodal_flake_and_unstable_category/plans/01_bimodal-flake-unstable-category.md]
- **Summary**: [159_fix_bimodal_flake_and_unstable_category/summaries/01_bimodal-flake-unstable-category-summary.md]

**Description**: Fix the bimodal solver-timing flakes, and introduce an 'unstable' test category so that whatever genuinely resists fixing stops holding up releases WITHOUT disappearing from view. Supersedes an earlier framing of this task that proposed withdrawing the bimodal theory from the published release surface; that remedy was rejected as disproportionate. The evidence says bimodal WORKS -- it shipped in 1.3.0, post-publish verification ran it from the published wheel (exit 0, ~770 lines of genuine countermodel output), and BM_CM_1 finds its countermodel on every decided draw. The defects are timing, not semantics. The theory stays registered and stays published.

PRIMARY AIM: FIX THE TESTS. The 'unstable' category is a pressure-release valve for the residue, NOT the deliverable. A run of this task that quarantines both tests without a genuine repair attempt has failed its primary aim.

THE TWO DEFECTS.
  (a) `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` -- intermittent. `examples.py`'s BM_CM_1_settings comment records a 15->60s recalibration and a divergent draw measured undecided at 600s (~64x median), concluding "the divergent-draw residual is accepted and recorded: no budget closes it". It failed in the tag-triggered Tests run while PASSING in release.yml's own matrix on the identical commit and on the preceding master push.
  (b) `oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` -- fails at 95-96 of 103 conclusive against floor=100, consistently, on GitHub runners; red on master since at least 2026-08-10. Its own assertion message calls it "a budget/performance regression to investigate, not a semantic one".

(1) ATTEMPT A REAL FIX FIRST -- (a), THE DIVERGENT DRAW. Do NOT re-tune `max_time`: the settings comment already states no budget closes this, and a second recalibration would burn a cycle re-learning that. Investigate instead: is the divergence seed-dependent (probe `smt/sat.random_seed` across a wide sweep and characterise the decided/undecided split)? Does the `\Future`/all_future operator family's quantifier bound-variable-aliasing cost (see operators.py `_fresh_bound_int` docstring, named in the settings comment as the cost-growth source) admit an encoding improvement that collapses the tail? Would a different N/M, or a tightened frame constraint, keep the same semantic content on a tractable search? A genuine encoding fix that removes the tail is the win condition here; seed-pinning is a fallback, not a fix, because it hides the tail rather than removing it.

(2) ATTEMPT A REAL FIX FIRST -- (b), THE CONCLUSIVE-POPULATION SHORTFALL. Diagnose before touching any number. Determine whether the shortfall is genuine cost growth in the oracle harness, shared-runner contention a larger per-formula budget would absorb, or a floor calibrated on quiet-host measurements that was never valid on CI hardware. DO NOT lower the floor to reach green -- the assertion encodes a real quality property. If the honest conclusion is that the floor was mis-calibrated for CI hardware, changing it is legitimate, but only with an in-comment justification of the same standard as BM_CM_1's budget recalibration (measurements, method, what was ruled out).

(3) INTRODUCE THE 'unstable' MARKER. Only for what survives (1) and (2). `code/pyproject.toml`'s `[tool.pytest.ini_options] markers` already carries this exact convention -- `slow` is the model to follow, including its style of explaining in-line how to select/deselect it. Add:
      "unstable: Tests with a documented, investigated non-semantic instability (e.g. a heavy-tailed solver draw). Deselected from release-gating runs with `-m \"not unstable\"`; run on their own by the unstable-watch workflow so they stay observed rather than forgotten."
    STRICT ENTRY CRITERIA -- this category must not become a dumping ground. A test may be marked `unstable` ONLY when all hold: the instability is understood and documented in-line at the marker site (what fails, why, what was ruled out); it is demonstrably NOT semantic (the assertion still holds on every decided/complete run); a genuine fix was attempted and its failure recorded; and an explicit EXIT criterion is written down (what must be observed for the marker to come off). "It failed once in CI" never qualifies.

(4) WIRE DESELECTION INTO THE GATING RUNS. `.github/workflows/tests.yml:73` currently runs `pytest tests/ src/model_checker -m "not packaging and not performance" -n 6 -q` -- extend the expression to also exclude `unstable`. Do the same for release.yml's `test-and-release` matrix and differential-tests.yml's invocations (lines ~45/55). Releases must not be gated on a known-unstable test; that is the entire point of the category.

(5) KEEP AN EYE ON THEM -- THE WATCH WORKFLOW IS A FIRST-CLASS DELIVERABLE. Quarantine without observation is deletion with extra steps. Add a NON-GATING workflow (e.g. `.github/workflows/unstable-watch.yml`) that runs on a schedule (nightly or weekly) plus `workflow_dispatch`, executes ONLY `-m unstable`, and reports outcomes in a form that makes the trend visible -- at minimum a job summary; better, an append-only record of pass/fail per run so the decided/undecided ratio is legible over time. It MUST NOT gate pushes, PRs, or tags. Two behaviours matter as much as the runs themselves: a test that has been green across the agreed exit threshold should be surfaced as READY TO PROMOTE back into the gating suite, and a test that starts failing in a NEW way (a semantic assertion, not the documented timing signature) must be loud, because that is a real regression hiding inside a quarantined test.

(6) DOCUMENT THE POLICY. Record entry criteria, exit criteria, the review cadence, and the promotion path in a durable place (extend `code/docs/core/TESTING_GUIDE.md` rather than inventing a new home, unless a better location exists). Include the standing rule that the `unstable` set is reviewed on a fixed cadence and that an indefinitely-quarantined test is itself a defect to escalate, not a steady state.

(7) TERMINAL DELIVERABLE -- CONDITIONAL FOLLOW-UP TASK. If (1) and (2) both fully succeed and nothing needed the marker, no follow-up is required; record that outcome. Otherwise, conclude by creating a follow-up task covering exactly what remains unstable, carrying forward concretely: which tests were marked and why; the evidence and the standing verdict that no budget closes the BM_CM_1 tail (so the follow-up does not re-tune `max_time` either); the oracle 95-96/103-vs-floor-100 measurements and the do-not-lower-the-floor instruction; each test's written exit criterion; and what was already ruled out by this task's repair attempts, so the follow-up starts from the frontier rather than the beginning. Set its `task_type` to `python` with a `file_scope` covering the bimodal theory package, its tests, and the oracle bimodal tree.

RELATIONSHIP TO THE CI-HARDENING TASK: that task's items (10) (harden/quarantine the BM_CM_1 flake), (11) (investigate the oracle floor), and (12) (decide whether the oracle suite gates anything) are SUPERSEDED by this task and must not be executed twice -- items (10) and (11) are this task's phases (1)-(3), and item (12) is answered by phases (4)-(5) (the oracle suite keeps gating, minus any unstable-marked members). The two tasks overlap on `.github/workflows/tests.yml`, `release.yml`, and `differential-tests.yml`, so they MUST NOT be run concurrently; run one, then re-read its outcome before starting the other. That task's headline TestPyPI-gate work is otherwise independent of this one.

AGENT CONSTRAINT: per .claude/rules/pr-prohibition.md, `git push`, `git tag`, `/merge`, `/tag`, and any twine upload remain USER-ONLY.

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

### 157. Dedupe theory lib version files w002
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 155
- **Research**: [157_dedupe_theory_lib_version_files_w002/reports/01_version-file-dedupe.md]
- **Plan**: [157_dedupe_theory_lib_version_files_w002/plans/01_version-file-dedupe.md]
- **Summary**: [157_dedupe_theory_lib_version_files_w002/summaries/01_version-file-dedupe-summary.md]

**Description**: Deduplicate the four identical theory_lib VERSION files to clear check-wheel-contents W002. code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION are four byte-identical files each containing `1.0.0`. check-wheel-contents flags them as `W002: Wheel contains duplicate files` and exits 1 on the built wheel; `--ignore W002` returns OK with exit 0. Independently verified twice against code/dist/model_checker-1.3.0-py3-none-any.whl. The finding is structural (four identical files), not an artifact of a stale build, so it reproduces on a fresh build.

THIS IS PRE-EXISTING, NOT A REGRESSION. It is out of scope for the CI-failure fix work that surfaced it, which deliberately reports W002 without remediating it and explicitly forbids touching the VERSION files to silence the lint. Do not treat this as urgent or release-blocking: `--ignore W002` is a legitimate signal for release verification in the meantime.

A STALE CLAIM NEEDS CORRECTING TOO: the archived rehearsal under specs/archive/125_release_engineering_and_pypi_rehearsal/ recorded check-wheel-contents as clean/OK. That no longer reproduces, consistent with specs/TODO.md:161's note that the rehearsal evidence is stale.

DECIDE THE REMEDY DELIBERATELY, do not assume deletion is correct. Research first: establish what reads these per-theory VERSION files at runtime, whether the value is load-bearing anywhere (packaging metadata, theory-version reporting, tests), and whether per-theory versioning is an intended convention that simply is not yet exercised (all four sitting at 1.0.0 is consistent with BOTH "vestigial" and "intended but never bumped"). Only then choose among: remove them in favour of a single source of truth; keep them but exclude them from the wheel; or keep them and accept W002 permanently via a pinned --ignore. Any option that changes what ships in the wheel must be checked against the packaging contract suite under code/tests/packaging/.

VERIFY BY REBUILDING. The evidence is a fresh `python -m build` plus check-wheel-contents on the resulting wheel -- a plain run should reach exit 0 without needing --ignore W002 if the remedy was deduplication. Note code/dist is gitignored (.gitignore:13, **/dist), so a local build does not perturb the working tree.

---

### 156. Portable pinned release verification runner
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None
- **Research**: [156_portable_pinned_release_verification_runner/reports/01_portable-release-verification.md]
- **Plan**: [156_portable_pinned_release_verification_runner/plans/01_release-verify-runner.md]
- **Summary**: [156_portable_pinned_release_verification_runner/summaries/01_release-verify-runner-summary.md]

**Description**: Turn the release verification named in .github/RELEASE_SETUP.md into a repeatable, pinned, portable runner -- and document it. THIS IS DELIBERATELY NOT A DOCUMENTATION-ONLY TASK. The deliverable is an executable script plus a pinned tool manifest plus the checklist prose that drives them. Prose alone would not close the actual defect, which is that the documented verification sequence is reproducible today only on one developer's machine.

THE DEFECT. RELEASE_SETUP.md:147 names `python -m build`, `check-wheel-contents`, and `twine check --strict` as part of release verification, but the repo provides no reproducible way to obtain them. flake.nix's devShells.default declares `packages = [ devPython ]`, and devPython carries only pytest, pytest-xdist, and pytest-timeout -- no build, no twine, no check-wheel-contents. Nothing in .github/ invokes the tool; the only reference is that prose line. Today the tool is available only because it happens to sit in one developer's nix profile (verified: /home/benjamin/.nix-profile/bin/check-wheel-contents, 0.6.3), and it is NOT resolvable from the flake-registry nixpkgs -- nixpkgs#check-wheel-contents, #checkWheelContents, #python3Packages.check-wheel-contents, and #python3Packages.checkWheelContents all fail to evaluate. That makes the documented verification non-reproducible for anyone else, and unpinned (0.6.3 today, silent drift later) for evidence that is meant to be COMPARED ACROSS RELEASES.

WHY THIS IS RELEASE ENGINEERING, NOT DOCUMENTATION. The release-rehearsal re-run task plans exactly this sequence -- fresh `python -m build`, `twine check --strict dist/*`, `check-wheel-contents dist/*.whl`, a wheel/sdist parity diff against the last published release, and re-recorded sha256sums -- driven off a checklist, and it will be run more than once, possibly by someone without that nix profile. Build the runner here so that work executes a checked-in procedure instead of reconstructing one from an archived narrative each time. This is precisely where clarity, consistency, and portability pay for themselves.

DELIVERABLE 1 -- THE RUNNER. A checked-in script (preferred path `code/scripts/release-verify.sh`, alongside the existing `verify-refactor.sh` precedent; deviate only with a stated reason) that performs the WHOLE sequence in a SINGLE `nix develop` invocation:
  (a) create an isolated venv and install the pinned tools into it (see Deliverable 2);
  (b) fresh `python -m build` in code/, capturing the log and the resulting dist/ listing;
  (c) `twine check --strict dist/*`;
  (d) `check-wheel-contents dist/*.whl`, plus a second run with `--ignore W002` (see below);
  (e) `pip download --no-deps model-checker==<REF> -d <tmp>` for the last published release, then diff the wheel RECORD/file listings and top-level directory sets new-vs-reference;
  (f) `sha256sum` of every produced artifact.
Requirements on the script: `<REF>` is a parameter with a sensible default (1.2.12 is the last published release today; the default must be overridable, not hardcoded at a call site); an `--out DIR` parameter selects where evidence is written; every step writes a NAMED evidence file rather than only streaming to the terminal, and the file names MIRROR the archived rehearsal's set (build.log, twine-check.txt, wheel-contents.txt, new-wheel-files.txt, ref-<version>-wheel-files.txt, wheel-files-diff.txt, top-level-dir-diff.txt, pip-download-<version>.log, sha256sums.txt, parity-diff.md) so a new run is diffable against an old one; the script writes nothing under code/ except code/dist/ (gitignored, .gitignore:13 `**/dist`) and nothing to flake.nix; steps (a) and (e) need network, so failing them must produce a clear, named error rather than a partial evidence set that reads as success.

DELIVERABLE 2 -- PIN THE TOOLS. A pinned manifest (preferred: `code/scripts/release-tools-requirements.txt`) giving exact `==` versions for build, twine, and check-wheel-contents, consumed by the runner's venv install. Comparable evidence across releases is the entire point; floating versions defeat it. Record in a comment why the pins are not in flake.nix.

DELIVERABLE 3 -- THE CHECKLIST PROSE. Rewrite RELEASE_SETUP.md's "Local Rehearsal (No Publish)" section so it drives off the runner: how to invoke it, what each evidence file contains, and what a reviewer should look at before tagging. That section currently points at `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` as a worked example -- keep it only as historical context, never as current evidence.

DELIVERABLE 4 -- THE READING GUIDE. Document the exit-code contract so a future reader is not misled into thinking the toolchain is broken. Specifically: which steps are hard gates (twine check --strict) versus informational (the parity diff, which is classified by a human and must not gate the release on byte-identity), and how to read a nonzero check-wheel-contents exit.

DELIVERABLE 5 -- RUN IT, DO NOT JUST WRITE IT. Execute the runner end to end on the current tree and report the produced evidence paths and each step's outcome. A script that has never been run is not a verified deliverable. Local builds do not perturb the working tree (code/dist is gitignored).

REUSE THE ESTABLISHED TECHNIQUE, DO NOT INVENT ONE. The archived release rehearsal under specs/archive/125_release_engineering_and_pypi_rehearsal/ already solved provisioning: an isolated venv created INSIDE `nix develop`, tools pip-installed there, flake.nix never modified. Its plan records the three constraints that make this non-obvious and that the runner must encode:
  - installing the tools system-wide fails on NixOS;
  - `PIP_USER=0` (or `--no-user`) is required because ~/.config/pip/pip.conf sets install.user=true globally on this host;
  - each `nix develop` invocation gets a fresh, non-persisting TMPDIR, so venv + build + check + diff MUST run in one invocation.

SCOPE BOUNDARIES. Do NOT add these tools to flake.nix's devShell -- the venv-inside-nix-develop approach exists precisely to avoid that, and widening the devShell is a separate decision with its own cost. Do NOT wire the runner into any CI workflow; whether check-wheel-contents becomes a CI gate is a separate decision. The runner is a local, on-demand release-verification tool.

EXPECT W002 TO FIRE, DO NOT FIX IT HERE. Running check-wheel-contents on the current tree exits 1 with `W002: Wheel contains duplicate files` for the four identical theory_lib/{bimodal,exclusion,imposition,logos}/VERSION files (independently verified twice; `--ignore W002` returns OK, exit 0). Deduplicating them has its own task. The runner must therefore treat a bare nonzero exit here as expected-and-recorded rather than aborting the remaining steps, and must run the `--ignore W002` variant as the "is there anything NEW?" signal. Both outcomes go in the evidence.

CORRECT A STALE CLAIM. The archived rehearsal recorded check-wheel-contents as clean/OK, which no longer reproduces; its recorded sha256sums are also invalid against the post-refactor tree. Neither RELEASE_SETUP.md nor the new prose may cite that evidence as current.

SEQUENCING. The release-rehearsal re-run task now depends on this one, and should consume the runner rather than open-coding the sequence.

---

### 155. Fix ci failures wheel dep and timing gated tests
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: None
- **Research**: [155_fix_ci_failures_wheel_dep_and_timing_gated_tests/reports/01_ci-failures-wheel-and-timing.md]
- **Plan**: [155_fix_ci_failures_wheel_dep_and_timing_gated_tests/plans/01_ci-fixes-wheel-and-timing.md]
- **Summary**: [155_fix_ci_failures_wheel_dep_and_timing_gated_tests/summaries/01_ci-fixes-summary.md]

**Description**: Fix the CI failures surfaced by the first live workflow run on 2026-08-12 (runs 31609253772, 31609253774, 31609253618). Every failure falls into one of two classes; NEITHER is a semantic defect. The substance is green: 2000-2002 passed on every job, matching the 2002 measured locally during the CI-gate work.

RELEASE-BLOCKING, FIX FIRST -- missing `wheel` breaks the publish pipeline. `.github/workflows/packaging.yml:27` installs `pytest build` and `.github/workflows/release.yml`'s `build` job installs `build twine`; neither installs `wheel`. The packaging contract suite invokes `python -m build --no-isolation`, which requires `wheel` importable in the ambient env, so it dies with `ERROR Missing dependencies: wheel` (observed: 2 passed, 116 errors, exit 1). packaging.yml already fails this way on every push. release.yml has NOT yet been exercised because 1.3.0 was never tagged, but its build job runs the same step and `publish-pypi` declares `needs: [build, publish-testpypi]` -- so tagging today burns the tag and never publishes. This step postdates v1.2.12, which is why the last release succeeded. Fix: add `wheel` to both install lists. Deterministic, not flaky; verify by re-running both workflows, not by reasoning about them.

CLASS 2 -- wall-clock assertions cannot survive contended CI runners. A DIFFERENT test failed on each Python version and 3.12 was spotless, which is the signature of contention rather than a version-specific defect:
  - 3.10: `bimodal/tests/integration/test_iterate.py::TestBimodalIteratorReal::test_iterate_two_produces_distinct_models` (Z3 returned unsat first model under load) and `tests/integration/test_performance.py::TestExecutionPerformance::test_complex_model_performance` (`Failed: Timeout (>30.0s) from pytest-timeout`)
  - 3.11: `src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetLoaderBehavior::test_performance_improvement` -- asserts initialization `< 0.01s`, measured `0.011432s`
  - 3.12: clean, 2002 passed
  - `nix flake check` on CI: same `test_performance_improvement` plus `builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::test_theory_library_execution` (`AssertionError: 'World Histories' not found in 'TIMEOUT: Model search exc...'`), 2 failed / 2000 passed

SPLIT THE REMEDY BY KIND -- do not apply one blanket fix:
  (a) Tests asserting SPEED (`test_performance_improvement`, `test_complex_model_performance`) assert something a shared 2-core runner cannot fairly measure. A 10ms assertion is not meaningful there. Mark them `@pytest.mark.performance` -- the marker is ALREADY registered at code/pyproject.toml:90 -- and deselect in CI with `-m "not packaging and not performance"`. Apply the SAME selector to BOTH `.github/workflows/tests.yml` AND `flake.nix`'s `checks.default`, or the two gates will disagree. Note `test_complex_model_performance`'s own docstring calls its 20s/30s budgets "hang guards, not performance budgets" with "3.3x headroom" -- CI contention ate the headroom; consider whether it belongs in (a) or (b).
  (b) Tests that merely RAN OUT OF TIME doing real work (`test_iterate_two_produces_distinct_models`, `test_theory_library_execution`) are correctness tests, not speed tests. RAISE the pytest-timeout budget for CI rather than deselecting them -- deselecting would silently drop genuine coverage. Prefer generous budgets over tight ones.

CLASS 3, PRE-EXISTING, LOWEST PRIORITY -- `.github/workflows/differential-tests.yml`: `oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` hits `Failed: Timeout (>300.0s) from pytest-timeout` (1 failed / 62 passed in 620s). This is NOT a regression from the CI-gate work -- the same workflow already failed on 2026-08-10 and 2026-07-18. Either raise its 300s budget or make that scan manual-only, consistent with how the exhaustive complexity-5 scan and TestBimodalHarnessIntegration are already deliberately manual-only. Do not let this block the release.

CONTEXT WORTH KNOWING: broadening `flake.nix`'s `checks.default` beyond bimodal is what pulled the class-2 tests into the flake gate. It passed locally on a quiet host (2002 passed / 0 failed) and could only fail where local verification structurally could not observe it -- CI. That is the gap being closed here, not a mistake in the broadening itself, which remains correct.

VERIFICATION MUST BE OBSERVED, NOT ASSERTED. The whole point of this task is that local green did not predict CI green. Local runs are necessary but NOT sufficient evidence here. The push that proves these fixes is user-only per .claude/rules/pr-prohibition.md, so implementation ends by reporting the fixes ready and naming exactly which workflow runs the user should check. Do not claim CI-green.

AGENT CONSTRAINT: per .claude/rules/pr-prohibition.md, do not push branches, do not open PRs, do not tag.

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

---

### 151. Rerun release rehearsal and publish to pypi
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 147, Task 149, Task 150, Task 156, Task 157
- **Research**: [151_rerun_release_rehearsal_and_publish_to_pypi/reports/01_release-rehearsal-rerun.md]
- **Plan**: [151_rerun_release_rehearsal_and_publish_to_pypi/plans/01_release-rehearsal-publish-prep.md]
- **Summary**: [151_rerun_release_rehearsal_and_publish_to_pypi/summaries/01_release-rehearsal-publish-prep-summary.md]

**Description**: Re-run the release rehearsal against the post-refactor tree and take the release to PyPI. Surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issues 1, 3, 17). This is the terminal task of the release sequence and should run only after the CLI defects, the documentation corrections, the CLI test suite, and the packaging-contract tests are done.

(1) THE EXISTING REHEARSAL EVIDENCE IS INVALID. The archived release rehearsal under specs/archive/125_release_engineering_and_pypi_rehearsal/ recorded wheel sha256 f85e6512... and sdist 255d2c01...; the current code/dist/ artifacts hash to 67be362c... and 02834d3c.... Roughly 22 commits have touched code/src since the CHANGELOG's 1.3.0 entry (2026-07-24), including the entire core/theory_lib boundary refactor. The checklist's pre-flight boxes are marked [x] but are no longer truthful -- and its own follow-on research anticipated exactly this, noting that any refactor invalidates the rehearsed evidence. Redo it: fresh `python -m build`, `twine check --strict dist/*`, `check-wheel-contents dist/*.whl`, a fresh wheel/sdist parity diff against the published 1.2.12, and re-recorded sha256sums. Reuse the archived rehearsal's structure and method notes -- it is a good template, only its data is stale.

(2) RESOLVE THE VERSION NUMBER AND THE CHANGELOG. All version sources currently agree on 1.3.0 (pyproject.toml:9, flake.nix:25 and :109, CHANGELOG, built artifacts; model_checker.__version__ is derived via importlib.metadata, so there is no second literal to drift). But 1.3.0 has NEVER been tagged -- the latest tag is v1.2.12 -- while code/CHANGELOG.md's `## [Unreleased]` sits empty despite those ~22 commits. Decide explicitly: either fold the post-refactor work into the 1.3.0 entry (defensible, since 1.3.0 was never published) or bump the version. Either way the CHANGELOG must stop understating what is being published. If bumping, update pyproject.toml AND both flake.nix sites.

(3) FRESH `nix flake check` ON A QUIET HOST. The archived checklist carries this caveat verbatim and it still stands: re-run it on a quiet or CI host immediately before tagging, to get a confirmation free of this host's shared-tenancy contention. A Z3 timing flake in test_bimodal.py::test_example_cases[BM_CM_1-example_case7] reproduces under CPU load.

(4) USER-ONLY BLOCKING GATE -- PyPI OIDC AND GITHUB ENVIRONMENTS. Every box in the archived checklist's one-time-setup section is unchecked: the PyPI trusted publisher for benbrastmckie/ModelChecker (workflow release.yml, environment pypi), the optional TestPyPI equivalent, and the `pypi`/`testpypi` GitHub Environments under Settings -> Environments. Pushing a tag before this is done runs the pipeline up to publish-pypi and FAILS there, after the test and build jobs have already burned. No agent can perform this -- it is PyPI and GitHub web-UI work. Surface it as an explicit gate the user must clear, and confirm it is cleared before any tag is pushed. No repository secrets are needed; Trusted Publishing uses the workflow's OIDC identity.

(5) POST-PUBLISH VERIFICATION, INCLUDING ON NIXOS. The review established that verifying a real published artifact on NixOS IS possible despite the "no pip on NixOS" guidance -- a venv install works; the only blocker is z3-solver's bundled libz3.so failing to resolve libstdc++.so.6. Working recipe:

    python3 -m venv testvenv
    PIP_USER=0 ./testvenv/bin/pip install model-checker
    LD_LIBRARY_PATH=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib \
      ./testvenv/bin/model-checker <project>/examples.py

After publishing, install FROM PyPI (not from local dist/) and run the full golden path: generate a project for each registered theory and execute it. The review ran exactly this against the local wheel and got 4/4 exit 0. Also confirm `pip index versions model-checker` shows the new release.

INCIDENTAL FINDING WORTH CONFIRMING, NOT ACTING ON: pip resolved z3-solver 5.0.0.0 -- a major version well beyond the `>=4.8.0` floor the project has ever tested -- and all four theories ran clean under it. No upper pin appears necessary. Re-confirm during verification; only add a constraint if something actually breaks.

AGENT CONSTRAINT: per .claude/rules/pr-prohibition.md and the archived checklist, every publish step is USER-ONLY -- `git push`, `git tag`, `/merge`, and any twine upload. Agents prepare, rehearse, verify, and report; the user executes. Do not invoke /tag.

---

### 150. Add general ci workflow and flake check gate
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: Task 147, Task 148, Task 149
- **Research**: [150_add_general_ci_workflow_and_flake_check_gate/reports/01_ci-workflow-and-flake-gate.md]
- **Plan**: [150_add_general_ci_workflow_and_flake_check_gate/plans/01_ci-workflow-and-flake-gate.md]
- **Summary**: [150_add_general_ci_workflow_and_flake_check_gate/summaries/01_ci-workflow-and-flake-gate-summary.md]

**Description**: Add continuous integration for the main test suites. Surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issue 7) and already an open Phase 1 item in specs/ROADMAP.md ("Add `nix flake check` as a CI gate job").

THE GAP: only two workflows exist. `.github/workflows/release.yml` is tag-triggered only (`v[0-9]+.[0-9]+.[0-9]+`). `.github/workflows/differential-tests.yml` is path-filtered to oracle/bimodal_logic/** and theory_lib/bimodal/**. So NOTHING runs code/tests/ or the in-package suite on ordinary pushes or pull requests. Regressions land silently and surface only at tag time, when the cost of finding them is highest -- which is precisely the situation the release rehearsal now finds itself in.

WHAT TO ADD: a push/PR workflow running (a) code/tests/ (283 tests, ~32s), (b) the in-package suite src/model_checker (1910 tests, ~7min serial), and (c) `nix flake check`. Both suites are currently GREEN -- the review measured 2193/2193 -- so this can be introduced as a hard gate immediately rather than as an advisory job.

IMPORTANT FINDING THAT CHANGES THE FLAKE SCOPING DECISION: flake.nix:107 scopes checks.default to the bimodal suite only, and justifies that narrowness with "the everything-else suite carries 28 documented pre-existing failures" (the 8-category breakdown recorded under specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/rest-suite-disposition.md). Those 28 failures DO NOT REPRODUCE on the current tree -- the boundary refactor resolved them, including the malformed "A[]" test-formula literal in code/tests/utils/helpers.py that Categories B/G were built around. Verify this independently, and if it holds: broaden checks.default beyond bimodal, update the now-false comment at flake.nix:107, and close the ROADMAP's "Follow-up task for the 28 documented 'everything-else' failures" item as resolved rather than triaging it. Do not propagate the 28-failure claim into new CI config.

CONSTRAINTS AND KNOWN HAZARDS:
- Use `-n 6`, not `-n auto`, for the bimodal suite: flake.nix documents a CPU-contention flake at -n auto, and the prior release work traced a Z3 timing flake in test_bimodal.py::test_example_cases[BM_CM_1-example_case7] to shared-tenancy contention. CI runners are contention-prone; budget accordingly and prefer generous timeouts over tight ones.
- Match the release matrix (3.10/3.11/3.12) or state deliberately why the PR gate runs a narrower matrix for speed.
- Decide the oracle differential suite's cadence while here -- ROADMAP has an open item on whether its slower tests (full complexity-5 scans, TestBimodalHarnessIntegration) warrant a scheduled/nightly job instead of blocking every matching push.
- Consider whether the packaging-contract tests belong in this workflow or a release-only one; if excluded here, say so explicitly rather than leaving it ambiguous.

SEQUENCING: depends on the CLI end-to-end suite so the new gate covers the CLI too rather than needing a second pass.

AGENT CONSTRAINT: per .claude/rules/pr-prohibition.md, do not push branches or open PRs. Author the workflow files and report ready.

---

### 149. Wheel and sdist packaging contract tests
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None
- **Research**: [149_wheel_and_sdist_packaging_contract_tests/reports/01_packaging-contract-tests.md]
- **Plan**: [149_wheel_and_sdist_packaging_contract_tests/plans/01_packaging-contract-tests.md]
- **Summary**: [149_wheel_and_sdist_packaging_contract_tests/summaries/01_packaging-contract-tests-summary.md]

**Description**: Add executable tests for the packaging contract. Surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issue 10).

THE PROBLEM: code/pyproject.toml:72 ([tool.setuptools.package-data]) and code/MANIFEST.in each carry long explanatory comments stating that the wheel allowlist and the sdist allowlist must stay in sync with each other and with theory_lib/docs/THEORY_ARCHITECTURE.md's Theory Contract -- and NOTHING enforces any of it. The comments are the only guard. Both files were deliberately written as explicit allowlists rather than blanket globs (a bare "*.md" sweeps in TODO.md, history/*.md, reports/*.md), which makes silent drift both easy and consequential.

No test in the suite touches wheel/sdist contents: grepping tests/ and src/model_checker/**/tests/ for wheel|sdist|bdist|MANIFEST|python -m build|twine returns only production-code hits and pip-install hint strings. The only artifact verification anywhere is in .github/workflows/release.yml -- and that is TAG-TRIGGERED ONLY, so it cannot catch drift until the moment of release, and even then it asserts nothing about CONTENTS (it runs `twine check --strict`, installs the wheel, imports it, and compares __version__ to the tag).

WHAT TO ASSERT (build the artifacts, then inspect them):
- EXCLUSIONS hold: no `oracle/` path (the oracle is a standalone top-level tree deliberately excluded from the wheel -- a Durable Decision in specs/ROADMAP.md); no TODO.md; no theory_lib/*/history/; no theory_lib/*/reports/; no theory_lib/*/examples_refactored/; no __pycache__/*.pyc.
- INCLUSIONS hold: each registered theory ships its VERSION, README.md, CITATION.md, LICENSE.md, the docs/*.md set, and notebooks/*.ipynb where present. Drive the theory list off the registry, not a literal.
- WHEEL/SDIST PARITY: the two allowlists agree on what ships. This is the specific invariant both files' comments assert and neither enforces.
- ENTRY POINT: the `model-checker` console script exists in the built wheel and runs from an installed venv. (Broader console-script behavior belongs to the CLI end-to-end suite; here the concern is specifically that the wheel DECLARES and INSTALLS it correctly.)

IMPLEMENTATION NOTES:
- The flake devShell has no `build`, `twine`, or `check-wheel-contents`. The prior release rehearsal handled this by creating an isolated venv INSIDE `nix develop`; reuse that technique. Each `nix develop` invocation gets a fresh non-persisting TMPDIR, so the build-and-inspect sequence must run in a single invocation.
- `PIP_USER=0` is required on any pip install: this host's ~/.config/pip/pip.conf sets install.user=true globally, which a venv rejects.
- These tests are necessarily slower than unit tests (they invoke a real build). Mark them so they can be selected/deselected, and ensure whatever CI job runs them actually does run them.
- code/build/ and code/dist/ currently hold stale local artifacts referenced by no test. Ensure the tests build fresh rather than inspecting whatever happens to be lying in dist/.

---

### 148. Cli end to end verification suite
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 146
- **Research**: [148_cli_end_to_end_verification_suite/reports/01_cli-e2e-verification-research.md]
- **Plan**: [148_cli_end_to_end_verification_suite/plans/01_cli-e2e-verification-plan.md]
- **Summary**: [148_cli_end_to_end_verification_suite/summaries/01_cli-e2e-verification-summary.md]

**Description**: Build real end-to-end verification for the CLI. This is the largest coverage gap found by the 2026-08-11 release review (specs/reviews/review-20260811.md, issues 4, 5, 6) and the main reason the CLI defects tracked separately went unnoticed.

THE GAP, PRECISELY:
- NOTHING in the test suite ever runs the `model-checker` console script. The one test that appears to (builder/tests/test_package_loading.py:244 TestSubprocessExecution::test_pythonpath_setup_in_subprocess) patches subprocess.run and then asserts against its own mock -- it exercises no production code at all. CI uses `python -m model_checker`, never the [project.scripts] entry point. Fix or delete that fake test as part of this work.
- `ParseFileFlags` (__main__.py:19) is never imported by any test. The only argument-level coverage is five error-path cases in tests/integration/test_error_handling.py:15-73, one of which (test_conflicting_flags, :69) is an empty `pass` stub.
- "Generate a project, then run it" -- the primary user journey -- is covered nowhere. test_issue_73_fix.py:82 explicitly patches input to 'n' to SKIP the execution branch; integration/test_generated_projects.py:88 documents that generated projects "cannot be loaded standalone". Several tests named like end-to-end coverage are not: tests/e2e/test_project_creation.py mostly uses tests/utils/helpers.py create_temp_project, which hand-writes a fake project and never calls BuildProject; tests/e2e/test_batch_output_real.py asserts only returncode==0 and nothing about batch output despite its name; builder/tests/e2e/test_full_pipeline.py:89 test_iteration_workflow passes `-i` believing it is an iteration flag (it is --print_impossible) and feeds unused stdin.
- An unused harness already exists and should be adopted rather than rebuilt: tests/utils/helpers.py:14 run_cli_command(), :138 assert_cli_success, :162 assert_cli_failure, and the cli_runner fixture at tests/conftest.py:166 -- no test requests any of them.

WHAT TO BUILD:
(a) CONSOLE-SCRIPT COVERAGE. Invoke the actual installed `model-checker` entry point as a subprocess, not just `python -m model_checker`. The console script is the single most user-visible artifact of the package and a break in it would ship undetected.
(b) ParseFileFlags UNIT TESTS. Cover parse(), the short/long mapping, and the flag-to-settings override path in settings/settings.py:215. Assert short and long forms are equivalent for EVERY registered flag -- this is the regression guard for the `-p` defect.
(c) FLAG COVERAGE. Currently zero of ~15 flags are exercised through the CLI. Cover --version, --help, --contingent/-c, --non_null/-n, --non_empty/-e, --disjoint/-d, --print_constraints/-p, --print_z3/-z, --print_impossible/-i, --align_vertically/-a, --maximize/-m (dispatches to comparison.run_comparison at __main__.py:309), --save/-s (assert files are actually produced), and --z3/--cvc5 dispatch including the cvc5-missing ImportError path at :283.
(d) GENERATE-THEN-EXECUTE, per registered theory. Generate a project via BuildProject and then RUN it through the console script, asserting exit 0 and no traceback. Drive this off the registry rather than a hardcoded theory list. The review verified this manually for all four theories (logos/exclusion/imposition/bimodal, 4/4 exit 0, output 1099/188/95/770 lines) -- this makes it automatic.
(e) Do NOT test --upgrade/-u by executing it: __main__.py:293 shells out to `pip install --upgrade model-checker`. Assert the constructed command instead.

NOTE ON A MISLEADING EXISTING FILE: builder/tests/integration/test_cli_interactive_integration.py drives BuildModule with an `interactive` flag that the CLI cannot produce (the real flag is --sequential/-q; settings/settings.py:247 lists `interactive` among no-op standard args). Reconcile it with the real flag surface or retire it.

SEQUENCING: depends on the CLI-defects work, because several behaviors under test are being corrected there and writing tests against the current broken behavior would encode the bugs.

BASELINE: the full suite is currently 2193/2193 green (283 top-level + 1910 in-package), so any red introduced here is genuinely new.

---

### 147. Correct stale release and environment docs
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None
- **Research**: [147_correct_stale_release_and_environment_docs/reports/01_release-env-docs-drift.md]
- **Plan**: [147_correct_stale_release_and_environment_docs/plans/01_release-env-docs-corrections.md]
- **Summary**: [147_correct_stale_release_and_environment_docs/summaries/01_release-env-docs-summary.md]

**Description**: Correct the release and environment documentation, which has drifted badly from the shipped pipeline. Surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issues 2, 14, 16). Issue 2 is rated CRITICAL because this is the documentation someone reads while performing the release; following it leads to a failed or wrongly-credentialed publish.

(1) `.github/workflows/README.md` -- DOCUMENTS A PROCESS THAT DOES NOT EXIST. The prior release-engineering work fixed release.yml and RELEASE_SETUP.md but never touched this third file. It still describes: `PYPI_API_TOKEN` repository secrets ("Name must be exactly: PYPI_API_TOKEN") which were deliberately removed in favour of OIDC Trusted Publishing; a Python 3.8/3.12 test matrix (actual, release.yml:25: 3.10/3.11/3.12); `cd Code` (wrong casing, previously fixed elsewhere); a manual `twine upload dist/*X.Y.Z*` flow; and `python code/run_update.py` described as the RECOMMENDED path -- a script that does not exist anywhere in the repository (`find . -name run_update.py` returns nothing). Decide between rewriting it to match the shipped five-job release.yml or deleting it and pointing at .github/RELEASE_SETUP.md. Deleting is defensible: a single accurate release doc beats two that must be kept in sync, and this file's entire content is now wrong.

(2) `.github/RELEASE_SETUP.md` -- BROKEN REFERENCES AND STALE MATRIX. Line 54 describes the test matrix as "Python 3.8 and 3.12"; release.yml:25 actually runs ['3.10','3.11','3.12']. Lines 77 and 146 point at `specs/125_release_engineering_and_pypi_rehearsal/`, which was archived and now lives under `specs/archive/`. Fix the matrix description and repoint both paths.

(3) `code/docs/development/ENVIRONMENT_SETUP.md` -- REFERENCES A NONEXISTENT FILE. Line 103 instructs `ls shell.nix .envrc  # Should exist for NixOS support`; there is no shell.nix in the repo (the flake replaced it; .envrc is `use flake`). Line 18 states "Python: 3.8 or higher" against pyproject's `requires-python = ">=3.10"`. Fix both.

(4) `docs/installation/BASIC_INSTALLATION.md` -- ADD THE NIXOS VERIFICATION RECIPE. The file currently says only "NixOS Users: Do not use pip installation" (line 9) and directs users to `nix develop`. That is correct guidance for development, but it leaves no way to verify a real published PyPI artifact on NixOS -- which is exactly what post-publish verification requires. The review established empirically that a venv install DOES work; the sole blocker is z3-solver's bundled libz3.so failing to resolve libstdc++.so.6 (`ldd` confirms `libstdc++.so.6 => not found`). Document the working recipe:

    python3 -m venv testvenv
    PIP_USER=0 ./testvenv/bin/pip install model-checker
    LD_LIBRARY_PATH=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib \
      ./testvenv/bin/model-checker <project>/examples.py

`PIP_USER=0` is required because this host's ~/.config/pip/pip.conf sets install.user=true globally, which a venv rejects. Frame this as a verification procedure, not as a recommended install path -- the `nix develop` guidance for ordinary use stays as-is.

SCOPE NOTE: documentation only. Do not modify release.yml or flake.nix here; if a doc/code disagreement is found where the CODE looks wrong, record it rather than fixing it here.

---

### 146. Fix cli defects found in release review
- **Status**: [COMPLETED]
- **Task Type**: python
- **Topic**: architecture
- **Dependencies**: None
- **Research**: [146_fix_cli_defects_found_in_release_review/reports/01_cli-defect-fixes.md]
- **Plan**: [146_fix_cli_defects_found_in_release_review/plans/01_fix-cli-defects.md]
- **Summary**: [146_fix_cli_defects_found_in_release_review/summaries/01_fix-cli-defects-summary.md]

**Description**: Fix the user-visible CLI defects surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issues 8, 9, 11, 12, 13, 15). These are small, independent, and should land in the published artifact rather than as a post-release follow-up. All line references are against code/src/model_checker/__main__.py unless noted.

(1) `-p` SILENTLY NO-OPS. `_short_to_long` at :202 maps c,d,e,l,m,n,q,s,i,v,u,z,a but omits `p`. settings/settings.py:215 only applies a flag override when the long name appears in `user_provided_flags` (derived from raw sys.argv), so `-p` never reaches the setting while `--print_constraints` works. Add the missing mapping. Then make the class of bug unrepresentable: derive the map from the parser's own registered actions rather than maintaining a hand-written literal, or add a test asserting every registered short option has a mapping entry. Note a second, narrower gap in the same function: only `len(arg)==2` tokens are considered, so clustered short flags (`-cn`) are not decomposed -- decide explicitly whether to fix or document this.

(2) `--load_theory` HELP IS STALE AND UNVALIDATED. :77 hardcodes `help='Load semantic theory: bimodal.'`. The registry reports four theories -- confirmed live via `registry.iter_theories()` returning ['bimodal','logos','exclusion','imposition'] -- so --help never tells users that logos, exclusion, and imposition exist. The argument also carries no `choices=`, so bad names fail late. Generate BOTH the help string and `choices` from the registry so neither can drift again. The registry is already the single source of truth per the ROADMAP's Durable Decisions entry, and BuildProject already defaults off `registry.get_registered()[0]` rather than a literal -- this is the last hardcoded theory name on the CLI surface.

(3) `--save jupyter` ACCEPTED THEN DISCARDED. `jupyter` is a valid argparse choice at :118, but output/config.py:64 `create_output_config` maps only 'markdown'/'md' and 'json'. `--save jupyter` therefore yields save_output=True with an empty formats list -- no output, no error. Either implement the format or remove it from `choices`. Separately, the help text's "No args = all formats" is inaccurate: bare `--save` produces markdown+json only. Correct the wording to match behavior.

(4) `--sequential`/`-q` ADVERTISED BUT RAISES. builder/module.py:139 `_initialize_output_management` raises NotImplementedError unconditionally, yet --help documents the flag as interactive per-model saving. Either hide the flag until implemented or fail with a clear user-facing message instead of a traceback. Do not leave a documented flag whose only behavior is an unhandled exception.

(5) DEAD `-j/--jupyter` PRE-CHECK. :252 scans sys.argv for -j/--jupyter and checks ipywidgets/matplotlib/networkx availability, but neither flag is registered on the parser, so argparse rejects the invocation first and the block is unreachable. Delete it, or register the flag if the dependency-hint behavior is wanted.

(6) `__pycache__` WARNING LEAKS TO USERS. builder/project.py prints `Warning: Skipped non-manifest item: __pycache__` on every project generation. Reproduced from an installed wheel during the review, so real users see it. Suppress __pycache__/*.pyc silently -- they are never manifest items and their presence is not a condition worth reporting.

CONSTRAINTS: no behavior change beyond these six items; do not refactor the parser wholesale. Each fix should be independently verifiable. Broad test coverage for these paths is the subject of the separate CLI end-to-end suite work, which depends on this -- but do not leave a fix here entirely unverified: add at least a minimal assertion per item.

CONTEXT: the CLI was verified working end to end during the review (installed wheel, four theories generated and executed, 4/4 exit 0), and the full suite is 2193/2193 green. These are polish defects on a working CLI, not breakage.
