---
next_project_number: 158
---

# TODO

## Task Order

*Updated 2026-08-12. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 151,152,156,157 | -- | packaging, semantics |
| 2 | 153 | 152 | semantics |
| 3 | 154 | 153 | semantics |

**Grouped by Topic** (indented = depends on parent):

### Packaging

151 [NOT STARTED] — Re-run the release rehearsal against the post-refactor tree and t
156 [NOT STARTED] — Document a portable check-wheel-contents recipe in .github/RELEAS
157 [NOT STARTED] — Deduplicate the four identical theory_lib VERSION files to clear 

### Semantics

152 [NOT STARTED] — AUDIT ONLY -- no semantics change, no constraint change, no examp
  └─ 153 [NOT STARTED] — Bring `BimodalSemantics`'s frame class up to the JPL paper's `def
    └─ 154 [NOT STARTED] — THE PAYOFF, and the one task in this group where OVER-CLAIMING is

## Tasks

### 157. Dedupe theory lib version files w002
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 155

**Description**: Deduplicate the four identical theory_lib VERSION files to clear check-wheel-contents W002. code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION are four byte-identical files each containing `1.0.0`. check-wheel-contents flags them as `W002: Wheel contains duplicate files` and exits 1 on the built wheel; `--ignore W002` returns OK with exit 0. Independently verified twice against code/dist/model_checker-1.3.0-py3-none-any.whl. The finding is structural (four identical files), not an artifact of a stale build, so it reproduces on a fresh build.

THIS IS PRE-EXISTING, NOT A REGRESSION. It is out of scope for the CI-failure fix work that surfaced it, which deliberately reports W002 without remediating it and explicitly forbids touching the VERSION files to silence the lint. Do not treat this as urgent or release-blocking: `--ignore W002` is a legitimate signal for release verification in the meantime.

A STALE CLAIM NEEDS CORRECTING TOO: the archived rehearsal under specs/archive/125_release_engineering_and_pypi_rehearsal/ recorded check-wheel-contents as clean/OK. That no longer reproduces, consistent with specs/TODO.md:161's note that the rehearsal evidence is stale.

DECIDE THE REMEDY DELIBERATELY, do not assume deletion is correct. Research first: establish what reads these per-theory VERSION files at runtime, whether the value is load-bearing anywhere (packaging metadata, theory-version reporting, tests), and whether per-theory versioning is an intended convention that simply is not yet exercised (all four sitting at 1.0.0 is consistent with BOTH "vestigial" and "intended but never bumped"). Only then choose among: remove them in favour of a single source of truth; keep them but exclude them from the wheel; or keep them and accept W002 permanently via a pinned --ignore. Any option that changes what ships in the wheel must be checked against the packaging contract suite under code/tests/packaging/.

VERIFY BY REBUILDING. The evidence is a fresh `python -m build` plus check-wheel-contents on the resulting wheel -- a plain run should reach exit 0 without needing --ignore W002 if the remedy was deduplication. Note code/dist is gitignored (.gitignore:13, **/dist), so a local build does not perturb the working tree.

---

### 156. Document portable check wheel contents recipe
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None

**Description**: Document a portable check-wheel-contents recipe in .github/RELEASE_SETUP.md. RELEASE_SETUP.md:147 names `python -m build`, `check-wheel-contents`, and `twine check --strict` as part of the release verification, but the repo provides no reproducible way to obtain them. flake.nix's devShells.default declares `packages = [ devPython ]`, and devPython carries only pytest, pytest-xdist, and pytest-timeout -- no build, no twine, no check-wheel-contents. Nothing in .github/ invokes the tool; the only reference is that prose line. Today the tool is only available because it happens to sit in one developer's nix profile (verified: /home/benjamin/.nix-profile/bin/check-wheel-contents, 0.6.3), and it is NOT resolvable from the flake-registry nixpkgs -- nixpkgs#check-wheel-contents, #checkWheelContents, #python3Packages.check-wheel-contents, and #python3Packages.checkWheelContents all fail to evaluate. That makes the documented release verification non-reproducible for anyone else, and unpinned (0.6.3 today, silent drift later) for evidence that is meant to be compared across releases.

REUSE THE ESTABLISHED TECHNIQUE, do not invent one. The archived release rehearsal under specs/archive/125_release_engineering_and_pypi_rehearsal/ already solved this: create an isolated venv INSIDE `nix develop` and pip install the tools there, never modifying flake.nix. Its plan records the two constraints that make this non-obvious -- installing the tools system-wide fails on NixOS, and each `nix develop` invocation gets a fresh non-persisting TMPDIR, so the whole build-and-inspect sequence must run in a SINGLE invocation. Both belong in the documented recipe.

PIN THE VERSIONS. The point of this task is comparable evidence across releases, so the recipe should pin check-wheel-contents (and build/twine) rather than floating.

SCOPE: documentation only. Do NOT add these tools to flake.nix's devShell -- the venv-inside-nix-develop approach exists precisely to avoid that, and widening the devShell is a separate decision with its own cost. Do NOT change any workflow to run check-wheel-contents in CI; that is also a separate decision.

EXPECT W002 TO FIRE. Running check-wheel-contents on the current tree exits 1 with `W002: Wheel contains duplicate files` for the four identical theory_lib/{bimodal,exclusion,imposition,logos}/VERSION files (independently verified twice; `--ignore W002` returns OK, exit 0). Do not fix that here -- it has its own task. The recipe should state the expected exit-1 and name --ignore W002 as the "is there anything new?" signal, so a future reader is not misled into thinking the toolchain is broken.

CORRECT A STALE CLAIM: the archived rehearsal recorded check-wheel-contents as clean/OK, which no longer reproduces. specs/TODO.md:161 already notes that rehearsal's evidence is stale; the recipe should not cite it as current evidence.

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 147, Task 149, Task 150

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
