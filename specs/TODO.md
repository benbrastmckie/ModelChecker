---
next_project_number: 152
---

# TODO

## Task Order

*Updated 2026-08-11. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 146,147,149 | -- | documentation, packaging, architecture |
| 2 | 148 | 146 | testing |
| 3 | 150,151 | 147,148,149 | packaging, architecture |

**Grouped by Topic** (indented = depends on parent):

### Documentation

147 [NOT STARTED] — Correct the release and environment documentation, which has drif

### Packaging

149 [NOT STARTED] — Add executable tests for the packaging contract. Surfaced by the 
  └─ 151 [NOT STARTED] — Re-run the release rehearsal against the post-refactor tree and t

### Architecture

146 [NOT STARTED] — Fix the user-visible CLI defects surfaced by the 2026-08-11 relea
150 [NOT STARTED] — Add continuous integration for the main test suites. Surfaced by 

### Testing

148 [NOT STARTED] — Build real end-to-end verification for the CLI. This is the large

## Tasks

### 151. Rerun release rehearsal and publish to pypi
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: Task 147, Task 148, Task 149

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
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: architecture
- **Dependencies**: Task 148

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: testing
- **Dependencies**: Task 146

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
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None

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
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Topic**: architecture
- **Dependencies**: None

**Description**: Fix the user-visible CLI defects surfaced by the 2026-08-11 release review (specs/reviews/review-20260811.md, issues 8, 9, 11, 12, 13, 15). These are small, independent, and should land in the published artifact rather than as a post-release follow-up. All line references are against code/src/model_checker/__main__.py unless noted.

(1) `-p` SILENTLY NO-OPS. `_short_to_long` at :202 maps c,d,e,l,m,n,q,s,i,v,u,z,a but omits `p`. settings/settings.py:215 only applies a flag override when the long name appears in `user_provided_flags` (derived from raw sys.argv), so `-p` never reaches the setting while `--print_constraints` works. Add the missing mapping. Then make the class of bug unrepresentable: derive the map from the parser's own registered actions rather than maintaining a hand-written literal, or add a test asserting every registered short option has a mapping entry. Note a second, narrower gap in the same function: only `len(arg)==2` tokens are considered, so clustered short flags (`-cn`) are not decomposed -- decide explicitly whether to fix or document this.

(2) `--load_theory` HELP IS STALE AND UNVALIDATED. :77 hardcodes `help='Load semantic theory: bimodal.'`. The registry reports four theories -- confirmed live via `registry.iter_theories()` returning ['bimodal','logos','exclusion','imposition'] -- so --help never tells users that logos, exclusion, and imposition exist. The argument also carries no `choices=`, so bad names fail late. Generate BOTH the help string and `choices` from the registry so neither can drift again. The registry is already the single source of truth per the ROADMAP's Durable Decisions entry, and BuildProject already defaults off `registry.get_registered()[0]` rather than a literal -- this is the last hardcoded theory name on the CLI surface.

(3) `--save jupyter` ACCEPTED THEN DISCARDED. `jupyter` is a valid argparse choice at :118, but output/config.py:64 `create_output_config` maps only 'markdown'/'md' and 'json'. `--save jupyter` therefore yields save_output=True with an empty formats list -- no output, no error. Either implement the format or remove it from `choices`. Separately, the help text's "No args = all formats" is inaccurate: bare `--save` produces markdown+json only. Correct the wording to match behavior.

(4) `--sequential`/`-q` ADVERTISED BUT RAISES. builder/module.py:139 `_initialize_output_management` raises NotImplementedError unconditionally, yet --help documents the flag as interactive per-model saving. Either hide the flag until implemented or fail with a clear user-facing message instead of a traceback. Do not leave a documented flag whose only behavior is an unhandled exception.

(5) DEAD `-j/--jupyter` PRE-CHECK. :252 scans sys.argv for -j/--jupyter and checks ipywidgets/matplotlib/networkx availability, but neither flag is registered on the parser, so argparse rejects the invocation first and the block is unreachable. Delete it, or register the flag if the dependency-hint behavior is wanted.

(6) `__pycache__` WARNING LEAKS TO USERS. builder/project.py prints `Warning: Skipped non-manifest item: __pycache__` on every project generation. Reproduced from an installed wheel during the review, so real users see it. Suppress __pycache__/*.pyc silently -- they are never manifest items and their presence is not a condition worth reporting.

CONSTRAINTS: no behavior change beyond these six items; do not refactor the parser wholesale. Each fix should be independently verifiable. Broad test coverage for these paths is the subject of the separate CLI end-to-end suite work, which depends on this -- but do not leave a fix here entirely unverified: add at least a minimal assertion per item.

CONTEXT: the CLI was verified working end to end during the review (installed wheel, four theories generated and executed, 4/4 exit 0), and the full suite is 2193/2193 green. These are polish defects on a working CLI, not breakage.
