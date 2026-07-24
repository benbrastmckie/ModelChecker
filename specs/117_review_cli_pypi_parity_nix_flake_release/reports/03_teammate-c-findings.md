# Critic Findings: Gaps in the Task 118-125 Restoration/Release Effort

**Task**: 117 - Review and stabilize the repo; verify CLI; audit PyPI parity; build a Nix flake
for NixOS testing; complete full testing; prepare a top-quality PyPI release.
**Role**: Critic (Teammate C) — identifying gaps, unvalidated assumptions, and blind spots in the
now-completed 118-125 work, cross-checked against the round-1 report's originally-identified
risks (`01_team-research.md`) to see what silently dropped.

## Key Findings

All findings below are things I verified directly in the current tree (branch
`task-117-restore-model-checker`), not inference from summaries. The common pattern across all
of them: **every verification 118-125 performed was a manual, local, one-off pytest/build/nix
run — nothing was re-derived from or checked against the actual CI/doc surface a real user or
release trigger would hit.** As a result, several concrete, mechanically-detectable defects
survived the entire 8-task decomposition untouched.

1. **The tag-triggered release pipeline is currently broken and would block the very publish
   task 125 rehearsed.** `.github/workflows/release.yml`'s `test-and-release` job matrix is
   `python-version: ['3.8', '3.12']`, but `code/pyproject.toml` declares
   `requires-python = ">=3.10"` (and classifiers list only 3.10/3.11/3.12). `pip install` of the
   built wheel on the Python 3.8 leg will refuse on `Requires-Python` metadata, and with
   `fail-fast: true` plus `build`/`publish-testpypi`/`publish-pypi` all gated on
   `needs: test-and-release`, this fails the entire release before a single artifact is
   published. Task 125 phases 1-3 touched this exact file (casing fix, OIDC migration,
   `RELEASE_SETUP.md` reconciliation) without catching it, and `PUBLISH-CHECKLIST.md`'s
   pre-flight section never asks the release-runner to inspect the workflow's Python matrix.

2. **A second GitHub Actions workflow, `.github/workflows/differential-tests.yml`, is stale and
   will fail on its next trigger.** It path-filters on `code/src/bimodal_logic/**` (a path that
   has never existed under `code/src/`) and `code/src/model_checker/theory_lib/bimodal/**` (which
   still exists, so the filter still fires), then runs pytest against
   `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py`. That
   file no longer exists there — task 118 phase 5 relocated it to
   `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (confirmed via
   `find`/`git show --stat`). No task in 118-125 touched this workflow. It is a live time bomb:
   the next commit that touches any `theory_lib/bimodal/**` file will trigger a CI run that
   errors on "file not found," and nothing in the "full testing" claims 118-125 make accounts for
   it, because all their verification was local `pytest ...` invocations, never `.github/workflows/*`.

3. **The CHANGELOG's 1.3.0 entry conflates this release with an unrelated, stale changeset and
   links to three files that don't exist.** `git show 42185381` (task 124 phase 5) shows the
   commit simply relabeled the pre-existing `## [Unreleased]` section header as
   `## [1.3.0] - 2026-07-24` and prepended an accurate "Framework Restoration" subsection — but
   left all the *prior* `[Unreleased]` content (an "Issue #73"/package-loading-refactor entry,
   unrelated to this restoration effort) folded into the same 1.3.0 release notes. That leftover
   content links to `docs/api/builder/loader.md`, `docs/guides/project_creation.md`, and
   `docs/migration/package_loading_v2.md` — none exist in the tree (verified via `ls`) — and its
   "Migration Optional"/"Performance Impact" sections describe a package-loading refactor, not
   the theory restoration, first-order removal, or oracle relocation this release is actually
   about. Anyone reading the CHANGELOG (or the GitHub Release notes, which link directly to it
   per `release.yml`'s `github-release` job) gets misleading provenance and three dead links —
   the opposite of "top-quality release."

4. **NixOS-facing install docs still point at the retired `shell.nix`, and the casing bug task
   125 fixed in `release.yml` is unfixed in seven install docs.** `docs/installation/
   BASIC_INSTALLATION.md`'s "NixOS Installation" section (line 159-173) and `README.md:36` both
   still say "use the provided `shell.nix`" and instruct `nix-shell` — but `code/shell.nix` was
   deleted in task 123 phase 4 ("Retire shell.nix, Commit flake.lock"; confirmed absent via
   `ls`). There is no root `shell.nix`, only `flake.nix` (`nix develop`/`nix build`). Following
   the current docs literally gives a NixOS user a missing-file error on the exact workflow the
   parent task asked to enable. Compounding this: the same `cd ModelChecker/Code` (capital `C`)
   directory-casing bug that task 125 phase 1 fixed in `release.yml` appears untouched in
   **seven** files — `docs/installation/BASIC_INSTALLATION.md`, `docs/installation/README.md`,
   `docs/installation/DEVELOPER_SETUP.md` (4 occurrences), `docs/installation/JUPYTER_SETUP.md`,
   `docs/installation/VIRTUAL_ENVIRONMENTS.md` — the actual directory is lowercase `code/`. Task
   124's "Documentation Refresh" summary describes touching root-level README/CLAUDE.md and
   package/scripts docs but never mentions `docs/installation/` at all; `BASIC_INSTALLATION.md`
   also still says "Python 3.8 or higher," contradicting `requires-python = ">=3.10"`.

5. **The Nix flake's `checks.default` — the only automated regression gate this whole effort
   produced — covers a small fraction of "full testing."** `flake.nix`'s `checks.default` runs
   exactly `src/model_checker/theory_lib/bimodal/tests` (by explicit, documented design in the
   flake's own comments). It never runs `logos`, `exclusion`, or `imposition` theory suites, the
   relocated `oracle/` suite, or the `code/tests/` integration/e2e tree. The 28 "everything-else"
   failures and the oracle suite's contention-flake/xfail behavior documented in
   `specs/122.../baselines/RELEASE-BASELINE.md` are recorded once, manually, in a spec artifact —
   they are not wired into any CI job or `nix flake check` target, so nothing will catch a future
   regression in those 1,880+2,716-286 tests automatically. Given the parent task's explicit ask
   to "complete full testing," the actual automated gate is materially narrower than that, and no
   118-125 artifact flags this narrowing as a residual gap (it's stated as a scope boundary, not
   a risk).

6. **The Nix flake cannot verify the PyPI `z3-solver>=4.8.0` dependency bound at all.**
   `flake.nix` uses `pythonRemoveDeps = [ "z3-solver" ]` (not a version relax) because the
   nixpkgs-native `python.pkgs.z3-solver` attribute has no PyPI-style dist-info to satisfy
   `pythonRuntimeDepsCheckHook` against. This is a reasonable mechanism, but its consequence is
   that `nix build`/`nix flake check` provide **zero** verification of the actual
   `z3-solver>=4.8.0` constraint declared in `pyproject.toml` — a NixOS user's `nix build` proves
   nothing about whether the code is compatible with real PyPI `z3-solver` wheels at all, only
   with whatever Z3 version nixpkgs happens to pin. No 118-125 artifact discusses this as a
   parity gap between the Nix path and the PyPI path (round 1's Teammate B flagged the
   "do NOT vendor PyPI's z3-solver wheel" decision but not this downstream verification-coverage
   loss).

7. **Round-1's identified risks that were silently dropped rather than resolved or explicitly
   deferred**: the round-1 synthesis (`01_team-research.md`) flagged `docs/usage/SEMANTICS.md`
   staleness and `code/scripts/README.md`'s link to a deleted
   `docs/theory/QUANTIFIER_SOLVERS.md` as "bounded follow-ups." Task 124 phase 4's own commit
   message says only "verify semantics usage doc needs no edits" — I did not independently
   re-verify this, but note it as a self-reported check, not a second-party confirmation, and the
   `scripts/README.md` link was not mentioned as checked anywhere in 118-125's commits or
   summaries I found (`git log --oneline | grep -i script` returns nothing from 118-125).

## Recommended Approach

Do not close task 117 on the strength of the local rehearsal evidence alone. Before treating the
release as ready:

1. **Fix `release.yml`'s Python matrix** to `['3.10', '3.12']` (or add `'3.11'` for real 3-way
   coverage) — this is the highest-severity item since it breaks the actual publish trigger, not
   just docs.
2. **Fix or retire `differential-tests.yml`** — update its path filters and pytest target to the
   relocated `oracle/bimodal_logic/tests/` location (and its `pip install -e code/` step, if the
   goal is still to test the in-package `bimodal` code against the standalone oracle), or delete
   it if the differential suite's CI coverage is meant to live elsewhere.
3. **Split or trim the CHANGELOG's 1.3.0 entry** — move the Issue #73/package-loading content to
   its own accurately-dated historical entry (or remove it if it was already covered by a prior
   real release) and drop the three dead documentation links, or restore the linked docs if they
   are still meant to exist.
4. **Update `docs/installation/` (all seven affected files) and `README.md:36`** to describe
   `nix develop`/`nix build` against `flake.nix` instead of the retired `shell.nix`, fix the
   `ModelChecker/Code` casing, and fix the `Python 3.8 or higher` claim to match
   `requires-python = ">=3.10"`. This is squarely inside the parent task's explicit "NixOS
   testing" and "top-quality release" asks and is currently unmet.
5. **Decide, explicitly, what "full testing" means for the release gate** — either widen
   `checks.default` (or add a second CI job) to run the full suite with the 28 known failures
   marked `xfail`/`skip` (matching the pattern already used for the oracle suite's 9 documented
   xfails), or explicitly document in the release checklist that CI only gates the bimodal
   subset and the rest is a manual, non-repeating verification. Leaving it implicit is the gap.
6. A cheap, valuable follow-up (not blocking): re-verify phase 4's semantics-doc "no edits
   needed" claim and the `scripts/README.md` `QUANTIFIER_SOLVERS.md` link independently, since
   both were carried forward from round 1 without a visible second check.

## Evidence/Examples

- `.github/workflows/release.yml:19` — `python-version: ['3.8', '3.12']` vs.
  `code/pyproject.toml:20` — `requires-python = ">=3.10"`.
- `.github/workflows/differential-tests.yml:4-9,22` — stale paths; confirmed via
  `find oracle -iname "*cross_oracle*"` (present) vs.
  `find code/src/model_checker/theory_lib/bimodal/tests -iname "*cross_oracle*"` (absent).
- `git show 42185381 -- code/CHANGELOG.md` — shows the `[Unreleased]` -> `[1.3.0]` relabel with
  old Issue #73 content retained underneath; dead links confirmed via `ls
  code/docs/api/builder/loader.md` etc. (all "No such file or directory").
- `docs/installation/BASIC_INSTALLATION.md:159-173`, `README.md:36` — `shell.nix`/`nix-shell`
  references; `ls code/shell.nix` -> "No such file or directory" (retired in task 123 phase 4,
  commit `3c79cf01`).
- `grep -n "ModelChecker/Code" README.md code/README.md docs/installation/*.md` — 8 hits across
  7 files, none touched by task 124.
- `flake.nix` — `checks.default` `checkPhase` runs only
  `pytest src/model_checker/theory_lib/bimodal/tests -n 6 -q`; comment block above it explicitly
  scopes out `oracle/` and "everything-else."
- `flake.nix` — `pythonRemoveDeps = [ "z3-solver" ]` (strips the requirement rather than
  relaxing its version bound).
- `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/RELEASE-BASELINE.md`
  and `rest-suite-disposition.md` — 28 documented, unfixed, ungated failures; the source of
  finding 5 above.

## Confidence Level

**High** for findings 1-4 and 6 — each was verified directly against file contents/paths in the
current tree, not inferred from summaries. **Medium** for finding 5 (the narrowness of the CI
gate is a legitimate scope question, but reasonable people could argue the manual
`RELEASE-BASELINE.md` snapshot is sufficient for a first restoration release). **Low-medium** for
finding 7 (I did not re-derive the semantics-doc/scripts-README claims myself, only noted the
absence of independent verification).
