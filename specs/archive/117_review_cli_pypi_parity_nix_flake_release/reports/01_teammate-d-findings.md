# Horizons Findings: Task 117 (Stabilize CLI / PyPI parity / Nix flake / Release)

## Key Findings

### 1. The repo's identity has been deliberately forked out from under the "model-checker" brand, and the docs/owner haven't caught up

`code/pyproject.toml` no longer describes the package published on PyPI as `model-checker`
(currently v1.2.12, 172 published versions). It was rewritten in a prior task's commits
(`task 101 phase 1: overhaul pyproject.toml`, `task 104 phase 4: add thin bimodal-logic check
CLI`) to:

- `name = "bimodal-logic"`, `version = "0.1.0"` (never published)
- `description = "Z3-based bimodal logic oracle ... for the bimodal_harness."`
- A new `[project.entry-points."bimodal_harness.oracle_providers"]` table and a
  `bimodal-logic` console script, alongside the pre-existing `model-checker` one.

This is not an accident — it is the documented outcome of an accepted architecture decision
record (`specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md`,
status: ACCEPTED): *"The ModelChecker codebase is being refactored from a multi-theory
framework into a focused bimodal Z3 oracle (`bmlogic-oracle`) that implements the
`OracleProvider` protocol expected by BimodalHarness."* It defines a three-repo architecture
(BimodalLogic Lean spec → ModelChecker Z3 oracle → BimodalHarness soundness bridge) as
"fixed and non-negotiable for the refactor."

Consistent with that pivot, `code/src/model_checker/theory_lib/` now contains only `bimodal/`
and `logos/` — `exclusion/` and `imposition/` are gone from the tree (removed months earlier,
per git history, independent of the bimodal-oracle work). `flake.nix` at repo root already
exists and is scoped entirely to this new identity: description *"ModelChecker — Z3-based
bimodal logic oracle"*, and its devShell hard-depends on a **sibling, out-of-repo path**
(`../BimodalHarness/src`) that most contributors, CI runners, and NixOS testers will not have.

None of this is reflected in `README.md`, `code/README.md`, `docs/`, or `CLAUDE.md`, all of
which still describe ModelChecker as a general 4-theory framework (logos, exclusion,
imposition, bimodal) installable via `pip install model-checker`. `code/CHANGELOG.md` has no
entry for the pivot or the theory removals either.

### 2. The project owner's own contemporaneous framing contradicts current HEAD

`specs/116_draft_email_modelchecker_architecture/email-draft.md` (task 116, completed this
same week, current git-status shows it still modified/in-flight) is Ben's own outgoing
description of the project to a third party. It says: *"The version on
https://pypi.org/project/model-checker/ is in good shape, though the CLI I have on GitHub is
mid-refactor, so best to pip install if you wanted to test it"* and *"Right now that's four
theories and around twenty operators sharing one engine."*

This confirms two things directly from the owner:
- He considers the **published PyPI `model-checker` package** — not current GitHub HEAD — to
  be the thing worth showing off right now.
- He believes/expects a 4-theory framework, which the current tree does not have (2 of 4
  theory directories are gone, and the pivot ADR explicitly narrows scope further to a single
  bimodal oracle).

### 3. Task 117 as scoped is a landmine given (1) and (2)

"Audit discrepancies with the model-checker package on PyPI" and "prepare a top-quality
release to push to PyPI" both presuppose there is one continuous "the project" to diff and
ship. There are now **two divergent identities** living in one working tree and one
`pyproject.toml`: the general framework PyPI users already depend on, and a from-scratch
`bimodal-logic` oracle package for a private external consumer. Proceeding to "release to
PyPI" without resolving which identity is being released risks one of two bad outcomes:
- Shipping `bimodal-logic` 0.1.0 as new, unrequested noise under a name nobody asked for, or
- Someone "helpfully" reverting the package name back to `model-checker` for the release and
  accidentally publishing a version that has silently dropped exclusion/imposition and most of
  the general-framework surface — a breaking release to a package with real installed users
  (README's "star the repo / watch for releases" messaging implies an actual audience).

## Recommended Approach

1. **Do not let task 117 (or any agent) auto-resolve this by picking a `pyproject.toml` name
   and publishing.** This is a hard-to-reverse, outward-facing action (once on PyPI, always on
   PyPI, `--skip-existing` in `release.yml` notwithstanding) and the two candidate outcomes
   have materially different consequences for real users. Surface a single explicit question
   to Ben before any build/publish step: *"Is the general multi-theory `model-checker`
   framework still the thing you want stabilized and released, with the bimodal-oracle work
   living elsewhere (branch/subpackage/separate repo), or has the project permanently
   narrowed to the bimodal oracle, in which case README/docs/CLAUDE.md and the PyPI listing
   itself need to be rewritten to say so?"* His task-116 email suggests the former is his
   actual mental model right now.
2. Once that's answered, this session's most valuable output may not be "ship a release" but
   **"reconcile HEAD with the answer"**: either restore/branch the general-framework identity
   before touching `pyproject.toml`/CLI, or do the honest doc rewrite (root README, CLAUDE.md,
   CHANGELOG, theory_lib README) that retires the 4-theory framing.
3. Treat this decision as the first real entry in `specs/ROADMAP.md`, which is currently an
   empty template (`- [ ] (No items yet -- add roadmap items here)`). The ADR that drove this
   pivot is buried in `specs/archive/106_.../reports/04_architectural-decisions.md` — not
   discoverable to a future contributor (or future-Ben) without task archaeology. A stabilize
   task is a natural moment to seed the roadmap with durable, non-task-numbered strategic
   state instead of leaving it to be re-discovered from git log.

## Opportunities to Advance Adjacent Roadmap Items

- **Nix as a first-class release-testing path, not a side quest**: `flake.nix` already exists
  but only offers a `devShells.x86_64-linux.default`, no `packages` output, no `flake.lock`,
  and a hard dependency on a private sibling repo. If the general-framework identity survives,
  extend it with a `packages.default` (`buildPythonPackage` from `code/`) so `nix build`/`nix
  run` work standalone, add `flake.lock` and additional systems, and wire `nix flake check`
  into CI/`release.yml` — this turns "NixOS users can't easily test releases" into a
  continuously-verified guarantee rather than a manual `shell.nix` afterthought, benefiting
  every NixOS contributor, not just this task.
- **PyPI Trusted Publishing (OIDC)**: `release.yml` currently uploads via a long-lived
  `PYPI_API_TOKEN` secret + twine. Migrating to PyPI's Trusted Publisher (`pypa/gh-action-pypi-publish`
  with OIDC) removes secret-rotation risk and is a small, durable improvement independent of
  which package identity ships — worth bundling into this task's CI touch-up regardless of the
  identity question above.
- **CHANGELOG/documentation health**: whichever identity wins, `code/CHANGELOG.md` needs an
  honest entry — it currently reads as if the last major change was package-loading
  robustness work, with no trace of the theory removals or the oracle pivot. This is a
  low-cost, high-trust-signal fix to bundle with the release.
- **CI matrix as regression net for the identity decision**: `release.yml`'s existing
  ubuntu/macos/windows × Python 3.8/3.12 matrix is a good scaffold — extend it (or add a
  parallel `flake check` job) to also gate on "theory_lib still contains the theories the
  README promises" so a future refactor can't silently repeat this drift between docs and
  code.

## Evidence/Examples

- ADR: `specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md`
  ("bmlogic-oracle Clean-Break Refactor", Decision 1: "Three-Repo Architecture ... fixed and
  non-negotiable for the refactor").
- `code/pyproject.toml`: `name = "bimodal-logic"`, `version = "0.1.0"`, dual entry points
  (`model-checker` and `bimodal-logic`).
- `flake.nix`: description "ModelChecker — Z3-based bimodal logic oracle"; `BIMODAL_HARNESS_SRC_DEFAULT
  = "../BimodalHarness/src"`.
- `code/src/model_checker/theory_lib/`: only `bimodal/` and `logos/` present; no
  `exclusion/`, no `imposition/`.
- `specs/116_draft_email_modelchecker_architecture/email-draft.md`: owner's own July 2026
  description, still describing "four theories" and treating GitHub HEAD as "mid-refactor"
  relative to the PyPI release.
- `specs/ROADMAP.md`: empty template, no recorded strategic decisions.
- `pip index versions model-checker`: 1.2.12 latest of 172 published versions — confirms an
  active, versioned public package exists and is not the same thing as current HEAD.

## Confidence Level

High on the factual findings (pivot ADR, pyproject/flake contents, missing theory
directories, email contents, empty roadmap — all directly read from the repo). Medium on the
recommendation to treat this as a blocking go/no-go question rather than something task 117
can resolve unilaterally — that's a judgment call about risk tolerance for an outward-facing
PyPI action, but given the explicit git-workflow/PR-prohibition norms already in this repo's
`.claude/rules/` (outward-facing actions require confirmation), it's the safer default.
