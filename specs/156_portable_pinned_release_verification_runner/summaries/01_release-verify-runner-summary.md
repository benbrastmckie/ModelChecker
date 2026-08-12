# Implementation Summary: Portable, Pinned Release-Verification Runner

- **Task**: 156 - portable_pinned_release_verification_runner
- **Status**: [COMPLETED]
- **Started**: 2026-08-12T16:55:00Z
- **Completed**: 2026-08-12T17:30:00Z
- **Effort**: ~2.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_release-verify-runner.md, reports/01_portable-release-verification.md,
  `specs/156_portable_pinned_release_verification_runner/rehearsal/` (12 evidence files)
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Built a checked-in, pinned, portable local rehearsal of the PyPI release pipeline's build/check
steps: `code/scripts/release-tools-requirements.txt` (three exact-pinned tools) and
`code/scripts/release-verify.sh` (a single-`nix develop`-invocation runner emitting a 12-file
named evidence set). Rewrote `.github/RELEASE_SETUP.md`'s "Local Rehearsal (No Publish)" section
to drive off the runner with a reading guide and exit-code contract, added a `code/scripts/README.md`
entry, and executed the runner end to end on the current tree, archiving its evidence into the
task directory. All 5 plan phases closed `[COMPLETED]`.

## What Changed

- **New**: `code/scripts/release-tools-requirements.txt` — `build==1.5.0`, `twine==7.0.0`,
  `check-wheel-contents==0.6.3`, with a header explaining why the pins are exact and why they are
  not in `flake.nix`.
- **New**: `code/scripts/release-verify.sh` (executable) — implements steps (a) provisioning,
  (b) `python -m build`, (c) `twine check --strict`, (d1) bare `check-wheel-contents`
  (informational), (d2) `check-wheel-contents --ignore W002` (hard gate), (e1) reference `pip
  download`, (e2) wheel file listings, (e3) unified diffs, (f) sha256 hashes, and generated
  `parity-diff.md`. Single-invocation `nix develop` re-exec guard; `note()`/`fail()`/`setup_fail()`/
  `record_step()` helpers; a per-step `summary.txt` ledger.
- **Modified**: `.github/RELEASE_SETUP.md` — replaced only the `### Local Rehearsal (No Publish)`
  section body with runner-driven prose, an evidence-file table, a hard-gate/informational reading
  guide, the exit-code contract, W002 reading guidance, and a "historical context only" framing
  of the archived task 125 rehearsal.
- **Modified**: `code/scripts/README.md` — appended a `## release-verify.sh` section following the
  file's existing `### Usage` / `### Flags` / `### Output Files` convention.
- **New**: `specs/156_portable_pinned_release_verification_runner/rehearsal/` — the official
  archived evidence set from the Phase 5 end-to-end run (12 files).

## Decisions

- `--ref VALUE` is the sole form for the reference-version argument (no bare positional alias) —
  the plan permitted omitting the alias "if it does not complicate the parser," and keeping a
  single named form kept the parser simpler.
- `setup_fail()` was given an optional `label` parameter so provisioning failures are labeled
  `SETUP FAILED:` and reference-fetch failures are labeled `REFERENCE FETCH FAILED:`, matching the
  plan's Risks & Mitigations table, which named both labels distinctly.
- Wheel file listings use the venv's `python -m zipfile` module (not `unzip`), avoiding a
  dependency on a tool not guaranteed present in the devShell, per the plan's explicit guidance.
- Top-level directory diffs are computed by extracting both wheels (`python -m zipfile -e`) into
  `$TMPDIR` scratch directories and running `find . -maxdepth 2 -type d`, mirroring the archived
  rehearsal's apparent method and output shape exactly (confirmed by direct comparison of
  `top-level-dir-diff.txt` against the archived file).

## Plan Deviations

- None (implementation followed plan). The two additions noted above (the `setup_fail` label
  parameter, and choosing `--ref` as the sole flag form) were both explicitly anticipated by the
  plan's own text, not departures from it.

## Impacts

- A developer can now rehearse a PyPI release locally with one command
  (`bash code/scripts/release-verify.sh`) instead of manually re-deriving the venv-inside-`nix
  develop` provisioning recipe each time.
- `PUBLISH-CHECKLIST.md`'s pre-flight step (which still points at the stale archived rehearsal
  evidence) is not itself edited by this task — out of `file_scope` — but the new
  `.github/RELEASE_SETUP.md` section now gives a correct, runnable alternative and explicitly
  flags the archived evidence as non-current.
- `flake.nix` and `.github/workflows/` remain untouched, as required; the devShell is not widened.
- W002 (four identical `theory_lib/*/VERSION` files) is unaffected — this task records and
  continues past it, per its explicit Non-Goal. A separate, concurrently active task in this same
  repository (`157_dedupe_theory_lib_version_files_w002`) targets that fix independently.

## Follow-ups

- None required for this task's own completion. `PUBLISH-CHECKLIST.md`'s pre-flight cross-
  reference to the archived rehearsal could be updated to point at the new runner in a future,
  separately scoped task — left untouched here per the plan's narrow rewrite-scope decision.

## References

- `specs/156_portable_pinned_release_verification_runner/plans/01_release-verify-runner.md`
- `specs/156_portable_pinned_release_verification_runner/reports/01_portable-release-verification.md`
- `specs/156_portable_pinned_release_verification_runner/handoffs/phase-{1..5}-handoff-*.md`
- `code/scripts/release-verify.sh`
- `code/scripts/release-tools-requirements.txt`
- `.github/RELEASE_SETUP.md`
- `code/scripts/README.md`

---

## Phase 5 End-to-End Run: Evidence Report

**Command**: `bash code/scripts/release-verify.sh --out specs/156_portable_pinned_release_verification_runner/rehearsal/`
(default `--ref 1.2.12`)

**Exit code**: `0`

**Terminal summary (verbatim, final lines)**:
```
[release-verify] Evidence directory: /home/benjamin/Projects/ModelChecker/specs/156_portable_pinned_release_verification_runner/rehearsal
[release-verify] All hard-gate checks passed
```

**Evidence directory**: `specs/156_portable_pinned_release_verification_runner/rehearsal/`
(12 files, all non-empty; filenames match the archived task 125 rehearsal's 10 names with
`<version>` substituted, plus the two documented additions `wheel-contents-ignore-w002.txt` and
`summary.txt`).

### `summary.txt` (full contents, verbatim)

```
release-verify.sh run
started (UTC): 2026-08-12T17:04:17Z
REF=1.2.12
OUT_DIR=/home/benjamin/Projects/ModelChecker/specs/156_portable_pinned_release_verification_runner/rehearsal

Resolved pinned tool versions (from pip freeze):
build==1.5.0
check-wheel-contents==0.6.3
twine==7.0.0

a-provision              gate   exit=0    (versions recorded in summary.txt)
b-build                  gate   exit=0    build.log
c-twine                  gate   exit=0    twine-check.txt
d1-wheel-contents        info   exit=1    wheel-contents.txt
d2-wheel-contents-w002   gate   exit=0    wheel-contents-ignore-w002.txt
e1-reference-fetch       gate   exit=0    pip-download-1.2.12.log
e2-file-listings         info   exit=0    new-wheel-files.txt, ref-1.2.12-wheel-files.txt
e3-diffs                 info   exit=0    wheel-files-diff.txt, top-level-dir-diff.txt
f-hashes                 info   exit=0    sha256sums.txt
parity-diff              info   exit=0    parity-diff.md

FAILURES=0
```

The record-and-continue contract is demonstrated directly by this ledger: `d1-wheel-contents`
recorded a nonzero exit (`1`) classified `info`, and every step from `d2-wheel-contents-w002`
through `parity-diff` still ran afterward, with `FAILURES=0` at the end.

### Per-step outcomes (quoted from the produced evidence files)

**(a) Provisioning** — resolved pinned versions per `pip freeze`, quoted above:
`build==1.5.0`, `check-wheel-contents==0.6.3`, `twine==7.0.0`.

**(b) Build** (`build.log`, tail, verbatim):
```
Successfully built model_checker-1.3.0.tar.gz and model_checker-1.3.0-py3-none-any.whl

--- code/dist/ directory listing ---
total 2092
drwxr-xr-x 2 benjamin users    4096 Aug 12 10:04 .
drwxr-xr-x 9 benjamin users    4096 Aug 12 10:04 ..
-rw-r--r-- 1 benjamin users 1179419 Aug 12 10:04 model_checker-1.3.0-py3-none-any.whl
-rw-r--r-- 1 benjamin users  953624 Aug 12 10:04 model_checker-1.3.0.tar.gz
```

**(c) `twine check --strict`** (`twine-check.txt`, verbatim, ANSI codes stripped for readability):
```
Checking /home/benjamin/Projects/ModelChecker/code/dist/model_checker-1.3.0-py3-none-any.whl: PASSED
Checking /home/benjamin/Projects/ModelChecker/code/dist/model_checker-1.3.0.tar.gz: PASSED
```
Both artifacts **PASSED**.

**(d1) Bare `check-wheel-contents`** (`wheel-contents.txt`, verbatim, exit `1`):
```
/home/benjamin/Projects/ModelChecker/code/dist/model_checker-1.3.0-py3-none-any.whl: W002: Wheel contains duplicate files:
  model_checker/theory_lib/bimodal/VERSION
  model_checker/theory_lib/exclusion/VERSION
  model_checker/theory_lib/imposition/VERSION
  model_checker/theory_lib/logos/VERSION
```
Matches the expected, documented finding exactly (the four `theory_lib/*/VERSION` duplicates).

**(d2) `check-wheel-contents --ignore W002`** (`wheel-contents-ignore-w002.txt`, verbatim, exit `0`):
```
/home/benjamin/Projects/ModelChecker/code/dist/model_checker-1.3.0-py3-none-any.whl: OK
```
Clean — no findings beyond the known W002.

**(e1) Reference fetch** (`pip-download-1.2.12.log`, tail, verbatim):
```
Collecting model-checker==1.2.12
  Using cached model_checker-1.2.12-py3-none-any.whl.metadata (19 kB)
Using cached model_checker-1.2.12-py3-none-any.whl (1.2 MB)
Saved /tmp/nix-shell.AQMUvW/release-verify-ref-download/model_checker-1.2.12-py3-none-any.whl
Successfully downloaded model-checker
```

**(e2)/(e3) File listings and diffs**: `new-wheel-files.txt` has 478 lines; `ref-1.2.12-wheel-files.txt`
has 514 lines. `wheel-files-diff.txt` is 410 lines, dominated by the `model_checker-1.2.12.dist-info`
→ `model_checker-1.3.0.dist-info` rename and the new `model_checker/solver/` module (also visible
in `top-level-dir-diff.txt`, verbatim):
```
--- ref-dirs.txt
+++ new-dirs.txt
@@ -1,13 +1,14 @@
 .
 ./model_checker
-./model_checker-1.2.12.dist-info
-./model_checker-1.2.12.dist-info/licenses
+./model_checker-1.3.0.dist-info
+./model_checker-1.3.0.dist-info/licenses
 ./model_checker/builder
 ./model_checker/iterate
 ./model_checker/jupyter
 ./model_checker/models
 ./model_checker/output
 ./model_checker/settings
+./model_checker/solver
 ./model_checker/syntactic
 ./model_checker/theory_lib
 ./model_checker/utils
```
This matches the archived task 125 rehearsal's own observed shape (dist-info rename +
`solver/` addition), confirming the diff mechanism reproduces the expected comparison.

**(f) Hashes** (`sha256sums.txt`, verbatim, 3 lines):
```
e99750cab0d0073f0258864b1a3aa56c76d499ca71eb19fb940b43749fe22e3b  .../code/dist/model_checker-1.3.0-py3-none-any.whl
617acb704963513160a489349d60681ca6bbebfa78576f72459ae78c7b17dc98  .../code/dist/model_checker-1.3.0.tar.gz
cebe110c0a599c9ab962b7a4fd88686c3cff5c893099b05002117ef3fb7a6d4e  .../release-verify-ref-download/model_checker-1.2.12-py3-none-any.whl
```

**`parity-diff.md`**: generated with the run's `<REF>` (1.2.12), built version (1.3.0), UTC
timestamp, pinned tool versions, an Artifact Identity table with the three SHA256 values above, a
File Count Summary (514 reference files vs. 478 new-build files), and a Classified Differences
section that explicitly defers classification to a human reviewer rather than fabricating a
verdict. Its Conclusion states plainly: "This diff is evidentiary, not a release gate."

### `--ref` override confirmation

A separate short run with `--ref 1.2.10` (scratch directory, not archived) produced
`pip-download-1.2.10.log` and `ref-1.2.10-wheel-files.txt`, confirming the reference version is
not hardcoded at any call site.

### Working-tree integrity

`git status --porcelain` before and after the run showed no changes under `code/` (the build
output lands in gitignored `code/dist/`, which never appears in `git status`); `git diff
--name-only` across the entire implementation contains neither `flake.nix` nor any
`.github/workflows/` path.

### Note: one interim flake during Phase 3 testing, diagnosed and resolved

A single interim (pre-Phase-5, non-archived) test run hit a `FileNotFoundError` when a
concurrently active session in this same shared working tree touched `code/`/`code/dist/`
mid-run (confirmed via a concurrent `git status --porcelain` showing another task's file also
changing at that moment). An immediate retry with no code changes succeeded cleanly, and every
subsequent run — including the official archived Phase 5 run reported above — completed without
incident. This was an artifact of the multi-agent-shared checkout used during implementation, not
a defect in `release-verify.sh`.
