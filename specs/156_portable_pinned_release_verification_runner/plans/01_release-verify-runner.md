# Implementation Plan: Portable, Pinned Release-Verification Runner

- **Task**: 156 - portable_pinned_release_verification_runner
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/156_portable_pinned_release_verification_runner/reports/01_portable-release-verification.md`
- **Artifacts**: plans/01_release-verify-runner.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

`.github/RELEASE_SETUP.md`'s "Local Rehearsal (No Publish)" section names a verification sequence
(`python -m build`, `twine check --strict`, `check-wheel-contents`, a parity diff against the last
published release) that no checked-in artifact implements and that no declared toolchain provides —
the tools exist today only in one developer's ambient nix profile, unpinned, and
`check-wheel-contents` is not resolvable from nixpkgs at all. This plan builds the missing
executable: a pinned tool manifest, a single-`nix develop`-invocation runner that emits an
11-file named evidence set mirroring the archived rehearsal's naming, rewritten checklist prose
that drives off the runner, a documented exit-code/reading guide, and an actual end-to-end run
whose evidence paths and per-step outcomes are reported. Definition of done: the runner has been
executed on the current tree, its evidence is on disk, and the prose describing it matches what
the run actually produced.

### Research Integration

Findings from `reports/01_portable-release-verification.md` that this plan encodes directly:

- **Provisioning technique is already solved; reuse, do not re-derive.** The archived task 125
  plan's Phase 4 and `code/tests/packaging/conftest.py`'s `packaging_toolchain` fixture
  independently arrived at the same recipe: `python -m venv` created *inside* `nix develop`,
  `pip install` with `PIP_USER=0`/`--no-user` (because `~/.config/pip/pip.conf` sets
  `install.user=true` globally on this NixOS host), all in one invocation because each
  `nix develop` gets a fresh, non-persisting `TMPDIR`.
- **Pinned versions are confirmed against PyPI**: `build==1.5.0`, `twine==7.0.0`,
  `check-wheel-contents==0.6.3`. `0.6.3` is also exactly the ambient version currently producing
  the observed W002 behavior, so pinning to it reproduces today's behavior rather than
  introducing day-one drift. All three are compatible with the devShell's Python 3.12.
- **`<REF>` default 1.2.12 is confirmed** as `model-checker`'s current PyPI `info.version`;
  `code/pyproject.toml` declares `1.3.0`, so the local build produces `model_checker-1.3.0-*` to
  diff against the `1.2.12` reference — the same comparison shape as the archived evidence.
- **Evidence file names are fixed by the archive** (10 files, verified present in
  `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/`): `build.log`,
  `twine-check.txt`, `wheel-contents.txt`, `new-wheel-files.txt`, `ref-<version>-wheel-files.txt`,
  `wheel-files-diff.txt`, `top-level-dir-diff.txt`, `pip-download-<version>.log`,
  `sha256sums.txt`, `parity-diff.md`. The `--ignore W002` variant has no archived precedent and
  needs a new name (`wheel-contents-ignore-w002.txt`).
- **Script conventions** come from `code/scripts/verify-refactor.sh`: `#!/usr/bin/env bash`,
  `set -uo pipefail` (deliberately not `-e` — accumulate failures, always run the whole
  sequence), `SCRIPT_DIR`/`REPO_ROOT` resolution + `cd`, a plain `for arg in "$@"` / `case`
  parser with no `getopts`, `note()`/`fail()` helpers with a `FAILURES` counter, and `exit 1` iff
  `FAILURES>0`. `--out DIR` is a genuinely new convention for this script family — no existing
  `code/scripts/` script takes a caller-supplied output directory.
- **`code/scripts/README.md`** documents scripts with a `## <script>` + `### Usage` +
  `### Flags` + `### Output Files` convention, but does not document `verify-refactor.sh` — a
  README entry is style-consistent and in `file_scope`, though not universal precedent.
- **The archived rehearsal evidence is stale**: its `check-wheel-contents` result (clean/OK) no
  longer reproduces and its sha256sums are invalid against the post-refactor tree. Neither the
  rewritten prose nor any new file may cite it as current.
- **Rewrite scope is narrow**: replace only the "Local Rehearsal (No Publish)" section
  (`.github/RELEASE_SETUP.md` lines 142-148). Leave "Test Release Workflow (Dry Run on GitHub)"
  and the `PUBLISH-CHECKLIST.md` cross-reference in "Ordered Release Steps" untouched — both
  cover unrelated, still-accurate ground.
- **`code/tests/packaging/test_parity.py` is a different comparison axis** (wheel vs. sdist of
  the same build) from the runner's parity diff (this build's wheel vs. the last published
  release's wheel). No duplication; do not fold one into the other.

### Prior Plan Reference

No prior plan for this task. The archived plan
`specs/archive/125_release_engineering_and_pypi_rehearsal/plans/01_release-engineering-pypi-rehearsal.md`
(Phase 4) is treated as reference context only: it supplies the three provisioning constraints and
the evidence-file naming, and calibrates effort (that phase was a one-off manual sequence; turning
it into a parameterized script is comparable work plus argument handling and error contracts). Its
phases are not copied.

### Roadmap Alignment

No `specs/ROADMAP.md` in this repository; no roadmap phases required (`roadmap_flag` not set).

## Goals & Non-Goals

**Goals**:

- A checked-in, parameterized, portable runner at `code/scripts/release-verify.sh` that executes
  the entire verification sequence in a **single** `nix develop` invocation and writes an 11-file
  named evidence set to a caller-selectable `--out DIR`.
- A pinned tool manifest at `code/scripts/release-tools-requirements.txt` with exact `==` pins and
  an in-file comment recording why the pins are not in `flake.nix`.
- A rewritten `.github/RELEASE_SETUP.md` "Local Rehearsal (No Publish)" section that drives off the
  runner and demotes the archived rehearsal evidence to historical context.
- A documented exit-code / reading guide distinguishing hard gates from informational steps, and
  explaining how to read a nonzero `check-wheel-contents` exit.
- An actual end-to-end execution of the runner on the current tree, with evidence paths and
  per-step outcomes reported.

**Non-Goals**:

- Adding `build`, `twine`, or `check-wheel-contents` to `flake.nix`'s devShell. The
  venv-inside-`nix develop` approach exists precisely to avoid that; widening the devShell is a
  separate decision with its own cost. **`flake.nix` is not touched by any phase of this plan.**
- Wiring the runner into any CI workflow. No file under `.github/workflows/` is modified.
- Fixing W002 (the four identical `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION`
  files). That deduplication has its own task. Here W002 is expected, recorded, and continued past.
- Making the parity diff a release gate. It is evidentiary and human-classified; byte-identity
  against a prior release is not a pass condition.
- Any push, tag, branch, or PR (per `.claude/rules/pr-prohibition.md`).
- Duplicating what `code/tests/packaging/` already covers (wheel/sdist internal parity, inclusion
  and exclusion assertions, console-script smoke).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Runner is invoked outside `nix develop`, or re-enters it per step, and `$TMPDIR` vanishes between steps — producing a truncated evidence set that reads as success | H | M | Phase 1 encodes a single guarded self-re-exec (`nix develop --command bash "$0" "$@"` under a `RELEASE_VERIFY_IN_SHELL` guard variable) so the entire sequence runs in exactly one invocation; the evidence directory is resolved to an absolute path *before* re-exec and is never under `$TMPDIR` |
| `PIP_USER`/`install.user=true` breaks the venv install on this host | H | H (certain without mitigation) | Export `PIP_USER=0` and pass `--no-user` explicitly; this is the documented, twice-independently-derived failure mode, not a speculative one |
| Network steps (venv tool install, `pip download` of the reference release) fail and leave a partial evidence set that looks complete | H | M | Distinct exit code 2 for "a required step could not run", a named `SETUP FAILED` / `REFERENCE FETCH FAILED` message, and a `summary.txt`-style per-step status ledger written even on failure so no missing file is silently interpreted as a pass |
| A nonzero `check-wheel-contents` exit aborts the run, or is later misread as "the toolchain is broken" | H | H | The bare run is classified informational: its exit code is recorded, never propagated as an abort; the `--ignore W002` companion run is the "is there anything NEW?" signal; Phase 4's reading guide states the expected nonzero exit explicitly |
| Rewritten prose re-cites the stale archived rehearsal evidence as current | M | M | Phase 4 task list requires a grep over the new section for `specs/archive/125_` and an explicit "historical context only, not current evidence" framing wherever it appears |
| Runner writes into the working tree outside `code/dist/` and perturbs git status | M | L | Phase 5 verifies with `git status --porcelain` before and after the run; only `code/dist/` (gitignored, `.gitignore:13` `**/dist`) and the `--out` directory may change |
| Pinned versions drift from what actually installs (e.g. a yanked release) | M | L | Phase 5's real run is what confirms the pins resolve; a pin that fails to install is a Phase 5 blocker, not a silent Phase 1 assumption |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: the runner is
built incrementally (scaffold -> build/check steps -> parity/hash steps), the prose documents the
finished contract, and the end-to-end run exercises everything.

---

### Phase 1: Pinned tool manifest and runner scaffold [COMPLETED]

- **Goal**: Land `code/scripts/release-tools-requirements.txt` with exact pins, and the runner's
  skeleton — shebang, header contract, argument parsing, single-invocation re-exec guard, evidence
  directory resolution, status-ledger helpers — with every downstream step present as a named,
  not-yet-implemented stub. Nothing here needs the network.

- **Tasks**:
  - [x] Create `code/scripts/release-tools-requirements.txt` with exactly three `==` pins:
        `build==1.5.0`, `twine==7.0.0`, `check-wheel-contents==0.6.3` (versions confirmed against
        PyPI in the research report).
  - [x] Add a header comment block to that manifest recording (a) why exact pins: evidence is meant
        to be COMPARED ACROSS RELEASES and floating versions defeat that; (b) why the pins are not
        in `flake.nix`: `check-wheel-contents` is not resolvable from nixpkgs
        (`nix eval --raw nixpkgs#check-wheel-contents.name` fails), and the venv-inside-`nix develop`
        approach deliberately avoids widening the devShell; (c) how to re-pin (query PyPI
        `info.version`, update all three together, re-run the runner).
  - [x] Create `code/scripts/release-verify.sh` with `#!/usr/bin/env bash` and `set -uo pipefail`
        (**not** `-e` — the sequence must always run to completion and report a consolidated
        result, matching `verify-refactor.sh`'s established posture).
  - [x] Write the header comment block in `verify-refactor.sh`'s style: purpose, the numbered step
        sequence (a)-(f), a `Usage:` line, the evidence-file table, and the exit-code contract
        (0 = all hard gates green; 1 = a hard gate failed; 2 = a required step could not run,
        e.g. provisioning or reference fetch).
  - [x] Add `SCRIPT_DIR`/`REPO_ROOT` resolution and `cd "$REPO_ROOT"`, copying the
        `verify-refactor.sh` three-line idiom verbatim.
  - [x] Implement argument parsing in the plain `while`/`case` style (no `getopts`, no external
        arg library): `--ref VERSION` (default `1.2.12`, overridable — must not be hardcoded at any
        call site), `--out DIR`, `--help`. Accept a bare positional `<REF>` as an alias for
        `--ref` only if it does not complicate the parser; otherwise document `--ref` as the sole
        form.
  - [x] Default `--out` to a timestamped directory under `/tmp` (e.g.
        `/tmp/release-verify-<UTC-timestamp>/`), consistent with `verify-refactor.sh`'s `/tmp`
        precedent. **It must never default to `$TMPDIR`**, which `nix develop` recreates per
        invocation. Resolve `--out` to an absolute path and `mkdir -p` it before any step runs.
  - [x] Implement the single-invocation guard: if `RELEASE_VERIFY_IN_SHELL` is unset, export it and
        `exec nix develop --command bash "$0" "$@"` exactly once from `$REPO_ROOT`, forwarding the
        already-absolutized `--out` and the resolved `--ref`; if it is set, proceed. Verify the
        guard cannot recurse.
  - [x] Implement `note()` / `fail()` / a `FAILURES` counter following `verify-refactor.sh`, plus a
        `setup_fail()` path that exits 2 with a named message, and a `record_step <name> <exit>
        <gate|info>` helper that appends to a per-step status ledger.
  - [x] Write the status ledger to `<out>/summary.txt` (name it explicitly in the header; it is a
        12th file beyond the archived 10 + the W002 variant) containing one line per step with step
        name, classification (hard gate / informational), exit code, and evidence filename — written
        incrementally so a crashed or network-failed run still leaves a ledger showing which steps
        never ran.
  - [x] Stub each of steps (a)-(f) as a named function that currently only calls `note()` and
        `record_step`, so the scaffold is runnable and the step order is reviewable before any
        heavy logic lands.
  - [x] Add `PIP_USER=0` export and `--no-user` intent to the header/comments now, so it cannot be
        forgotten in Phase 2.

- **Timing**: 1 hour

- **Depends on**: none

- **Verification Tier**: local

- **Scope Hypothesis**: This phase asserts (i) exactly 3 pinned tools in the manifest and (ii) that
  the runner's evidence set is 11 named files plus `summary.txt`. Confirm (i) by reading the
  manifest back and counting `==` lines; confirm (ii) by counting the filenames declared in the
  header table against the archived set
  (`ls specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` = 10) plus
  `wheel-contents-ignore-w002.txt`. If the archived listing differs from 10 at implementation time,
  the header table is what must change — the mirror requirement, not the number, is the contract.

- **Files to modify**:
  - `code/scripts/release-tools-requirements.txt` - new file; three `==` pins plus rationale comment
  - `code/scripts/release-verify.sh` - new file; header, arg parsing, re-exec guard, helpers, step stubs

- **Verification**:
  - `bash -n code/scripts/release-verify.sh` parses clean.
  - `bash code/scripts/release-verify.sh --help` prints usage, the evidence-file table, and the
    exit-code contract, and exits 0 without entering `nix develop`.
  - Running the scaffold with `--out <tmpdir>` creates the directory, writes `summary.txt` with one
    stub line per step, and exits 0.
  - `grep -c '==' code/scripts/release-tools-requirements.txt` reports 3 pin lines.
  - `git status --porcelain` shows only the two intended new files.
  - `chmod +x` applied to the runner (or invocation documented as `bash <path>`, matching
    `verify-refactor.sh`'s documented `bash code/scripts/verify-refactor.sh` usage).

---

### Phase 2: Provisioning, build, and the two check tools (steps a-d) [NOT STARTED]

- **Goal**: Implement the venv provisioning, the fresh build, `twine check --strict`, and both
  `check-wheel-contents` runs, each writing its named evidence file and recording its
  gate/informational classification.

- **Tasks**:
  - [ ] **Step (a) — provisioning**: `export PIP_USER=0`; `python -m venv "$TMPDIR/release-verify-venv"`;
        `"$VENV/bin/pip" install --no-user --disable-pip-version-check -r
        code/scripts/release-tools-requirements.txt`. On any failure call `setup_fail` with a named
        `SETUP FAILED: could not provision pinned release tools (network required)` message and
        exit 2 — never continue into steps that would emit partial, success-looking evidence.
  - [ ] Record the resolved tool versions (`pip freeze` filtered to the three tools) into
        `summary.txt` so the evidence self-identifies which pins produced it.
  - [ ] **Step (b) — build**: remove/ignore any stale `code/dist/` contents so the run is fresh, then
        run `python -m build` from `code/` using the venv's interpreter, capturing combined
        stdout/stderr to `<out>/build.log`, and append a `dist/` directory listing to that same log
        (matching the archived `build.log`, whose trailing listing was appended by the rehearsal's
        own capture logic, not by `build`). Classify as a **hard gate**.
  - [ ] Assert `code/dist/` now contains exactly one `*.whl` and one `*.tar.gz`, and capture their
        paths into shell variables used by every later step. A wrong count is a hard-gate failure
        with a named message.
  - [ ] **Step (c) — twine**: `"$VENV/bin/twine" check --strict code/dist/*` to
        `<out>/twine-check.txt`. Classify as a **hard gate** — this is the one step whose failure
        must block a release.
  - [ ] **Step (d1) — bare check-wheel-contents**: `"$VENV/bin/check-wheel-contents" <wheel>` to
        `<out>/wheel-contents.txt`. **Capture the exit code and continue.** A nonzero exit here is
        expected today (W002, four identical `theory_lib/*/VERSION` files) and MUST NOT abort the
        run or increment `FAILURES`. Classify as **informational**; record the exit code in
        `summary.txt` and append an explanatory trailer line to `wheel-contents.txt` naming W002 as
        the expected finding and pointing at the `--ignore W002` companion file.
  - [ ] **Step (d2) — W002-ignored run**: `"$VENV/bin/check-wheel-contents" --ignore W002 <wheel>`
        to `<out>/wheel-contents-ignore-w002.txt`. This is the "is there anything NEW?" signal:
        classify it as a **hard gate** (a nonzero exit here means a finding beyond the known,
        separately-tracked W002 duplication).
  - [ ] Ensure `set -uo pipefail` plus the accumulate-don't-abort posture actually holds for each
        captured command (use explicit `|| true` / `rc=$?` capture around each so a nonzero exit is
        recorded rather than swallowed or fatal).

- **Timing**: 1.25 hours

- **Depends on**: 1

- **Verification Tier**: local

- **Scope Hypothesis**: This phase asserts that the bare `check-wheel-contents` run exits nonzero
  with W002 on the current tree and that `--ignore W002` exits 0. Confirm at implementation time by
  reading the two produced evidence files and their recorded exit codes in `summary.txt` — do not
  assume. If the bare run unexpectedly exits 0 (e.g. W002 was fixed by the separate task in the
  interim), the runner's logic is unchanged (it records and continues either way); only the
  reading guide's example in Phase 4 needs to reflect the observed reality.

- **Files to modify**:
  - `code/scripts/release-verify.sh` - implement steps (a) through (d2)

- **Verification**:
  - `bash -n code/scripts/release-verify.sh` parses clean.
  - A real invocation reaches step (d2) and produces non-empty `build.log`, `twine-check.txt`,
    `wheel-contents.txt`, and `wheel-contents-ignore-w002.txt` in the `--out` directory.
  - `summary.txt` shows step (d1) with a recorded nonzero exit AND subsequent steps still executed —
    the record-and-continue requirement demonstrated, not merely asserted.
  - Simulating a provisioning failure (e.g. temporarily pointing at a nonexistent requirements
    path) exits 2 with the named `SETUP FAILED` message and does not produce a partial evidence set
    that reads as success.
  - `git status --porcelain` shows no change under `code/` other than the (gitignored) `code/dist/`
    and the intended edit to `release-verify.sh`.

---

### Phase 3: Reference fetch, parity diffs, hashes, and the parity report (steps e-f) [NOT STARTED]

- **Goal**: Implement the reference-release download, the wheel file-listing and top-level-directory
  parity diffs, the sha256 manifest, and the generated `parity-diff.md` — completing the 11-file
  evidence set.

- **Tasks**:
  - [ ] **Step (e1) — reference fetch**: `"$VENV/bin/pip" download --no-deps
        "model-checker==$REF" -d "$TMPDIR/ref-download"`, capturing output to
        `<out>/pip-download-<REF>.log`. On failure call the named
        `REFERENCE FETCH FAILED: could not download model-checker==<REF> (network required)` path
        and exit 2 — a missing reference must not silently degrade into a diff-free evidence set.
  - [ ] **Step (e2) — file listings**: write the sorted full file listing of the freshly built wheel
        to `<out>/new-wheel-files.txt` and of the reference wheel to
        `<out>/ref-<REF>-wheel-files.txt` (use `python -m zipfile -l` or `unzip -Z1` from the venv
        interpreter — do not depend on a tool absent from the devShell).
  - [ ] **Step (e3) — diffs**: unified `diff` of the two full listings to
        `<out>/wheel-files-diff.txt`, and of the two maxdepth-2 top-level directory sets to
        `<out>/top-level-dir-diff.txt`, mirroring the archived files' raw-`diff`-output format.
        Both classified **informational**: a nonempty diff between a 1.3.0 build and a 1.2.12
        release is expected and must never gate.
  - [ ] **Step (f) — hashes**: `sha256sum` the new wheel, the new sdist, and the reference wheel into
        `<out>/sha256sums.txt`, one `sha256  path` line each, matching the archived three-line shape.
  - [ ] **Generate `<out>/parity-diff.md`** following the archived report's structure: an Artifact
        Identity table (artifact / name / SHA256), a File Count Summary, a Classified Differences
        section, and a Conclusion. The generated version must (i) state that classification of the
        differences is a **human** step the reviewer performs, (ii) state explicitly that the diff
        is evidentiary and not a release gate, and (iii) carry the run's `<REF>`, the built version,
        the UTC timestamp, and the pinned tool versions. Do not fabricate a classification verdict
        the script cannot compute — leave the Classified Differences section as the raw grouping
        plus a reviewer prompt.
  - [ ] Finalize the exit logic: `exit 0` iff no hard gate failed; `exit 1` if any did; `exit 2` on
        a setup/network abort. Print a closing consolidated summary to the terminal naming the
        `--out` directory and each step's classification and outcome.
  - [ ] Confirm every one of the 11 evidence files plus `summary.txt` is written by a successful
        run, and that a missing file at the end is itself reported as a failure rather than passing
        unnoticed.

- **Timing**: 1.25 hours

- **Depends on**: 2

- **Verification Tier**: local

- **Scope Hypothesis**: This phase asserts the complete evidence set is the archived 10 names plus
  `wheel-contents-ignore-w002.txt` plus `summary.txt` = 12 files. Confirm by `ls -1 <out> | wc -l`
  after a successful run and by diffing that listing against
  `ls -1 specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` — the archived names
  must all appear (with `<version>` substituted), and the only additions must be the two named above.

- **Files to modify**:
  - `code/scripts/release-verify.sh` - implement steps (e1)-(e3), (f), `parity-diff.md` generation, final exit logic

- **Verification**:
  - `bash -n code/scripts/release-verify.sh` parses clean.
  - A full invocation produces all 12 files, each non-empty.
  - `ls -1 <out>` matches the archived rehearsal's filename set (with `<version>` substituted) plus
    exactly the two documented additions.
  - `--ref` with a different published version (e.g. an earlier 1.2.x) produces correspondingly
    renamed `ref-<version>-wheel-files.txt` and `pip-download-<version>.log`, proving the parameter
    is not hardcoded.
  - `sha256sums.txt` contains three lines.
  - `parity-diff.md` contains no claim the script cannot substantiate, and contains no citation of
    the archived rehearsal as current evidence.

---

### Phase 4: Checklist prose, reading guide, and scripts README entry [NOT STARTED]

- **Goal**: Rewrite `.github/RELEASE_SETUP.md`'s "Local Rehearsal (No Publish)" section to drive off
  the runner, document the exit-code / reading contract, and add a `code/scripts/README.md` entry.
  Prose and markdown only — no script logic changes.

- **Tasks**:
  - [ ] Replace the body of `.github/RELEASE_SETUP.md`'s `### Local Rehearsal (No Publish)` section
        (currently at line 142, body lines 144-148) with runner-driven content: the exact invocation
        (`bash code/scripts/release-verify.sh [--ref VERSION] [--out DIR]`), the note that it
        re-enters `nix develop` itself and needs network for provisioning and the reference fetch,
        and a table of the 11 evidence files with one line each on what the file contains.
  - [ ] Add the **reading guide** to that section: which steps are **hard gates** —
        provisioning, `python -m build`, `twine check --strict`, and the `--ignore W002`
        `check-wheel-contents` run — versus **informational** — the bare `check-wheel-contents`
        run and the parity diff, which is classified by a human and must not gate the release on
        byte-identity against a prior release.
  - [ ] Document the exit-code contract explicitly: `0` = all hard gates green; `1` = a hard gate
        failed; `2` = a required step could not run (provisioning or reference fetch), so the
        evidence set is incomplete and must not be read as a pass.
  - [ ] Document **how to read a nonzero `check-wheel-contents` exit**: it is expected on the
        current tree, it reports `W002: Wheel contains duplicate files` for the four identical
        `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files, deduplication is tracked
        separately, and the `--ignore W002` companion file is the signal that answers "is there
        anything NEW?". State plainly that a nonzero exit here does not mean the toolchain is broken.
  - [ ] Add a short pointer to `code/scripts/release-tools-requirements.txt` explaining that the
        tools are pinned so evidence is comparable across releases, and that they are deliberately
        not in `flake.nix`.
  - [ ] Demote the archived rehearsal: keep at most one sentence pointing at
        `specs/archive/125_release_engineering_and_pypi_rehearsal/rehearsal/` as **historical
        context**, explicitly noting its `check-wheel-contents` result and sha256sums no longer
        reproduce against the current tree. Never present it as current evidence.
  - [ ] Leave the `### Test Release Workflow (Dry Run on GitHub)` section and the
        `PUBLISH-CHECKLIST.md` cross-reference in "Ordered Release Steps" untouched.
  - [ ] Append a `## release-verify.sh` section to `code/scripts/README.md` following that file's
        existing `## <script>` + `### Usage` + `### Flags` + `### Output Files` convention.
  - [ ] Verify every path referenced by the new prose exists on disk (the `prose` tier's named
        blind spot is broken cross-references — check them, do not assume).

- **Timing**: 1 hour

- **Depends on**: 3

- **Verification Tier**: prose

- **Scope Hypothesis**: This phase asserts the `.github/RELEASE_SETUP.md` edit is confined to the
  single `### Local Rehearsal (No Publish)` section. Confirm with `git diff --stat` plus a read of
  the diff hunk boundaries: the hunk must begin at or after the `### Local Rehearsal (No Publish)`
  heading and end at or before the following `### Test Release Workflow` heading. Any hunk outside
  that range is out of scope and must be reverted.

- **Files to modify**:
  - `.github/RELEASE_SETUP.md` - rewrite only the "Local Rehearsal (No Publish)" section
  - `code/scripts/README.md` - append a `## release-verify.sh` section

- **Verification**:
  - `git diff .github/RELEASE_SETUP.md` touches only the Local Rehearsal section.
  - The new section names all 11 evidence files, and each name matches a filename the runner
    actually writes (cross-check against the Phase 3 evidence listing, not against this plan).
  - The new section states the three exit codes and the W002 reading guidance.
  - `grep -n 'specs/archive/125' .github/RELEASE_SETUP.md` shows the archived reference framed as
    historical only — no sentence presents it as current, reviewable evidence.
  - Every filesystem path cited in the new prose resolves (`test -e` each).
  - `code/scripts/README.md` renders with the new section following the established heading pattern.

---

### Phase 5: End-to-end run and evidence report [NOT STARTED]

- **Goal**: Actually execute `code/scripts/release-verify.sh` end to end on the current tree,
  archive the evidence, and report the produced paths and each step's outcome. A script that has
  never been run is not a verified deliverable.

- **Tasks**:
  - [ ] Record `git status --porcelain` before the run as a baseline.
  - [ ] Run the full command with evidence archived into the task directory:
        `bash code/scripts/release-verify.sh --out specs/156_portable_pinned_release_verification_runner/rehearsal/`
        (task-artifact space, mirroring the archived task 125 `rehearsal/` precedent; this is
        artifact output, not a deliverable-file-scope change). Use the default `--ref 1.2.12`.
  - [ ] Capture the runner's own terminal summary and its exit code verbatim.
  - [ ] Verify all 12 files exist in the output directory and none is empty.
  - [ ] Read each evidence file and record its per-step outcome: build success and artifact names,
        `twine check --strict` PASSED/FAILED per artifact, the bare `check-wheel-contents` exit code
        and finding, the `--ignore W002` exit code, the reference download result, the two diffs'
        shape, and the three sha256 values.
  - [ ] Confirm the record-and-continue contract held in practice: the bare `check-wheel-contents`
        step's nonzero exit is present in `summary.txt` AND every subsequent step ran.
  - [ ] Confirm `git status --porcelain` after the run shows no change under `code/` beyond the
        gitignored `code/dist/`, and no change to `flake.nix` or any `.github/workflows/` file.
  - [ ] Exercise the `--ref` override once against a different published version to prove the
        default is overridable and the reference-named files rename accordingly (a short
        confirmation run; full evidence need not be archived for this variant).
  - [ ] If the run reveals any inaccuracy in the Phase 4 prose (a filename, an exit code, a
        described behavior), correct the prose — the documentation must describe what the runner
        actually did, not what it was planned to do. Scope any such correction to the same two
        documentation files.
  - [ ] Report the evidence directory path, each file's path, and each step's outcome in the
        implementation summary.

- **Timing**: 1 hour

- **Depends on**: 4

- **Verification Tier**: full

- **Commit Mode**: per-substep

- **Files to modify**:
  - `specs/156_portable_pinned_release_verification_runner/rehearsal/*` - generated evidence (new)
  - `.github/RELEASE_SETUP.md` - only if the run reveals a documentation inaccuracy
  - `code/scripts/README.md` - only if the run reveals a documentation inaccuracy

- **Verification**:
  - The runner completed and its exit code is recorded and explained against the documented
    contract (0/1/2).
  - All 12 evidence files exist, are non-empty, and their names match the documented set.
  - `summary.txt` shows every step attempted, with each classification and exit code.
  - The bare `check-wheel-contents` nonzero exit is recorded and the run continued past it.
  - `git status --porcelain` confirms no unintended working-tree changes; `flake.nix` and
    `.github/workflows/` are untouched (`git diff --name-only` contains neither).
  - The reported per-step outcomes are quoted from the evidence files, not paraphrased from
    expectation.

---

## Testing & Validation

- [ ] `bash -n` clean on `code/scripts/release-verify.sh` after every phase that edits it.
- [ ] `bash code/scripts/release-verify.sh --help` prints usage, evidence-file table, and exit
      codes without entering `nix develop`.
- [ ] A complete run exits with a code matching the documented contract and writes all 12 evidence
      files, each non-empty.
- [ ] The evidence filename set matches the archived rehearsal's 10 names (with `<version>`
      substituted) plus `wheel-contents-ignore-w002.txt` and `summary.txt`.
- [ ] The bare `check-wheel-contents` step's nonzero exit is recorded and the run continues —
      demonstrated in `summary.txt`, not asserted in prose.
- [ ] `--ref` override changes the reference-named files, proving no hardcoded call site.
- [ ] A simulated provisioning failure exits 2 with a named message and leaves no
      success-looking partial evidence set.
- [ ] `git diff --name-only` after all phases lists only: `.github/RELEASE_SETUP.md`,
      `code/scripts/release-verify.sh`, `code/scripts/release-tools-requirements.txt`,
      `code/scripts/README.md`, and files under
      `specs/156_portable_pinned_release_verification_runner/`.
- [ ] `flake.nix` is unmodified. No file under `.github/workflows/` is modified.
- [ ] No push, tag, branch, or PR is created (`.claude/rules/pr-prohibition.md`).

## Artifacts & Outputs

- `code/scripts/release-verify.sh` - the runner (new, executable)
- `code/scripts/release-tools-requirements.txt` - pinned tool manifest (new)
- `.github/RELEASE_SETUP.md` - rewritten "Local Rehearsal (No Publish)" section with reading guide
- `code/scripts/README.md` - new `## release-verify.sh` section
- `specs/156_portable_pinned_release_verification_runner/rehearsal/` - the Phase 5 run's 12
  evidence files
- `specs/156_portable_pinned_release_verification_runner/summaries/01_release-verify-runner-summary.md`
  - implementation summary reporting evidence paths and per-step outcomes

## Rollback/Contingency

- The two new files (`release-verify.sh`, `release-tools-requirements.txt`) are additive — deleting
  them reverts the runner entirely with no other effect.
- The two documentation edits are confined to one section each; `git checkout` of those two paths
  restores the prior prose (which points at the archived rehearsal).
- `code/dist/` is gitignored (`.gitignore:13` `**/dist`), so builds never perturb tracked state; the
  evidence directory is outside the package tree and can be deleted freely.
- If a pinned version turns out not to install (yanked release, resolver conflict), the contingency
  is to re-pin all three tools together from current PyPI `info.version` values and re-run — not to
  float the pins, which would defeat the cross-release comparability the manifest exists for.
- If W002 is fixed by the separate deduplication task before this lands, no runner logic changes:
  the bare run simply records exit 0. Only the reading guide's worked example needs updating.
- `flake.nix` is never modified by this plan, so no devShell rollback is possible or needed.
