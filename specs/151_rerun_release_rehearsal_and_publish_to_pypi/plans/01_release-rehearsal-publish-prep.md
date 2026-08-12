# Implementation Plan: Re-run the release rehearsal and prepare the PyPI publish

- **Task**: 151 - rerun_release_rehearsal_and_publish_to_pypi
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: 147, 149, 150, 155, 156, 157 (all `[COMPLETED]`)
- **Research Inputs**: `specs/151_rerun_release_rehearsal_and_publish_to_pypi/reports/01_release-rehearsal-rerun.md`
- **Artifacts**: plans/01_release-rehearsal-publish-prep.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, pr-prohibition.md
- **Type**: python
- **Lean Intent**: false

## Overview

The release sequence's terminal task. All prior release work has landed, but the newest
rehearsal evidence went stale again (task 157's `VERSION`-file dedupe invalidated task 156's
archived run), and `code/scripts/release-verify.sh` still hard-codes the now-false expectation
that bare `check-wheel-contents` fails with W002. This plan corrects that gate contract and its
documentation, resolves the version/CHANGELOG question by folding post-refactor work into the
never-published `1.3.0` entry, captures a genuinely fresh rehearsal evidence set, obtains a
quiet-host `nix flake check` confirmation, and hands the user a task-scoped publish checklist.

Definition of done: a fresh `release-verify.sh` evidence set archived under
`specs/151_.../rehearsal/` with all hard gates green; a CHANGELOG that no longer understates what
is being published; a quiet-host `nix flake check` verdict recorded (pass, or an explicit
regression finding that blocks the release); and a `PUBLISH-CHECKLIST.md` whose first item is the
user-only PyPI trusted-publisher gate.

**Hard constraint carried into every phase**: `git push`, `git tag`, `twine upload`, `gh pr
create`, `/merge`, and `/tag` are USER-ONLY. No phase of this plan performs any of them. Agents
prepare, rehearse, verify, and report; the user executes the publish.

### Research Integration

Findings integrated from `reports/01_release-rehearsal-rerun.md`:

- The runner (`code/scripts/release-verify.sh`, built by task 156) **supersedes** the archived
  by-hand rehearsal sequence — implementation invokes it rather than re-deriving steps.
- The d1/d2 W002 defect is fully diagnosed with line anchors (comments at 15-16 and 52-57; step
  bodies at ~296-341) and independently re-confirmed: a fresh from-scratch build now yields
  `check-wheel-contents dist/*.whl` exit 0 with no `--ignore`.
- Task 156's own archived rehearsal evidence is itself stale (its `wheel-contents.txt` still
  records the W002 finding) — it must not be reused.
- Version state is clean and agrees on `1.3.0` across `pyproject.toml:9`, `flake.nix:25`,
  `flake.nix:137`, and the CHANGELOG; no `v1.3.0` tag exists; PyPI's live latest is `1.2.12`.
  64 commits touched `code/src` since the `## [1.3.0]` entry was written. Research recommends
  Option A (fold into 1.3.0, no bump) — adopted by this plan.
- GitHub `pypi`/`testpypi` Environments now exist (confirmed read-only via `gh api`); the PyPI
  **trusted-publisher** registration remains unconfirmable without web-UI access and is the
  live half of the blocking gate.
- Today's `nix flake check` failed on `test_iteration_via_iterate_api` under load average 4.84
  with 4 concurrent agent sessions — plausibly a second contention-sensitive Z3-timing flake
  (prior evidence shows 31.59-64.34s wall-clock against a 30s budget on this host), but
  unproven and requiring a quiet-host re-run.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Correct `release-verify.sh`'s d1/d2 gate assignment so bare `check-wheel-contents` is the hard
  gate and the stale W002 narrative is removed from code and docs.
- Resolve the version/CHANGELOG question explicitly: fold into `1.3.0`, expand the entry to
  cover the refactor, W002 fix, CI fixes, and release tooling.
- Produce a fresh, officially-archived rehearsal evidence set under
  `specs/151_.../rehearsal/` that reflects the current tree.
- Obtain a quiet-host `nix flake check` verdict, and characterize the
  `test_iteration_via_iterate_api` failure as flake or regression.
- Hand the user a task-scoped `PUBLISH-CHECKLIST.md` with the PyPI trusted-publisher gate as an
  explicit, first, blocking item, and a copy-paste post-publish verification runbook including
  the NixOS `LD_LIBRARY_PATH` recipe.

**Non-Goals**:
- Tagging, pushing, publishing, or uploading anything. All user-only.
- Registering the PyPI trusted publisher or altering GitHub Environments — web-UI work outside
  agent reach.
- Executing the post-publish verification (requires a published `1.3.0` artifact that does not
  yet exist); it is written as a runbook and deferred.
- Bumping the version number (Option B is explicitly rejected; see Overview).
- Adding a `z3-solver` upper pin — the incidental `5.0.0.0` finding is confirmed, not acted on,
  unless the post-publish run actually breaks.
- Rewriting the archived task-125 checklist in place; it is a structural template only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A third rehearsal goes stale if commits land on `code/src` between this task and the user's tag push | M | M | The checklist instructs a final `release-verify.sh` re-run immediately before tagging; the evidence set is explicitly not one-and-done |
| A quiet host cannot be obtained on this shared multi-agent machine | H | M | Phase 5 checks `uptime`/`ps aux` before running and records the contention state as part of the verdict; fall back to a GitHub Actions CI run as the quiet-host equivalent, or record the verdict as INCONCLUSIVE and surface it as a user gate rather than claiming a pass |
| `test_iteration_via_iterate_api` reproduces on a quiet host (genuine regression) | H | L | Phase 5 stops the release path and records a BLOCKED verdict rather than proceeding; no checklist is issued claiming readiness |
| Flipping d1 to a hard gate breaks the runner's exit-code contract in an unnoticed way | M | L | Phase 1 verifies with `bash -n`, `--help` (which exits before `nix develop`), and a real end-to-end run in Phase 4 that must exit 0 |
| Docs drift: `code/scripts/README.md` is outside the recorded `file_scope` and carries the same stale W002 framing | M | H | Phase 2 explicitly widens scope to include it, recorded as a deliberate decision rather than an accidental out-of-scope edit |
| The user tags before confirming the PyPI trusted publisher, burning CI and failing at `publish-pypi` | M | M | Checklist places the trusted-publisher confirmation as gate item 0, above every ordered step, with the exact Owner/Repository/Workflow/Environment values to match |
| An agent is tempted to "just verify" the publish by tagging | H | L | Every phase restates the user-only constraint; Phase 6's checklist has an explicit "What the agent never does" section carried over from the archived template |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2 | 1 |
| 3 | 4 | 1, 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Correct the release-verify.sh W002 gate contract [COMPLETED]

**Premise re-confirmed at implementation time** (2026-08-12): fresh `cd code && rm -rf dist &&
python -m build --no-isolation` (exit 0) followed by `check-wheel-contents dist/*.whl` on the
resulting `model_checker-1.3.0-py3-none-any.whl` reports `OK`, exit 0, with no `--ignore` flag.

**Goal**: `code/scripts/release-verify.sh` treats bare `check-wheel-contents` as the hard gate,
with every trace of the "W002 expected, run with `--ignore`" contract removed from both its
header documentation and its executable step bodies.

**Tasks**:
- [ ] Re-confirm the premise before editing: from a clean `code/dist/`, run a fresh
      `python -m build` and `check-wheel-contents dist/*.whl`, and record that it exits 0 with no
      `--ignore` flag. Do not edit on the research report's word alone.
- [ ] Update the header step-sequence comment (lines 15-16): d1 becomes `[hard gate]`; remove or
      repurpose the d2 line.
- [ ] Remove the "Reading a nonzero check-wheel-contents (bare) exit" header block (lines 52-57)
      describing the superseded W002 expectation.
- [ ] Update the evidence-file manifest comment (the `Evidence files written to <out>/` block) to
      match the post-change output set, including its stated file count.
- [ ] Rewrite `step_d1_wheel_contents_bare()`: classify `gate`, call `fail` on nonzero, and drop
      the appended "A nonzero exit here is EXPECTED today..." note baked into
      `wheel-contents.txt`.
- [ ] Decide and apply the d2 disposition — either remove `step_d2_wheel_contents_ignore_w002()`
      entirely (and its `wheel-contents-ignore-w002.txt` evidence file and call site), or retain
      it demoted to `info` as a historical-comparison signal. Record the decision and its
      rationale in the phase notes; do not leave both a hard-gated d1 and a hard-gated d2.
- [ ] Update the exit-code contract comment if the d2 disposition changes what a nonzero exit
      can mean.
- [ ] Grep the script for any remaining `W002` occurrence and confirm each surviving one is a
      deliberate historical reference, not a live expectation.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: The change is hypothesized to be confined to `code/scripts/release-verify.sh`
at four regions (header lines ~15-16, ~52-57, the evidence-file manifest block, and step bodies
~296-341), and to reduce the evidence set from 12 files to 11 if d2 is removed. Confirm at
implementation time by `grep -n 'W002\|wheel-contents' code/scripts/release-verify.sh` before and
after, and by counting the files the manifest comment enumerates against what Phase 4's real run
actually writes. Line numbers are from the research report and may have drifted — locate by
content, never by line number alone.

**Commit Mode**: atomic-batch

**d2 disposition decision**: removed `step_d2_wheel_contents_ignore_w002()` entirely, along with
its `wheel-contents-ignore-w002.txt` evidence file and its call site in `main()`. Rationale: with
W002 no longer firing, `check-wheel-contents --ignore W002` and bare `check-wheel-contents` are
functionally identical against the current wheel -- retaining d2 would mean carrying a
permanently-redundant second invocation of the same tool rather than a genuine
historical-comparison signal. Evidence set reduced from 12 files to 11, reflected in the header
comment, the `print_help` evidence list, and `generate_parity_diff`'s Evidence Files section.

**Files to modify**:
- `code/scripts/release-verify.sh` - flip d1 to hard gate, remove d2, correct all header
  comments and the evidence manifest

**Verification**:
- `bash -n code/scripts/release-verify.sh` exits 0
- `bash code/scripts/release-verify.sh --help` exits 0 and prints a step sequence with no
  "expected nonzero (W002)" text (the `--help` path returns before entering `nix develop`)
- `grep -c 'ignore W002' code/scripts/release-verify.sh` matches the chosen d2 disposition
- Enumerated direct dependents identified for Phase 2: `.github/RELEASE_SETUP.md`,
  `code/scripts/README.md`

---

### Phase 2: Correct the release documentation to match the new gate contract [NOT STARTED]

**Goal**: Every document describing the rehearsal states the current contract — bare
`check-wheel-contents` is the hard gate, the duplicate `VERSION` files are gone — with the
historical note preserved but re-worded so it is no longer backwards.

**Tasks**:
- [ ] `.github/RELEASE_SETUP.md`: fix the `wheel-contents.txt` evidence-table row (line ~168),
      removing "(W002 expected — see below)".
- [ ] `.github/RELEASE_SETUP.md`: update the hard-gate list (lines ~180-181) so bare
      `check-wheel-contents` is named, not `check-wheel-contents --ignore W002`.
- [ ] `.github/RELEASE_SETUP.md`: rewrite the "Reading a nonzero bare `check-wheel-contents` exit"
      paragraph (lines ~195-200), including removing "Deduplicating those files is tracked as a
      separate, later change" — that change has landed.
- [ ] `.github/RELEASE_SETUP.md`: re-word the "Historical context only" paragraph (lines ~202-206)
      so the "the tree has since grown the W002-triggering duplicate `VERSION` files" clause reads
      correctly (the tree has since lost them). Keep the paragraph's core point that the archived
      task-125 evidence is non-current.
- [ ] `code/scripts/README.md`: correct its `release-verify.sh` section — the "bare and with
      `--ignore W002`" framing and the `wheel-contents-ignore-w002.txt` output-file listing —
      consistent with the Phase 1 d2 disposition.
- [ ] Record in the phase notes that `code/scripts/README.md` was deliberately added beyond the
      task's recorded `file_scope`, with the reason (same stale framing, would otherwise
      immediately contradict the corrected runner).

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: Exactly two documentation files are hypothesized to carry the stale W002
framing (`.github/RELEASE_SETUP.md`, `code/scripts/README.md`). Confirm at implementation time
with `grep -rn 'W002' --include='*.md' . | grep -v '^./specs/'` and correct every live hit found;
if the grep returns a third file, widen this phase rather than deferring it.

**Files to modify**:
- `.github/RELEASE_SETUP.md` - evidence table row, hard-gate list, two W002 paragraphs
- `code/scripts/README.md` - `release-verify.sh` section framing and output-file list

**Verification**:
- Diff read-through confirming every changed hunk lies inside markdown prose
- `grep -rn 'W002' --include='*.md' . | grep -v '^./specs/'` returns only deliberate historical
  references, each read and confirmed correctly worded
- The documented evidence-file list matches the manifest comment Phase 1 left in the runner

---

### Phase 3: Fold post-refactor work into the 1.3.0 CHANGELOG entry [NOT STARTED]

**Goal**: `code/CHANGELOG.md`'s `## [1.3.0]` entry accurately describes everything being
published, with no version bump and all version literals left in agreement.

**Tasks**:
- [ ] Re-confirm the version literals agree before writing: `code/pyproject.toml` line ~9,
      `flake.nix` line ~25, `flake.nix` line ~137, and the CHANGELOG heading. Record the four
      observed values.
- [ ] Re-confirm no `v1.3.0` tag exists (`git tag -l "v1.3.0"` returns empty) — the entire
      fold-not-bump rationale rests on 1.3.0 never having been published.
- [ ] Expand the `## [1.3.0]` entry with sections covering: the core/theory_lib boundary refactor,
      the duplicate `theory_lib/*/VERSION` dedupe and its W002 consequence, the CI fixes (the
      missing `wheel` build dependency and the raised timing budgets), and the new
      `release-verify.sh` rehearsal runner. Derive the content from the actual commit range
      (`git log --oneline <changelog-commit>..HEAD -- code/src`), not from task numbers.
- [ ] Update the entry's date from `2026-07-24` to the intended release date, or add an explicit
      note distinguishing the draft date from the publish date.
- [ ] Leave `## [Unreleased]` present and empty (it is the landing pad for post-release work).
- [ ] Confirm no task-number references leak into `code/CHANGELOG.md` — it is a deliverable
      outside `specs/**`, so cite durable anchors (file paths, feature names) instead.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: Three version literals plus the CHANGELOG heading are hypothesized to be the
complete set of version sources (`model_checker.__version__` derives from `importlib.metadata`
and is not a fourth literal). Confirm with `grep -rn '1\.3\.0' code/pyproject.toml flake.nix
code/CHANGELOG.md` and by `grep -rn '__version__' code/src/model_checker/__init__.py`; if a fourth
literal exists, the fold decision still holds but the confirmation list must be corrected.

**Files to modify**:
- `code/CHANGELOG.md` - expand and re-date the `## [1.3.0]` entry

**Verification**:
- Diff read-through confirming changes are confined to CHANGELOG prose
- `grep -rn 'version' code/pyproject.toml flake.nix | grep '1\.3\.0'` still shows three agreeing
  sites, unchanged by this phase
- `bash .claude/scripts/check-task-references.sh` (or equivalent grep for `task [0-9]`) finds no
  new task-number reference in `code/CHANGELOG.md`

---

### Phase 4: Run the corrected rehearsal and archive fresh evidence [NOT STARTED]

**Goal**: A complete, current `release-verify.sh` evidence set lives under
`specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/` with every hard gate green and
freshly recorded sha256sums.

**Tasks**:
- [ ] Check host contention first (`uptime`, `ps aux | grep -c claude`) and record it — a build
      under heavy load is still valid evidence, but the state must be on record.
- [ ] Run `bash code/scripts/release-verify.sh --ref 1.2.12 --out
      specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/` end to end.
- [ ] Confirm the runner exits 0. On exit 1, do not proceed — read the failing gate's evidence
      file and fix forward. On exit 2, the evidence set is INCOMPLETE and must not be read as a
      pass; resolve the provisioning or reference-fetch failure and re-run.
- [ ] Verify `summary.txt` records `d1-wheel-contents` as class `gate` with `exit=0` — the direct
      confirmation that Phase 1's flip is correct and W002 no longer fires.
- [ ] Verify the archived file set matches the manifest comment Phase 1 left in the runner
      (count and names).
- [ ] Read `parity-diff.md` and `wheel-files-diff.txt` and record a one-paragraph human
      classification of the new-wheel-vs-1.2.12 differences (the refactor will produce a large,
      expected diff; confirm nothing unexpected such as test files, `oracle/`, or `specs/` content
      appears in the wheel).
- [ ] Record the fresh sha256sums of the wheel and sdist from `sha256sums.txt` into the phase
      notes, superseding the archived task-125 hashes (`f85e6512...` / `255d2c01...`) and task
      156's set.
- [ ] Confirm `code/dist/` remains gitignored and is never staged.

**Timing**: 1 hour

**Depends on**: 1, 2, 3

**Verification Tier**: full

**Scope Hypothesis**: The evidence set is hypothesized to contain the file count Phase 1's
manifest comment declares (12 originally, 11 if d2 was removed). Confirm by
`ls -1 specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/ | wc -l` against that
comment; a mismatch means either the manifest or a step body was missed in Phase 1.

**Files to modify**:
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/` - new directory, full
  evidence set (created by the runner)

**Verification**:
- `release-verify.sh` exit code is 0
- `summary.txt` shows every `gate`-class step at `exit=0`
- `twine-check.txt` shows PASSED for both wheel and sdist
- `wheel-contents.txt` shows a clean run with no W002 finding and no appended "expected nonzero"
  note
- `sha256sums.txt` values differ from both the archived task-125 hashes and task 156's, confirming
  a genuinely fresh build

---

### Phase 5: Obtain a quiet-host nix flake check verdict [NOT STARTED]

**Goal**: A recorded, defensible verdict on `nix flake check` against the current tree —
either a clean pass on a demonstrably quiet host, or an explicit regression finding that blocks
the release.

**Tasks**:
- [ ] Establish and record quiet-host conditions before starting: `uptime` load average and
      `ps aux | grep claude` showing no other concurrent agent sessions. If the host is contended,
      either wait for a quiet window or use a GitHub Actions CI run as the quiet-host equivalent
      — do not run and then reinterpret a contended result.
- [ ] Run `nix flake check` to completion. Capture the full output.
- [ ] Record the verdict in one of three explicit forms:
      **PASS** (clean run on a confirmed-quiet host — the release-blocking item is cleared);
      **FLAKE** (`test_iteration_via_iterate_api` and/or
      `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` failed under recorded
      contention but passed quiet, or vice versa across repeated runs — characterize and do not
      block); or **REGRESSION** (a failure reproduces on a confirmed-quiet host — this blocks the
      release and the phase ends with a BLOCKED finding, not a checklist).
- [ ] If the verdict is FLAKE and `test_iteration_via_iterate_api` was the failing test, decide
      whether to proactively raise its `max_time` past 30 (prior evidence records 31.59-64.34s
      wall-clock on this host against that budget), matching the treatment already applied to its
      sibling `test_iterate_two_produces_distinct_models`. If taken, this widens `file_scope` to
      `code/src/model_checker/builder/tests/unit/test_example.py` — record the widening
      deliberately, and re-run at least that test file afterwards.
- [ ] If the verdict is INCONCLUSIVE (no quiet window obtainable and CI unavailable), say so
      plainly and carry it into Phase 6's checklist as a user gate, never as a claimed pass.

**Timing**: 1.25 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: Two tests are hypothesized to be the contention-sensitive set
(`test_iteration_via_iterate_api`, `BM_CM_1-example_case7`). Confirm from the actual run output;
if a third timing-sensitive test surfaces, record it rather than forcing the observation into the
known two.

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_example.py` - conditional, only if the FLAKE
  branch's `max_time` hardening is taken

**Verification**:
- `nix flake check` output captured verbatim, with the host-contention evidence (`uptime`,
  `ps aux`) recorded alongside it
- The verdict is one of PASS / FLAKE / REGRESSION / INCONCLUSIVE, stated explicitly with its
  supporting evidence
- If `max_time` was raised, `PYTHONPATH=code/src pytest
  code/src/model_checker/builder/tests/unit/test_example.py -v` passes

---

### Phase 6: Author the publish checklist and the release-readiness report [NOT STARTED]

**Goal**: The user has a single, current, task-scoped document containing the blocking
trusted-publisher gate, the ordered user-only publish steps, and a copy-paste post-publish
verification runbook — plus a readiness report stating exactly what was verified and what was not.

**Tasks**:
- [ ] Create `specs/151_rerun_release_rehearsal_and_publish_to_pypi/PUBLISH-CHECKLIST.md` using
      `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` as the
      structural template (its section shape: Version Confirmation / Pre-Flight Checks /
      One-Time OIDC Setup / Ordered Release Steps / What the Agent Never Does / References).
      Reuse the structure; replace all of its data.
- [ ] **Gate item 0, first and blocking, USER-ONLY**: confirm on pypi.org (Settings → Publishing)
      that a trusted publisher exists with exactly Owner `benbrastmckie`, Repository
      `ModelChecker`, Workflow `release.yml`, Environment `pypi`; optionally the TestPyPI
      equivalent with Environment `testpypi`. State plainly that GitHub Environments are already
      confirmed present (both created 2026-08-12, no protection rules) and that this PyPI-side
      registration is the remaining half. State the consequence of skipping it: the tag runs
      `test-and-release` and `build`, `publish-testpypi` fails softly under
      `continue-on-error: true`, and `publish-pypi` fails at the OIDC exchange after CI time is
      already spent.
- [ ] Pre-flight section: record the Phase 4 evidence path and the fresh sha256sums; record the
      Phase 5 `nix flake check` verdict verbatim; record the version-literal agreement from
      Phase 3. Mark each with its actual observed state, never a pre-checked box.
- [ ] Add an explicit instruction to re-run
      `bash code/scripts/release-verify.sh --ref 1.2.12` immediately before tagging if any commit
      has touched `code/src` since Phase 4 — the evidence set is not one-and-done.
- [ ] Ordered release steps section, all marked USER-ONLY: create the annotated `v1.3.0` tag, push
      it, watch the `release.yml` run, confirm `publish-pypi` succeeded. Do not invoke `/tag`.
- [ ] Post-publish verification runbook, copy-paste runnable:
      `pip index versions model-checker` shows `1.3.0`; then
      `python3 -m venv testvenv`, `PIP_USER=0 ./testvenv/bin/pip install model-checker`,
      `LD_LIBRARY_PATH=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib
      ./testvenv/bin/model-checker <project>/examples.py`; generate and execute a project for each
      of `logos`, `exclusion`, `imposition`, `bimodal`, expecting 4/4 exit 0. Note that this
      installs FROM PyPI, never from local `dist/`.
- [ ] Add the incidental `z3-solver` note: pip is expected to resolve 5.0.0.0, well beyond the
      `>=4.8.0` floor; confirm all four theories still run clean under it and add an upper pin
      ONLY if something actually breaks.
- [ ] Carry over a "What the agent never does" section: no `git push`, no `git tag`, no
      `twine upload`, no `gh pr create`, no `/merge`, no `/tag`.
- [ ] Write the implementation summary as the release-readiness report: what was fixed, what was
      rehearsed, the fresh hashes, the flake-check verdict, and the one gate that remains open.
- [ ] Confirm the checklist references durable anchors (file paths, workflow names, environment
      names) — task numbers are permitted here since it lives under `specs/**`, but prefer
      durable anchors anyway for the user-facing steps.

**Timing**: 1 hour

**Depends on**: 4, 5

**Verification Tier**: prose

**Files to modify**:
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/PUBLISH-CHECKLIST.md` - new
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/summaries/01_release-rehearsal-publish-prep-summary.md` - new

**Verification**:
- The checklist's gate item 0 is the PyPI trusted-publisher confirmation, positioned before every
  ordered step
- Every pre-flight box reflects an actually-observed state from Phases 3-5, with no box marked
  complete on the strength of a prior task's evidence
- The recorded sha256sums match `rehearsal/sha256sums.txt` exactly
- Diff read-through confirms all content is markdown prose
- No `git push`, `git tag`, `twine upload`, or `/tag` was executed at any point in this plan

---

## Testing & Validation

- [ ] `bash -n code/scripts/release-verify.sh` exits 0
- [ ] `bash code/scripts/release-verify.sh --help` exits 0 with no stale W002 text
- [ ] `bash code/scripts/release-verify.sh --ref 1.2.12 --out specs/151_.../rehearsal/` exits 0
      with every `gate`-class step at `exit=0`
- [ ] `twine check --strict` PASSED for both wheel and sdist
- [ ] Bare `check-wheel-contents` on the fresh wheel exits 0 with no `--ignore`
- [ ] `nix flake check` verdict recorded with host-contention evidence (PASS / FLAKE /
      REGRESSION / INCONCLUSIVE)
- [ ] `grep -rn 'W002' --include='*.md' .` outside `specs/` returns only deliberate, correctly
      worded historical references
- [ ] Version literals agree at `1.3.0` across `code/pyproject.toml`, `flake.nix` (both sites),
      and `code/CHANGELOG.md`
- [ ] `git status --short` shows no `code/dist/` content staged at any point

## Artifacts & Outputs

- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/plans/01_release-rehearsal-publish-prep.md`
  (this file)
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/` (fresh evidence set:
  `build.log`, `twine-check.txt`, `wheel-contents.txt`, listings, diffs, `sha256sums.txt`,
  `parity-diff.md`, `summary.txt`)
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/PUBLISH-CHECKLIST.md`
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/summaries/01_release-rehearsal-publish-prep-summary.md`
- Modified: `code/scripts/release-verify.sh`, `.github/RELEASE_SETUP.md`, `code/scripts/README.md`,
  `code/CHANGELOG.md`, and conditionally
  `code/src/model_checker/builder/tests/unit/test_example.py`

## Rollback/Contingency

- All source changes (Phases 1-3, 5-conditional) are small, additive-or-corrective text edits in
  four to five tracked files. Revert with a targeted `git revert` of the phase commits; no
  migration, schema change, or data transformation is involved.
- The rehearsal evidence set (Phase 4) is generated output under `specs/`; deleting the
  `rehearsal/` directory and re-running the runner reproduces it from scratch. `code/dist/` is
  gitignored and never committed, so no build artifact can leak into history.
- If Phase 5 returns REGRESSION, the correct contingency is to stop, not to revert: leave the
  Phase 1-4 corrections in place (they are independently valid), mark the task `[BLOCKED]` with
  the reproduction evidence, and spawn a task for the failing test before any tag is pushed.
- Nothing in this plan reaches a remote or a package index, so no rollback of a published artifact
  is ever needed. If the user publishes and a defect is found post-publish, PyPI does not permit
  re-uploading the same version — the remedy is a patch release, which is outside this task.
