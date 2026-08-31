# Implementation Plan: Task #158

- **Task**: 158 - Harden release CI / TestPyPI gate
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: 161 (`fix_testpypi_trusted_publisher`) - COMPLETED and verified green on the
  `v1.3.7` tag push (Actions run 32996862484). Input satisfied; safe to land the hard gate.
- **Research Inputs**: specs/158_harden_release_ci_testpypi_gate/reports/01_harden-testpypi-gate.md
- **Artifacts**: plans/01_harden-testpypi-gate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Convert the TestPyPI rehearsal step in `.github/workflows/release.yml` from a soft canary into a
real gate, add a seconds-cheap `preflight` job that fails fast before the 9-job matrix, add a
`verify-testpypi` job that installs and smoke-tests the just-uploaded artifact, and close the
supporting friction points (non-interactive project generation, orchestrator runtime-file
gitignore residue, rehearsal-evidence commit recording, workflow-ordering documentation).

Definition of done: `publish-pypi` cannot run unless a real TestPyPI install-and-import succeeded;
a version/CHANGELOG/tag-shape mismatch fails within seconds rather than after the full matrix;
`model-checker -l <theory>` can generate a project without any `input()` prompt; and the working
tree no longer accumulates tracked orchestrator loop-guard residue before a tag.

Constraints that shape every phase: `git push`, `git tag`, `/merge`, `/tag`, and any twine upload
are **user-only** (`.claude/rules/pr-prohibition.md`). A real tag-push trigger therefore cannot be
rehearsed by the implementer -- every workflow change is verified by static/syntax means plus
careful expression review, never by executing the pipeline.

### Research Integration

The report at `reports/01_harden-testpypi-gate.md` re-verified all eleven numbered items against
the tree on 2026-08-31. Four findings materially change the plan versus the task description's
original text and are carried into the phases below:

1. **Item 3's flake.nix premise is stale.** `flake.nix:21` now derives `version` from
   `code/pyproject.toml` via `builtins.fromTOML` (commit `8252fe74`). The two hardcoded literals
   the task names at `flake.nix:25` and `flake.nix:137` no longer exist -- those line numbers now
   land on unrelated comments. The preflight version check is a **two**-way comparison (tag vs.
   `code/pyproject.toml`), not a three-way one. `flake.nix` needs **no edit** in this task.
2. **Item 5's target text is outside the declared file_scope.** `.github/RELEASE_SETUP.md`
   contains zero `pip index versions` occurrences. The stale advice lives at
   `code/docs/development/PYPI_RELEASE_GUIDE.md:149`, which is not in file_scope. Flagged below,
   not silently edited.
3. **The CHANGELOG preflight gate will block the next release.** `code/CHANGELOG.md`'s newest
   entry is `## [1.3.2]`; `## [Unreleased]` is empty; `code/pyproject.toml` is at `1.3.7`. Every
   release 1.3.3-1.3.7 shipped with no CHANGELOG entry. The gate is correct policy, and its first
   effect will be to block the next tag until an entry is written. Flagged below.
4. **An adjacent `.gitignore` discrepancy was discovered, not named by item 6.** `.gitignore:33`
   reads `**/.return-meta.json`, but `.claude/context/standards/orchestrator-runtime-files.md`
   states in two places that the bare `.return-meta.json` must stay tracked as durable
   per-dispatch provenance. Flagged below as a user decision, not resolved unilaterally.

Confirmed unchanged from the description: item 1's `continue-on-error: true` at
`release.yml:147` and `publish-pypi`'s `needs: [build, publish-testpypi]` at `release.yml:200`
(the gate is a genuine no-op today); item 4's exact defect (`__main__.py` `main()` never reads
`module_flags.file_path` in the `--load_theory` branch, and `ask_generate()` +
`_handle_example_script()` call `input()` three times unconditionally); item 6's six tracked
`.orchestrator-loop-guard` files; item 8's missing commit SHA in `release-verify.sh`'s
`summary.txt` header.

### Prior Plan Reference

No prior plan. This is the first plan version for this task.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no `roadmap_flag` was set, so no
roadmap phases are included and no roadmap items are claimed.

## Goals & Non-Goals

**Goals**:
- Make a TestPyPI upload failure hard-block the production PyPI publish, with one explicit,
  visible escape hatch (`workflow_dispatch` input `skip_testpypi`).
- Prove the uploaded artifact is installable and importable, not merely that bytes moved.
- Fail fast on tag/version/CHANGELOG/tag-shape mismatches before the 9-job matrix runs.
- Give `model-checker` a non-interactive project-generation path that exits non-zero rather than
  raising `EOFError` when required input is missing.
- Stop orchestrator loop-guard files from dirtying the tree before `/tag`.
- Record the commit that `release-verify.sh` evidence was captured against.
- Document the workflow-file ordering hazard in `.github/RELEASE_SETUP.md`.

**Non-Goals**:
- Items 9-12 of the task description. Item 9 is discharged; items 10-12 are superseded by the
  (completed, archived) bimodal-flake task and MUST NOT be executed here.
- Item 1(c)'s GitHub Environment required-reviewer protection rule. Both `pypi` and `testpypi`
  environments exist with `"protection_rules": []`; adding one is web-UI work no agent may
  perform. Surfaced as a user decision, documented in Phase 6, never scripted.
- Any edit to `flake.nix` (finding 1 above: derived version, nothing to check).
- Any edit to `code/docs/development/PYPI_RELEASE_GUIDE.md` (outside file_scope; finding 2).
- Any edit to `code/CHANGELOG.md` (outside file_scope; finding 3 -- backfilling release notes is
  user-authored release content, not agent work).
- Any change to the `-m` pytest selection expressions in `tests.yml`,
  `differential-tests.yml`, or `packaging.yml`. Those three files appear in file_scope only
  because of the CONCURRENCY note's shared territory with the `development`-marker task; nothing
  in items 1 and 3-8 requires touching them. Phase 8 records this as a confirmed no-edit.
- Any `git push`, `git tag`, twine upload, `/merge`, or `/tag`.
- Extending `verify-testpypi`'s smoke test to the full four-theory golden path. Phase 3 lands the
  minimum bar (import + `__version__` equality + `model-checker --help`); the golden-path
  extension is called out as an explicit follow-up decision once Phase 1 has landed.

## Out-of-Scope Flags and User Decision Points

These are surfaced deliberately. None is executed by this plan. The implementer records each in
the implementation summary; none blocks any phase.

| # | Flag | Why it is not executed here | What the user must decide |
|---|------|-----------------------------|---------------------------|
| A | Item 1(c): required-reviewer protection on the `pypi` GitHub Environment | Web-UI-only configuration; explicitly named user-only by the task's own AGENT CONSTRAINT paragraph and `.claude/rules/pr-prohibition.md` | Whether a human click before production publish is wanted, or whether Phase 3's `verify-testpypi` makes it redundant |
| B | The CHANGELOG gate blocks the next release | Phase 4 authors the gate (in scope); `code/CHANGELOG.md` is not in file_scope, and backfilling 1.3.3-1.3.7 release notes is user-authored content | Whether to write a `## [Unreleased]`/next-version CHANGELOG entry before the next tag push, or to land Phase 4's CHANGELOG assertion as a warning first and promote it to a hard failure later |
| C | Item 5's real target, `code/docs/development/PYPI_RELEASE_GUIDE.md:149` (`pip index versions model-checker`) | Outside the declared file_scope; the in-scope `.github/RELEASE_SETUP.md` has zero occurrences | Whether to widen file_scope for this task or spawn a follow-up to correct that one line |
| D | `.gitignore:33`'s `**/.return-meta.json` contradicts `orchestrator-runtime-files.md` | `.gitignore` IS in file_scope and this line is adjacent to item 6's lines, but the task text never raises it -- it is a new research finding, and reversing it would start tracking a file class that is currently ignored repo-wide | Whether to remove the bare pattern to align with the standard, or record that this repo deliberately diverges |
| E | Extending `verify-testpypi` to the four-theory golden path | Depends on Phase 1 landing; adds real CI minutes and a new failure surface to a job that gates production publishes | Whether the minimum-bar smoke test is sufficient, or the golden path should follow in a separate change |
| F | Test files for Phase 1 are not in the declared file_scope | `code/tests/unit/test_main_cli.py` and `code/src/model_checker/builder/tests/unit/test_project.py` are not listed, but `CLAUDE.md` mandates TDD (tests BEFORE implementation) for the in-scope source change | The plan proceeds on the stated assumption that tests covering an in-scope source edit are a corollary of that edit, not scope widening. If the user disagrees, Phase 1 must be re-scoped rather than skipped |

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The `skip_testpypi` expression evaluates wrong under a `push: tags:` trigger (where `inputs` is unpopulated), silently disabling or permanently enabling the escape | H | M | Phase 2 uses the null-safe `${{ inputs.skip_testpypi != true }}` form and verifies it by static expression review plus a syntax-only render; the phase's verification explicitly names "cannot be rehearsed" as its blind spot |
| Dropping `continue-on-error` converts a soft canary into a hard block on every release | H | L | Dependency 161 is verified green on a real tag (`v1.3.7`, run 32996862484); the `skip_testpypi` escape is landed in the same phase, never after |
| TestPyPI index propagation lag makes `verify-testpypi` flaky and blocks good releases | M | M | Bounded retry loop (10 attempts, 15s apart) with a final exit-code check; pin the exact `==${VERSION}` (test.pypi.org still carries a stale `0.1` release that a bare install would resolve) |
| TestPyPI does not mirror dependencies, so `z3-solver` fails to resolve | H | H (certain without mitigation) | `--index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/`, exactly as the task text specifies |
| Four phases edit the same file (`release.yml`), producing conflicting hunks | M | M | Phases 2 -> 3 -> 4 are strictly serialized in three separate waves; each re-reads the file before editing |
| The new CHANGELOG assertion blocks the next release unexpectedly | M | H | Flag B above; Phase 4 prints an explicit, actionable failure message naming `code/CHANGELOG.md` and the version, and the phase records the consequence in the summary |
| `git rm --cached` on loop-guard files is misread as deleting working-tree state | L | L | Phase 5 uses `--cached` only, and verifies with `git status --short` that the working-tree copies survive |
| The non-interactive CLI change breaks the existing interactive path | M | M | Phase 1 is TDD-first and keeps `ask_generate()` as the default path; the new behavior is reachable only under the new flag |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 5, 7 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 6 | 4 |
| 5 | 8 | 1, 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel. Wave 1's four phases touch four disjoint
file sets (`__main__.py`+`project.py`; `release.yml`; `.gitignore`; `release-verify.sh`).
Waves 2-4 exist to serialize the three phases that all edit `release.yml`.

---

### Phase 1: Non-interactive project generation [COMPLETED]

**Goal**: `model-checker -l <theory>` can create a project with no `input()` call and exits
non-zero when required information is missing, instead of dying with `EOFError`.

**Tasks**:
- [x] Read `code/tests/unit/test_main_cli.py` and
      `code/src/model_checker/builder/tests/unit/test_project.py` for existing conventions
- [x] RED: add failing tests covering (a) `-l <theory> -y <name>` generating a project with no
      prompt, (b) the destination directory being honored rather than discarded, (c) a non-zero
      exit when a name is required under the non-interactive flag but absent, (d) the existing
      interactive path still reaching `ask_generate()` when the flag is absent
- [x] Add the non-interactive flag to `_create_parser()` in
      `code/src/model_checker/__main__.py`, following the file's existing long-name +
      single-letter-alias convention (compare `--load_theory/-l`, `--contingent/-c`) and adding
      the letter to the `_short_to_long` map in `parse()`
- [x] Decide and implement how the project name and destination are supplied. The existing
      positional `file_path` (`nargs='?'`) is already bound by argparse when `-l THEORY DIR` is
      passed but is never read by the `--load_theory` branch; either read it, or add an explicit
      name argument. Record the choice and its rationale in the summary
- [x] In `main()`, branch to `builder.generate(name, destination_dir)` directly (it is already
      fully non-interactive) instead of `ask_generate()` when the flag is set, and `sys.exit(1)`
      -- not bare `return` -- when required information is missing
- [x] Make `_handle_example_script()`'s prompt (`project.py:706`) skippable under the same flag,
      via a threaded `run_example: bool = False` parameter or an unconditional
      "you can test your project by running" message
- [x] GREEN: run the new tests plus the existing builder and CLI suites

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: The three `input()` call sites are `project.py:159`, `project.py:165`, and
`project.py:706`, and `main()`'s `--load_theory` branch is the only CLI route into
`ask_generate()` besides the bare-`sys.argv` case. Confirm at implementation time with
`grep -n 'input(' code/src/model_checker/builder/project.py` and
`grep -n 'ask_generate' code/src/model_checker/`; if a fourth prompt or a second route exists,
widen the phase and say so rather than leaving a prompt reachable under the new flag.

**Files to modify**:
- `code/src/model_checker/__main__.py` - new flag in `_create_parser()`, alias in
  `_short_to_long`, non-interactive branch in `main()`
- `code/src/model_checker/builder/project.py` - `_handle_example_script()` prompt made skippable
- `code/tests/unit/test_main_cli.py` - CLI-level tests (see out-of-scope flag F)
- `code/src/model_checker/builder/tests/unit/test_project.py` - builder-level tests (flag F)

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/unit/test_main_cli.py code/src/model_checker/builder/tests/ -v` passes
- A real non-interactive invocation in a temp directory creates a project and exits 0
- The same invocation with stdin closed (`< /dev/null`) does not raise `EOFError`
- Omitting the required name under the flag exits non-zero with a clear message

---

### Phase 2: Make TestPyPI a hard gate with an explicit escape [COMPLETED]

**Goal**: A TestPyPI upload failure blocks the production publish, and the only way past it is a
deliberate, visible `workflow_dispatch` opt-out.

**Tasks**:
- [x] Re-read `.github/workflows/release.yml` in full before editing (dependency 161 landed the
      OIDC-claims diagnostic step in this same job; do not work from the report's line numbers)
- [x] Remove the job-level `continue-on-error: true` (currently line 147) and rewrite the comment
      block above it (currently lines 143-146) to state the new hard-gate posture and name the
      escape hatch. Do NOT remove the `continue-on-error: true` on the OIDC diagnostic step
      itself (currently line 162) -- that one is correctly scoped to a diagnostic
- [x] Add a `workflow_dispatch:` block to the `on:` section (currently `push: tags:` only) with a
      boolean input `skip_testpypi`, `default: false`, and a description naming the consequence
- [x] Gate the `publish-testpypi` job with a null-safe `if:` using the
      `${{ inputs.skip_testpypi != true }}` form. `inputs` is unpopulated under a `push` trigger,
      so an unguarded truthiness read is wrong in both directions -- verify the chosen expression
      by static review against GitHub's documented empty-context behavior
- [x] Leave `publish-pypi`'s `needs:` untouched in this phase (Phase 3 repoints it)

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `.github/workflows/release.yml` - `on:` section, `publish-testpypi` job header and comment

**Verification**:
- The file parses as valid YAML (`python -c 'import yaml,sys; yaml.safe_load(open(...))'`)
- If `actionlint` is available, it reports no new findings; if not, record its absence rather
  than claiming a check that did not run
- `grep -n 'continue-on-error' .github/workflows/release.yml` shows exactly one remaining
  occurrence, on the OIDC diagnostic step
- **Known blind spot, state it in the summary**: a real tag push is user-only and cannot be
  rehearsed by the implementer. The `skip_testpypi` expression's runtime behavior under a
  `push: tags:` trigger is verified by review and syntax only, and is the single highest-value
  thing for the user to watch on the next release

---

### Phase 3: Add the verify-testpypi job [NOT STARTED]

**Goal**: `publish-pypi` runs only after the just-uploaded TestPyPI artifact has been installed
from the index and smoke-tested.

**Tasks**:
- [ ] Re-read `.github/workflows/release.yml` after Phase 2's edits
- [ ] Add a `verify-testpypi` job with `needs: [test-and-release, build, publish-testpypi]`,
      `runs-on: ubuntu-latest`, and no added permissions (it only installs from an index; no OIDC)
- [ ] Re-derive the version locally with `VERSION=${GITHUB_REF#refs/tags/v}`, matching the
      existing pattern in `test-and-release`'s "Get version from tag" step. Do not introduce a
      cross-job `outputs:` block -- this repo's workflows have no precedent for one and
      re-deriving is the lower-diff choice
- [ ] Install with BOTH indexes, pinned to the exact version:
      `pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ "model-checker==${VERSION}"`.
      Never a bare install: test.pypi.org still carries a stale `0.1` release from a pre-CI
      manual upload
- [ ] Wrap the install in a bounded retry for index propagation lag -- a
      `for i in $(seq 1 10); do ... && break; sleep 15; done` loop plus a final exit-code check
      that fails the step if the last attempt also failed. There is no existing retry idiom in
      this repo's workflows or `code/scripts/*.sh` to reuse; match the repo's bash style
      (`set -uo pipefail`, no external retry actions)
- [ ] Smoke test at the minimum bar: import the package, assert `model_checker.__version__`
      equals `${VERSION}`, and run `model-checker --help`
- [ ] Repoint `publish-pypi`'s `needs:` from `[build, publish-testpypi]` to
      `[build, verify-testpypi]` (the direct `publish-testpypi` edge is redundant --
      `verify-testpypi` already depends on it)
- [ ] Record out-of-scope flag E (golden-path extension) in the summary rather than implementing it

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The minimum-bar smoke test needs no dependency on Phase 1, because
`model-checker --help` already exits 0 non-interactively (argparse handles `-h`/`--help` before
`main()` reaches `ask_generate()`). Confirm at implementation time by running
`PYTHONPATH=code/src python -m model_checker --help < /dev/null; echo $?` and checking it is 0.
If that is false, the smoke test must depend on Phase 1's flag and the phase widens accordingly.

**Files to modify**:
- `.github/workflows/release.yml` - new `verify-testpypi` job; `publish-pypi` `needs:` edge

**Verification**:
- The file parses as valid YAML and `actionlint` (if available) reports no new findings
- The job graph is acyclic and every `needs:` target exists: confirm by listing job names and
  their `needs:` values
- The install command contains both `--index-url` and `--extra-index-url` and an explicit `==`
  version pin (grep for all three)
- Same blind spot as Phase 2: the retry loop's real behavior against TestPyPI's propagation lag
  is unrehearsable here

---

### Phase 4: Add the fail-fast preflight job [NOT STARTED]

**Goal**: Tag/source-of-truth mismatches fail within seconds, before the 9-job matrix and the
build run.

**Tasks**:
- [ ] Re-read `.github/workflows/release.yml` after Phase 3's edits
- [ ] Add a `preflight` job with `needs: []` (runs first), `runs-on: ubuntu-latest`, no matrix,
      and `actions/checkout@v4` with `fetch-depth: 0` -- full history and tags are required by
      both the CHANGELOG grep and the tag-ancestry check
- [ ] Assert the tag version equals `code/pyproject.toml`'s `version =` (currently line 11).
      **Two literals, not three** -- see Overview finding 1: `flake.nix:21` derives its version
      from the same TOML file by construction and cannot drift. Do not add a `flake.nix` check;
      it would re-read the identical file and is redundancy, not defense in depth
- [ ] Assert `code/CHANGELOG.md` has a non-empty entry for the version being released. The
      failure message MUST name the file and the version explicitly -- this gate will fire on the
      next release (out-of-scope flag B), and the message is the user's only guidance at that
      moment
- [ ] Assert the tag is annotated and reachable from the default branch:
      `git cat-file -t "$GITHUB_REF_NAME"` reports `tag` (not `commit`, which means a lightweight
      tag) and `git merge-base --is-ancestor "$GITHUB_REF_NAME" origin/master` exits 0. Confirm
      the default branch name is `master` at implementation time rather than assuming it
- [ ] Fold in item 7's mechanical backstop: assert the tagged commit's
      `.github/workflows/release.yml` matches the default branch's copy. `fetch-depth: 0` is
      already set for the checks above, so this is a low-incremental-cost addition to the same
      job rather than a new one
- [ ] Add `preflight` to `test-and-release`'s `needs:` so the expensive matrix never starts before
      these assertions pass

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly two independent version literals exist (tag and
`code/pyproject.toml`), not the three the task description names. Confirm at implementation time
with `grep -n 'version' flake.nix | head` -- if a hardcoded literal has reappeared since commit
`8252fe74`, add the third check and say so; if the derivation stands, record the confirmed
two-literal scope in the summary.

**Files to modify**:
- `.github/workflows/release.yml` - new `preflight` job; `test-and-release` `needs:` edge

**Verification**:
- The file parses as valid YAML and `actionlint` (if available) reports no new findings
- Each assertion's shell logic is exercised locally against the current tree where possible: the
  version comparison and the CHANGELOG grep can both be run by hand against `v1.3.7` /
  `code/pyproject.toml` / `code/CHANGELOG.md` to confirm they behave as intended -- and the
  CHANGELOG check is EXPECTED to report a miss for 1.3.7, which is the gate working correctly,
  not a defect. Record that observed result in the summary
- The tag-ancestry and workflow-match assertions are review-only (they need CI's checkout context)
- `flake.nix` is confirmed unmodified: `git diff --name-only` must not list it

---

### Phase 5: Gitignore and untrack orchestrator loop-guard files [NOT STARTED]

**Goal**: `.orchestrator-loop-guard` files stop dirtying the working tree before a tag, matching
`.claude/context/standards/orchestrator-runtime-files.md`'s ephemeral (must-ignore) class.

**Tasks**:
- [ ] Confirm the current tracked set with `git ls-files | grep orchestrator-loop-guard`
- [ ] Add `**/.orchestrator-loop-guard` to `.gitignore`, adjacent to the existing orchestrator
      runtime entries (currently lines 33-37)
- [ ] `git rm --cached` each tracked loop-guard path. Use `--cached` only -- working-tree copies
      must survive
- [ ] Confirm-and-close, without editing: `.orchestrator-multi-state.json` /
      `.orchestrator-multi-state-sess_*.json` (lines 36-37) and `.return-meta-multi.json` /
      `.return-meta-multi-sess_*.json` (lines 34-35) are ALREADY covered. The task's open question
      about `.return-meta-multi-*` is answered; do not re-add either pair
- [ ] Do NOT touch `.gitignore:33`'s `**/.return-meta.json`. It contradicts the standard (see
      out-of-scope flag D) but reversing it is a user decision -- record it, leave it

**Timing**: 30 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Six `.orchestrator-loop-guard` files are currently tracked (one under
`specs/161_fix_testpypi_trusted_publisher/`, five under `specs/archive/`). Confirm the exact set
with `git ls-files | grep orchestrator-loop-guard | wc -l` immediately before the `git rm --cached`
and untrack whatever that command actually returns -- the count may have moved since research.

**Files to modify**:
- `.gitignore` - one added pattern
- (git index only, via `git rm --cached`) the tracked `.orchestrator-loop-guard` paths

**Verification**:
- `git ls-files | grep orchestrator-loop-guard` returns nothing
- `git check-ignore -v <one of the paths>` reports a match on the new `.gitignore` line
- `ls` confirms the working-tree copies still exist
- `git status --short` shows only the intended deletions-from-index and the `.gitignore` edit

---

### Phase 6: Document the workflow-ordering hazard and the new gates [NOT STARTED]

**Goal**: `.github/RELEASE_SETUP.md`'s "Release Process" section states the push-before-tag
ordering requirement and describes the new preflight/verify gates.

**Tasks**:
- [ ] Add an explicit note to the "Release Process" section (currently lines 74-90) that the
      branch must be pushed (or landed via `/merge`) BEFORE the tag is created and pushed,
      because Actions executes the workflow file **as it exists at the tagged commit**. Cite the
      1.3.0 incident concretely: an uncommitted-then-unpushed
      `pip install build twine` -> `... wheel` fix resolved correctly only by accident of push
      ordering
- [ ] Cross-reference Phase 4's preflight workflow-file-match assertion as the mechanical backstop
- [ ] Document the new gate topology: `preflight` -> matrix -> `build` -> `publish-testpypi` ->
      `verify-testpypi` -> `publish-pypi` -> `github-release`, and the `skip_testpypi`
      `workflow_dispatch` escape and when it is legitimate to use
- [ ] Note the CHANGELOG preflight requirement so the next releaser sees it before tagging rather
      than at tag time (out-of-scope flag B)
- [ ] Record out-of-scope flag A (environment protection rule) as a documented user option, with
      the fact that both environments currently have empty `protection_rules`
- [ ] Add a JSON-API-over-simple-index note (`https://pypi.org/pypi/model-checker/json`, bounded
      retry) for post-publish confirmation. **Only in this file.** Do NOT edit
      `code/docs/development/PYPI_RELEASE_GUIDE.md:149`, where the actual stale
      `pip index versions` advice lives -- it is outside file_scope (out-of-scope flag C)

**Timing**: 45 minutes

**Depends on**: 4

**Verification Tier**: prose

**Files to modify**:
- `.github/RELEASE_SETUP.md` - "Release Process" section additions

**Verification**:
- Diff read-through confirming every changed hunk is prose/markdown with no executable surface
- Every job name and flag name mentioned matches the actual `release.yml` after Phase 4
- Internal file references resolve (`code/CHANGELOG.md`, `code/pyproject.toml`, the checklist path)
- `git diff --name-only` lists exactly one file for this phase

---

### Phase 7: Record the rehearsal-evidence commit [NOT STARTED]

**Goal**: `release-verify.sh` output identifies the tree state it was captured against, so the
"has `code/src` changed since?" check becomes answerable.

**Tasks**:
- [ ] Add the commit SHA to `summary.txt`'s header block (currently lines 176-182, alongside the
      existing `started (UTC)` / `REF` / `OUT_DIR` lines) via `git rev-parse HEAD`
- [ ] Stamp the same SHA into `parity-diff.md`'s header block (currently lines 443-455), for the
      same reason the other identity fields live there
- [ ] Document the companion freshness check as a manual step in the script's own help/comment
      output: `git log <evidence-commit>..HEAD -- code/src` must be empty. State plainly WHY it is
      manual: the script's output goes to `/tmp` or a user-chosen `--out DIR`, both outside
      version control, so preflight has nothing to read the evidence commit from
- [ ] Record the discoverability gap for the user: full automation of item 8 requires first
      deciding where the evidence-commit record persists past the ephemeral output directory.
      That is a design decision, not an implementation detail, and is not made here

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/scripts/release-verify.sh` - `summary.txt` header block, `parity-diff.md` header block,
  help/comment text

**Verification**:
- `bash -n code/scripts/release-verify.sh` passes
- If `shellcheck` is available, no new findings; if not, say so rather than claiming the check
- A real run (or the narrowest invocation that produces `summary.txt`) shows the SHA in the
  header, and that SHA matches `git rev-parse HEAD`
- The script still exits with its prior status on an unchanged tree

---

### Phase 8: Full gate run and flag reporting [NOT STARTED]

**Goal**: The complete repository gate set passes over all changes, and every out-of-scope flag
and unrehearsable blind spot is reported to the user rather than left implicit.

**Tasks**:
- [ ] Run the full test suite: `PYTHONPATH=code/src pytest code/tests/ -v`
- [ ] Run the builder and CLI suites specifically, since Phase 1 touched them
- [ ] Re-validate every edited YAML file parses, and run `actionlint` over
      `.github/workflows/release.yml` if available
- [ ] Confirm the final `release.yml` job graph end to end: `preflight` -> `test-and-release` ->
      `build` -> `publish-testpypi` -> `verify-testpypi` -> `publish-pypi` -> `github-release`,
      with every `needs:` target existing and no cycle
- [ ] Confirm the no-edit claims explicitly, with evidence: `flake.nix`,
      `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`,
      `.github/workflows/packaging.yml`, `code/pyproject.toml`, `code/CHANGELOG.md`, and
      `code/docs/development/PYPI_RELEASE_GUIDE.md` must all be absent from
      `git diff --name-only` against the pre-task baseline
- [ ] Write the implementation summary, which MUST include: all six out-of-scope flags (A-F) with
      their current status; the unrehearsable blind spots from Phases 2-4; the observed CHANGELOG
      gate result from Phase 4's local exercise; and the Phase 1 name/destination design choice
- [ ] Confirm no `git push`, `git tag`, `/merge`, `/tag`, or twine upload was performed

**Timing**: 45 minutes

**Depends on**: 1, 2, 3, 4, 5, 6, 7

**Verification Tier**: full

**Files to modify**:
- None (verification and reporting only; the summary artifact is written under `specs/`)

**Verification**:
- Full pytest run is green, or every failure is triaged and shown to pre-date this task
- The job-graph confirmation is recorded as actual command output, not asserted from memory
- The no-edit list above is confirmed by `git diff --name-only`, quoted in the summary

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` passes
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v` passes
- [ ] New Phase 1 tests fail before the implementation and pass after (RED -> GREEN recorded)
- [ ] `model-checker -l <theory> ...` completes non-interactively with stdin closed, exit 0
- [ ] The same command with required information missing exits non-zero with a clear message
- [ ] The interactive path is unchanged when the new flag is absent
- [ ] `.github/workflows/release.yml` parses as YAML; `actionlint` clean if available
- [ ] `release.yml` has exactly one `continue-on-error`, on the OIDC diagnostic step
- [ ] The `verify-testpypi` install command carries both index URLs and an `==` version pin
- [ ] `git ls-files | grep orchestrator-loop-guard` is empty; working-tree copies survive
- [ ] `bash -n code/scripts/release-verify.sh` passes; `summary.txt` carries the commit SHA
- [ ] `flake.nix`, the three sibling workflow files, `code/pyproject.toml`, `code/CHANGELOG.md`,
      and `PYPI_RELEASE_GUIDE.md` are all unmodified

## Artifacts & Outputs

- `specs/158_harden_release_ci_testpypi_gate/plans/01_harden-testpypi-gate.md` (this file)
- `specs/158_harden_release_ci_testpypi_gate/summaries/01_harden-testpypi-gate-summary.md`
- `.github/workflows/release.yml` - hard TestPyPI gate, `skip_testpypi` escape,
  `verify-testpypi` job, `preflight` job, rewired `needs:` edges
- `.github/RELEASE_SETUP.md` - ordering hazard, gate topology, CHANGELOG requirement, JSON-API
  verification note, environment-protection user option
- `.gitignore` - `**/.orchestrator-loop-guard`
- `code/scripts/release-verify.sh` - evidence-commit recording
- `code/src/model_checker/__main__.py`, `code/src/model_checker/builder/project.py` -
  non-interactive project generation
- New/extended tests in `code/tests/unit/test_main_cli.py` and
  `code/src/model_checker/builder/tests/unit/test_project.py`

## Rollback/Contingency

Every phase is an independent, self-contained commit, so rollback is per-phase `git revert`.

- **If the hard gate proves too aggressive in practice** (Phase 2): the `skip_testpypi`
  `workflow_dispatch` escape is the designed response and needs no code change. Reverting Phase 2
  alone restores the soft canary without disturbing Phases 3-4.
- **If `verify-testpypi` flakes on index propagation** (Phase 3): widen the retry bound before
  reverting. If it must be reverted, also revert `publish-pypi`'s `needs:` edge back to
  `[build, publish-testpypi]` in the same commit, or the graph breaks.
- **If the CHANGELOG assertion blocks a release the user needs out** (Phase 4): the escape is to
  write the CHANGELOG entry, not to weaken the gate. If a same-day release is genuinely blocked,
  demote that one assertion to a warning as a temporary measure and record it, rather than
  removing the whole preflight job -- the version and tag-shape checks are unrelated to it.
- **If Phase 5's untracking is unwanted**: `git revert` restores the index entries; the
  working-tree files were never touched.
- **If Phase 1 regresses the interactive path**: the new behavior is reachable only under the new
  flag, so reverting the `main()` branch alone restores prior behavior while keeping the tests as
  documentation of intent.
