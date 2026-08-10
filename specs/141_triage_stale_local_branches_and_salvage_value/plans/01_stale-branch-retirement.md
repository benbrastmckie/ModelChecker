# Implementation Plan: Task #141

- **Task**: 141 - Triage the 9 stale local-only branches, salvage anything of value, then retire them
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/141_triage_stale_local_branches_and_salvage_value/reports/01_stale-branch-triage.md
- **Artifacts**: plans/01_stale-branch-retirement.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; .claude/rules/no-task-references-in-deliverables.md; .claude/rules/pr-prohibition.md
- **Type**: general
- **Lean Intent**: false

## Overview

The triage phase is complete: all nine stale local-only branches have recorded, evidence-grounded
verdicts (five `(a) superseded`, four `(c) finding worth recording`, none `(b) reusable code`,
none `(d) unclear`). This plan executes the salvage-and-retire half: it writes the four `(c)`
findings into durable, branch-independent engineering documentation, bundles all nine branches to
a verified archive outside the repository, deletes the nine local branches behind an explicit
ordering gate, and records the verdict table plus verification evidence in the task summary.

**Definition of done**: the nine branch names no longer appear in `git branch --list`; a verified
`.bundle` file exists outside the repository for each of the nine with its `git bundle verify`
output recorded; the cvc5 and witness/non-determinism findings are readable in the codebase's own
documentation by someone who never knew the branches existed; and the summary carries the
nine-row verdict table with measured real deltas.

**This plan contains no source-code changes.** Research classified no branch as `(b) reusable
code as-is` — every piece of code worth having is already present in `master` in cleaner form.
Consequently there are no new tests, no `pytest` runs against changed behavior, and no test phases.
Verification is entirely documentation-content checks and git-state checks. Inventing a test phase
here would be fabricating work; the Testing & Validation section below reflects that honestly.

### Research Integration

Findings carried directly from `reports/01_stale-branch-triage.md`:

- All nine branches share one ancient merge-base with `master` (`fcf2b95`, 2024-02-08), so raw
  `master..branch` counts (1978-2108) measure inherited pre-restoration history, not branch work.
  The reliable deltas are the pairwise-ancestor numbers, reproduced in the verdict table below.
- Three internal ancestor chains exist: `bimodal_witness_backup` -> `bimodal_witness`;
  `bimodal_refactor` -> {`witness-falsity-attempt`, `quantifier-free-witnesses`};
  `cvc5-feasibility-test` -> `bimodal-cvc5-pilot`.
- The witness-predicate refactor line's destination already exists in `master`'s
  `bimodal/semantic/` subpackage, including a `ForAll`-based `_witness_constraint_for_falsity()`.
  `master` has no `quantifier_free_witnesses` setting: that path was built, marked
  "production-ready", and never adopted.
- The un-superseded facts are the cvc5 feasibility result (`mbqi`+`enum-inst`, `BM_CM_1` in ~6ms
  vs Z3 timeout, ~850x, 30/30 deterministic across six countermodel examples) and the unresolved
  `CallableFunction` segfault the follow-on pilot hit and never fixed.
- The original "non-determinism is inherent to `ForAll` instantiation heuristics" diagnosis was
  later superseded by a more precise root cause found independently: a process-global
  `_bound_var_counter` in bimodal's `operators.py` leaking its numeric suffix across runs. That
  counter and its `reset_bound_var_counter()` fix are present in the working tree today
  (`operators.py:69`, `:72`, `:130`).
- Recommended documentation homes, both confirmed to exist:
  `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` (18.8 KB, ends with
  `## Theoretical Background` / `## Conclusion`) and `code/src/model_checker/solver/README.md`
  (153 lines, ends with `## Known Differences`). Neither currently contains any `task N` citation.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap phases are required.

## Goals & Non-Goals

**Goals**:

- Every branch classified `(c)` has its finding written into a durable file under `code/`, phrased
  as engineering documentation that stands on its own once the branch is gone.
- All nine branches archived as individually verified, self-contained git bundles at a stated
  absolute path outside the repository working tree and outside `/tmp`.
- All nine local branches deleted, gated on the two preceding conditions being recorded and green.
- A nine-row verdict table with measured real deltas, bundle paths, and verification output
  recorded in the task summary.

**Non-Goals**:

- No source-code changes, no ported code, no new tests (nothing was classified `(b)`).
- No remote operations of any kind. No `git push` in any form; no deletion or modification of any
  `origin/*` ref. The ten remote branches are entirely out of scope and must be left untouched.
- No merging of any stale branch into `master` or any other branch.
- No checkout of `master` or of any of the nine branches. All branch content is read with
  `git show <branch>:<path>` and `git diff`, never by switching the working tree.
- Not resolving the open question of whether bimodal's `'solver': 'cvc5'` setting works end-to-end
  today. Phase 2 records that as an explicitly open question in the documentation; verifying it
  requires installing and running cvc5 and belongs to a separate task.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Branch deleted before its bundle verifies, losing history irrecoverably | H | L | Phase 4 opens with an explicit gate script that re-runs `git bundle verify` on all nine bundles and aborts on any non-zero exit; deletion is unreachable unless the gate passes. |
| Bundle written under the repo working tree or under `/tmp`, then lost | H | L | Absolute archive path `/home/benjamin/branch-archive/ModelChecker/` is fixed in Phase 3 and asserted with a guard that the path does not start with the repo root and does not start with `/tmp`. |
| Branch names containing `/` produce broken bundle filenames | M | M | Filenames sanitize `/` to `__` (e.g. `feature__bimodal-cvc5-pilot.bundle`); the manifest records the exact original ref alongside each filename. |
| Documentation written as a branch postmortem, becoming meaningless after deletion | M | M | Phase 1 and Phase 2 success criteria include a `grep` that fails if any of the nine branch names appears in the edited files. |
| Task-number citations leak into files under `code/` | M | M | Phase 1 and Phase 2 success criteria include a `grep -E 'task [0-9]+'` check that must return no matches in the edited files. |
| A phase needs a checkout of a stale branch to read content | M | L | Not required by any phase: `git show <branch>:<path>` reads any blob without switching. If an implementer nonetheless finds a checkout unavoidable, that is a stop-and-report condition, not a step to improvise: the working tree is on `task-140-fix-bimodal-order-dependence` with uncommitted changes in `specs/`, and any checkout must be preceded by `bash .claude/scripts/git-snapshot.sh` and followed by a restore. |
| Accidental deletion of a live branch (`master`, `task-117-*`, `task-140-*`) | H | L | Phase 4 deletes only from a hardcoded nine-name list and asserts afterwards that exactly `master`, `task-117-restore-model-checker`, and `task-140-fix-bimodal-order-dependence` remain. |
| `git branch -D` fails on the currently checked-out branch | L | L | None of the nine is checked out; the working tree is on `task-140-fix-bimodal-order-dependence`. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |
| 3 | 5 | 4 |

Phases within the same wave can execute in parallel. Phases 1, 2, and 3 touch disjoint targets
(bimodal docs, solver docs, and the external archive respectively) and share no files.

**Territory**:

| Phase | Owns (writes) |
|-------|---------------|
| 1 | `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` |
| 2 | `code/src/model_checker/solver/README.md` |
| 3 | `/home/benjamin/branch-archive/ModelChecker/*`, `specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md` |
| 4 | local git refs only (deletions) |
| 5 | `specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md` |

---

### Phase 1: Record the witness and non-determinism findings in bimodal architecture docs [COMPLETED]

- **Goal:** A reader of `bimodal/docs/ARCHITECTURE.md` who has never heard of the retired branches
  learns (i) that a quantifier-free witness encoding was built, validated, and deliberately not
  adopted, (ii) that the non-determinism it was built to work around has a different, smaller,
  already-fixed root cause, and (iii) that the `ForAll`-based falsity constraint in the current
  code is the surviving piece of that line of work.

- **Depends on:** none

- **Timing:** 1 hour

- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - add one new top-level
    section, `## Witness Predicate Design History`, placed after `## Extension Points` and before
    `## Testing Architecture`; add its entry to the existing `## Table of Contents` list.

- **Tasks:**
  - [x] **Task 1.1**: Read the current `## Constraint Generation` and `## Extension Points`
        sections of `ARCHITECTURE.md` to match voice and heading depth. *(completed)*
  - [x] **Task 1.2**: Read `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
        and `code/src/model_checker/theory_lib/bimodal/operators.py` (lines 50-135) so every claim
        in the new section names a construct that actually exists in the tree today. *(completed:
        discovered `_witness_constraint_for_falsity()` is an unreached placeholder, not the active
        mechanism — see deviation below)*
  - [x] **Task 1.3**: Optionally read the abandoned encoding via `git show
        feature/quantifier-free-witnesses:Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
        to confirm the `generate_witness_constraints_quantifier_free()` name and the
        `quantifier_free_witnesses` setting name before citing them. Read-only; do not check out.
        *(completed: also cross-checked `semantic.py`/`examples.py` on that branch for the exact
        setting name)*
  - [x] **Task 1.4**: Write `### Falsity Constraints for Modal Operators`. *(deviation: altered —
        direct inspection showed `_witness_constraint_for_falsity()` is a bare-`pass` placeholder
        never called outside its own tests; the actual Box true/false mechanism is
        `z3.ForAll`/`z3.Exists` implemented directly in `NecessityOperator` in `operators.py`. The
        section documents the real mechanism and names the witness-registry classes as unused
        scaffolding, rather than presenting the placeholder as the active design)*
  - [x] **Task 1.5**: Write `### The Quantifier-Free Encoding, and Why It Is Not Used`: an
        alternative encoding enumerating `(world, time)` pairs instead of using `z3.ForAll` was
        implemented and validated to the point of being called production-ready. It is not in the
        codebase and there is no `quantifier_free_witnesses` setting. Records why: it was built to
        work around non-deterministic `Box`-countermodel results, and that symptom was later
        traced to a different cause (next subsection), so the encoding's motivating problem no
        longer exists. States plainly that reintroducing it should require a fresh, measured
        justification. *(completed)*
  - [x] **Task 1.6**: Write `### Non-Determinism: Diagnosed Causes`: contrasts the two
        attributions. The earlier attribution blamed Z3's `ForAll` quantifier-instantiation
        heuristics. The confirmed cause was a process-global bound-variable counter in
        `operators.py` whose numeric suffix leaked across successive semantics instances, making
        constraint variable names order-dependent; the fix is `reset_bound_var_counter()`, called
        once per fresh `BimodalSemantics`, with `test_bound_var_counter_isolation.py` as the
        empirical guard. Adds the forward-looking rule: when bimodal results become
        order-dependent again, check counter/naming isolation before concluding that `ForAll`
        instantiation is inherently non-deterministic. *(completed)*
  - [x] **Task 1.7**: Add the new section to `## Table of Contents`. *(completed)*
  - [x] **Task 1.8**: Verify no branch name and no task-number citation appears in the file.
        *(completed: both greps confirmed empty)*

- **Verification** (each is a command whose exit status or output decides pass/fail; run from
  `/home/benjamin/Projects/ModelChecker`):
  - [ ] Section exists:
        `grep -q '^## Witness Predicate Design History' code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
  - [ ] All three subsections exist (expect `3`):
        `grep -cE '^### (Falsity Constraints for Modal Operators|The Quantifier-Free Encoding, and Why It Is Not Used|Non-Determinism: Diagnosed Causes)' code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
  - [ ] Substantive content present (expect all four to match):
        `grep -c 'reset_bound_var_counter' ...ARCHITECTURE.md`,
        `grep -c '_witness_constraint_for_falsity' ...ARCHITECTURE.md`,
        `grep -c 'quantifier_free_witnesses' ...ARCHITECTURE.md`,
        `grep -c 'test_bound_var_counter_isolation' ...ARCHITECTURE.md`
  - [ ] No task-number citation (must print nothing, exit 1):
        `grep -nEi 'task [0-9]+' code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
  - [ ] No branch-name anchor (must print nothing, exit 1):
        `grep -nE 'bimodal_refactor|bimodal_witness|quantifier-free-witnesses|witness-falsity-attempt|cvc5-feasibility-test|bimodal-cvc5-pilot|refactor/exclusion|new_claude' code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
  - [ ] Every code symbol cited actually exists (each must exit 0):
        `grep -q 'reset_bound_var_counter' code/src/model_checker/theory_lib/bimodal/operators.py` and
        `grep -q '_witness_constraint_for_falsity' code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`

---

### Phase 2: Record the cvc5 feasibility result and the known segfault in the solver docs [NOT STARTED]

- **Goal:** A reader of `solver/README.md` deciding whether to set `'solver': 'cvc5'` learns the
  concrete measured reason the cvc5 backend exists, the exact option configuration that made it
  work, the fact that default cvc5 settings do not, and the one known integration failure mode -
  without needing any branch, report, or task tracker.

- **Depends on:** none

- **Timing:** 45 minutes

- **Files to modify:**
  - `code/src/model_checker/solver/README.md` - add `## Background: Why a cvc5 Backend` after the
    existing `## Architecture` section, and `## Known Issues` immediately before the existing
    `## Known Differences` section.

- **Tasks:**
  - [ ] Read `code/src/model_checker/solver/README.md` in full (153 lines) and
        `code/src/model_checker/solver/cvc5_adapter.py` to confirm option-setting and
        function-application call sites before describing them.
  - [ ] Confirm the exposed setting: `grep -n "'solver'" code/src/model_checker/theory_lib/bimodal/semantic/core.py`
        (currently `'solver': 'z3'` at line 63 with a `'z3' or 'cvc5'` comment).
  - [ ] Optionally read the pilot's reproduction script via
        `git show feature/bimodal-cvc5-pilot:test_segfault_debug.py` (path may differ; locate with
        `git ls-tree -r --name-only feature/bimodal-cvc5-pilot | grep segfault`) to confirm the
        failing call shape before describing it. Read-only; do not check out.
  - [ ] Write `## Background: Why a cvc5 Backend`. Content: on the bimodal theory's hardest
        countermodel examples, Z3 timed out under both the quantified and the quantifier-free
        witness encodings; cvc5 configured with `mbqi` and `enum-inst` solved the hardest case
        (`BM_CM_1`) in roughly 6 ms - about a 850x improvement over the Z3 timeout threshold - and
        reproduced deterministically across 30 runs covering six countermodel examples
        (`BM_CM_1`, `BM_CM_2`, `TN_CM_1`, `TN_CM_2`, `MD_CM_1`, `MD_CM_2`) with no loss of
        countermodel correctness. State the configuration dependency explicitly and prominently:
        with default options cvc5 returns `unknown` immediately; the result depends entirely on
        enabling `mbqi` and `enum-inst`. Note that these measurements came from standalone scripts
        against an ad hoc harness, not from this abstraction layer, so they establish feasibility
        rather than current-state behavior.
  - [ ] Write `## Known Issues`, covering two items:
        (1) *cvc5 segfault on callable-function application* - an attempt to drive the bimodal
        theory through the cvc5 backend hit a reproducible segmentation fault when applying a
        declared function to an argument through the adapter's function-application path
        (`apply_function` with a `CallableFunction`-style handle). The fault was reproduced with a
        minimal script and never resolved. Anyone enabling cvc5 for a theory that declares and
        applies uninterpreted functions should expect to hit it and should reproduce it minimally
        first.
        (2) *bimodal's cvc5 path is unverified end-to-end* - the `'solver'` setting accepts
        `'cvc5'`, but no test or documented run demonstrates that bimodal produces correct
        countermodels through it. Treat the setting as unvalidated for bimodal until such a run
        exists.
  - [ ] Verify no branch name and no task-number citation appears in the file.

- **Verification** (run from `/home/benjamin/Projects/ModelChecker`):
  - [ ] Both sections exist (expect `2`):
        `grep -cE '^## (Background: Why a cvc5 Backend|Known Issues)' code/src/model_checker/solver/README.md`
  - [ ] Measured specifics present (each must exit 0):
        `grep -q 'mbqi' code/src/model_checker/solver/README.md`,
        `grep -q 'enum-inst' code/src/model_checker/solver/README.md`,
        `grep -q 'BM_CM_1' code/src/model_checker/solver/README.md`,
        `grep -qE '850|6 ?ms' code/src/model_checker/solver/README.md`
  - [ ] Segfault issue recorded (each must exit 0):
        `grep -qi 'segfault\|segmentation fault' code/src/model_checker/solver/README.md`,
        `grep -q 'apply_function' code/src/model_checker/solver/README.md`
  - [ ] Section ordering preserved - `## Known Issues` precedes `## Known Differences`:
        `test "$(grep -n '^## Known Issues' code/src/model_checker/solver/README.md | cut -d: -f1)" -lt "$(grep -n '^## Known Differences' code/src/model_checker/solver/README.md | cut -d: -f1)"`
  - [ ] No task-number citation (must print nothing, exit 1):
        `grep -nEi 'task [0-9]+' code/src/model_checker/solver/README.md`
  - [ ] No branch-name anchor (must print nothing, exit 1):
        `grep -nE 'bimodal_refactor|bimodal_witness|quantifier-free-witnesses|witness-falsity-attempt|cvc5-feasibility-test|bimodal-cvc5-pilot|refactor/exclusion|new_claude' code/src/model_checker/solver/README.md`

---

### Phase 3: Bundle all nine branches outside the repository and verify each bundle [NOT STARTED]

- **Goal:** Nine self-contained, individually verified git bundles exist at a fixed absolute path
  outside the repository working tree and outside `/tmp`, with tip SHAs, verification output, and
  checksums recorded in the task artifacts, making the subsequent deletion fully reversible.

- **Depends on:** none

- **Timing:** 30 minutes

- **Archive location (fixed, stated explicitly):**
  `/home/benjamin/branch-archive/ModelChecker/`

  This is outside `/home/benjamin/Projects/ModelChecker` (so it is not in the working tree, not
  tracked, and not touched by any git operation on the repo) and outside `/tmp` (so it survives
  reboot and tmpfs cleanup).

- **Bundle naming:** branch name with `/` replaced by `__`, plus `.bundle`:

  | Branch | Bundle filename |
  |---|---|
  | `bimodal_refactor` | `bimodal_refactor.bundle` |
  | `feature/bimodal-cvc5-pilot` | `feature__bimodal-cvc5-pilot.bundle` |
  | `feature/bimodal_witness` | `feature__bimodal_witness.bundle` |
  | `feature/bimodal_witness_backup` | `feature__bimodal_witness_backup.bundle` |
  | `feature/cvc5-feasibility-test` | `feature__cvc5-feasibility-test.bundle` |
  | `feature/quantifier-free-witnesses` | `feature__quantifier-free-witnesses.bundle` |
  | `feature/witness-falsity-attempt` | `feature__witness-falsity-attempt.bundle` |
  | `new_claude` | `new_claude.bundle` |
  | `refactor/exclusion` | `refactor__exclusion.bundle` |

- **Tasks:**
  - [ ] Create the archive directory: `mkdir -p /home/benjamin/branch-archive/ModelChecker`.
  - [ ] Assert the archive path is neither inside the repo nor under `/tmp` before writing
        anything (guard: the path must not begin with `/home/benjamin/Projects/ModelChecker` and
        must not begin with `/tmp`).
  - [ ] For each of the nine branches, record the tip SHA with
        `git rev-parse refs/heads/<branch>`.
  - [ ] For each of the nine, create a self-contained bundle covering the branch's full history:
        `git bundle create /home/benjamin/branch-archive/ModelChecker/<file>.bundle refs/heads/<branch>`.
        Bundling the full ref (not a `master..branch` range) means the bundle has no prerequisites
        and verifies standalone in any clone.
  - [ ] For each bundle, run `git bundle verify <path>` and capture both its stdout and its exit
        status. Abort the phase on any non-zero exit.
  - [ ] Record `sha256sum` for each bundle.
  - [ ] Write `specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md`
        containing: the archive absolute path; a nine-row table of branch, bundle filename, tip
        SHA, bundle byte size, and sha256; the verbatim `git bundle verify` output for all nine;
        and a short restore recipe
        (`git fetch /home/benjamin/branch-archive/ModelChecker/<file>.bundle
        refs/heads/<branch>:refs/heads/<branch>`).
  - [ ] Do not delete anything in this phase. Deletion belongs exclusively to Phase 4.

- **Verification** (run from `/home/benjamin/Projects/ModelChecker`):
  - [ ] Exactly nine bundles exist (expect `9`):
        `ls /home/benjamin/branch-archive/ModelChecker/*.bundle | wc -l`
  - [ ] Every bundle verifies (expect no output and exit 0 from the loop):
        `for b in /home/benjamin/branch-archive/ModelChecker/*.bundle; do git bundle verify "$b" >/dev/null || echo "FAIL $b"; done`
  - [ ] Each bundle's contained tip matches the live branch tip (expect no `MISMATCH` lines): for
        each branch, compare `git rev-parse refs/heads/<branch>` against the SHA reported by
        `git bundle list-heads <bundle>`.
  - [ ] Manifest exists and has nine data rows:
        `test -f specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md` and
        `grep -cE '\.bundle' specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md`
        returns at least `9`.
  - [ ] Archive is outside the repo (must print nothing, exit 1):
        `git -C /home/benjamin/Projects/ModelChecker status --porcelain | grep 'branch-archive'`
  - [ ] Nothing was deleted yet (expect `9`):
        `git branch --list --format='%(refname:short)' | grep -cE '^(bimodal_refactor|feature/bimodal-cvc5-pilot|feature/bimodal_witness|feature/bimodal_witness_backup|feature/cvc5-feasibility-test|feature/quantifier-free-witnesses|feature/witness-falsity-attempt|new_claude|refactor/exclusion)$'`

---

### Phase 4: Retire the nine local branches behind an explicit ordering gate [NOT STARTED]

- **Goal:** The nine stale local branches are deleted, and the deletion provably could not have
  happened before the findings were written and the bundles verified.

- **Depends on:** 1, 2, 3

- **Timing:** 15 minutes

- **Branches deleted (all nine):** `bimodal_refactor`, `feature/bimodal-cvc5-pilot`,
  `feature/bimodal_witness`, `feature/bimodal_witness_backup`, `feature/cvc5-feasibility-test`,
  `feature/quantifier-free-witnesses`, `feature/witness-falsity-attempt`, `new_claude`,
  `refactor/exclusion`.

  **Branches kept (must survive untouched):** `master`, `task-117-restore-model-checker`,
  `task-140-fix-bimodal-order-dependence` (the current HEAD). No branch from the nine is kept -
  every one is either `(a) superseded` with its destination already in `master`, or `(c)` with its
  finding written to durable documentation in Phases 1-2. All nine are bundled regardless of
  verdict, so retirement is reversible in every case.

  **Remote refs deleted: none.** The ten `origin/*` refs are out of scope and must be identical
  before and after this phase.

- **Tasks:**
  - [ ] **Gate check A - verdicts recorded**: assert
        `specs/141_triage_stale_local_branches_and_salvage_value/reports/01_stale-branch-triage.md`
        exists and its verdict table names all nine branches. Abort on failure.
  - [ ] **Gate check B - findings written**: re-run every content assertion from Phase 1 and
        Phase 2 verification. Abort on any failure.
  - [ ] **Gate check C - bundles green**: re-run `git bundle verify` on all nine bundles and
        re-confirm the count is nine. Abort on any non-zero exit.
  - [ ] Only if A, B, and C all pass: delete each of the nine with
        `git branch -D <branch>` (local only). Capture each command's output line, which contains
        the deleted tip SHA, for the summary.
  - [ ] Confirm each deleted tip SHA matches the SHA recorded in `bundle-manifest.md`.
  - [ ] Run no `git push`, no `git remote` mutation, and no `git merge` in this phase or any other.

- **Verification** (run from `/home/benjamin/Projects/ModelChecker`):
  - [ ] None of the nine remains (expect `0`):
        `git branch --list --format='%(refname:short)' | grep -cE '^(bimodal_refactor|feature/bimodal-cvc5-pilot|feature/bimodal_witness|feature/bimodal_witness_backup|feature/cvc5-feasibility-test|feature/quantifier-free-witnesses|feature/witness-falsity-attempt|new_claude|refactor/exclusion)$'`
  - [ ] Exactly three local branches remain (expect `3`):
        `git branch --list --format='%(refname:short)' | wc -l`
  - [ ] The three survivors are the expected ones (expect `3`):
        `git branch --list --format='%(refname:short)' | grep -cE '^(master|task-117-restore-model-checker|task-140-fix-bimodal-order-dependence)$'`
  - [ ] HEAD unchanged (expect `task-140-fix-bimodal-order-dependence`):
        `git rev-parse --abbrev-ref HEAD`
  - [ ] Remote refs untouched (expect `10`):
        `git branch -r --no-color | wc -l`
  - [ ] Bundles still all verify after deletion (expect no `FAIL` lines):
        `for b in /home/benjamin/branch-archive/ModelChecker/*.bundle; do git bundle verify "$b" >/dev/null || echo "FAIL $b"; done`
  - [ ] Round-trip recoverability spot-check on one bundle without mutating refs (expect the tip
        SHA to be listed):
        `git bundle list-heads /home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle`

---

### Phase 5: Record the verdict table and verification evidence in the task summary [NOT STARTED]

- **Goal:** The task summary is the single place a future reader can consult to see what each of
  the nine branches was, what was decided, what was salvaged and where it now lives, where the
  archive is, and the raw evidence that every step verified.

- **Depends on:** 4

- **Timing:** 30 minutes

- **Files to create:**
  - `specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md`

- **Tasks:**
  - [ ] Create `summaries/` lazily at write time (do not pre-create other directories).
  - [ ] Write the nine-row verdict table with these columns: branch, verdict `(a)`/`(c)`, measured
        real delta (commits since nearest real ancestor, per the research report), last commit
        date, disposition (deleted), bundle filename, and - for `(c)` rows - the exact durable
        documentation path and section heading where the finding now lives.
  - [ ] Reproduce the measured real deltas from the research report: `bimodal_refactor` 70 commits
        since `338f090e`; `feature/bimodal_witness` 16 since `338f090e`;
        `feature/bimodal_witness_backup` 2 since `338f090e`; `feature/quantifier-free-witnesses` 6
        on `bimodal_refactor`'s tip; `feature/witness-falsity-attempt` 1 on `bimodal_refactor`'s
        tip; `feature/cvc5-feasibility-test` 4 on `bimodal_refactor`'s tip;
        `feature/bimodal-cvc5-pilot` 19 on `cvc5-feasibility-test`'s tip; `refactor/exclusion` and
        `new_claude` no ancestor relation to the other eight. Note alongside the table why the raw
        `master..branch` counts (1978-2108) are not the real delta.
  - [ ] Record the archive absolute path `/home/benjamin/branch-archive/ModelChecker/` and the
        restore recipe, and cross-reference `bundle-manifest.md`.
  - [ ] Paste the verification evidence: the nine `git bundle verify` result lines, the post-
        deletion `git branch --list` output, and the `git branch -r | wc -l` count showing origin
        untouched.
  - [ ] State explicitly that no code was ported (nothing classified `(b)`), therefore no tests
        were added or run, and that no `git push`, no merge, and no remote mutation occurred.
  - [ ] Note the one open question carried forward: bimodal's `'solver': 'cvc5'` path is unverified
        end-to-end; it is now documented in `solver/README.md` under `## Known Issues` and is
        candidate work for a separate task.

- **Verification** (run from `/home/benjamin/Projects/ModelChecker`):
  - [ ] Summary exists:
        `test -f specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md`
  - [ ] All nine branch names appear in the summary (expect `9`):
        `grep -oE '(bimodal_refactor|feature/bimodal-cvc5-pilot|feature/bimodal_witness_backup|feature/bimodal_witness|feature/cvc5-feasibility-test|feature/quantifier-free-witnesses|feature/witness-falsity-attempt|new_claude|refactor/exclusion)' specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md | sort -u | wc -l`
  - [ ] Archive path recorded:
        `grep -q '/home/benjamin/branch-archive/ModelChecker' specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md`
  - [ ] Both durable documentation targets cited for the `(c)` findings (expect both to exit 0):
        `grep -q 'bimodal/docs/ARCHITECTURE.md' ...summary.md` and
        `grep -q 'solver/README.md' ...summary.md`
  - [ ] Bundle verification evidence present (expect at least `9`):
        `grep -c 'The bundle records a complete history\|is okay' specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md`

---

## Testing & Validation

This plan changes no source code and ports no code (no branch was classified `(b) reusable code`),
so there are no unit tests to add and no behavior to regression-test. Validation is documentation-
content checking and git-state checking, run as the per-phase verification commands above.

- [ ] Phase 1 and Phase 2 content assertions all pass (sections present, cited symbols exist in
      the tree, no task-number citations, no branch-name anchors).
- [ ] All nine bundles pass `git bundle verify` both before and after deletion.
- [ ] Each bundle's recorded head SHA equals the branch tip SHA captured before deletion.
- [ ] Post-deletion local branch set is exactly `{master, task-117-restore-model-checker,
      task-140-fix-bimodal-order-dependence}`.
- [ ] `git branch -r | wc -l` is `10` before and after, confirming origin untouched.
- [ ] `git rev-parse --abbrev-ref HEAD` is `task-140-fix-bimodal-order-dependence` throughout - the
      working tree was never switched.
- [ ] Repository-wide check that no task-number citation was introduced outside `specs/`:
      `grep -rnEi 'task [0-9]+' code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md code/src/model_checker/solver/README.md`
      returns nothing.
- [ ] Optional sanity run confirming the documentation edits did not disturb importable code (no
      code changed, so this must pass unchanged):
      `PYTHONPATH=code/src python -c "import model_checker.solver, model_checker.theory_lib.bimodal"`

## Artifacts & Outputs

- `specs/141_triage_stale_local_branches_and_salvage_value/plans/01_stale-branch-retirement.md` (this file)
- `specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md` (Phase 3)
- `specs/141_triage_stale_local_branches_and_salvage_value/summaries/01_stale-branch-retirement-summary.md` (Phase 5)
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - new `## Witness Predicate Design History` section (Phase 1)
- `code/src/model_checker/solver/README.md` - new `## Background: Why a cvc5 Backend` and `## Known Issues` sections (Phase 2)
- `/home/benjamin/branch-archive/ModelChecker/*.bundle` - nine verified bundles, outside the repository (Phase 3)

## Rollback/Contingency

- **Documentation edits (Phases 1-2)**: both files are tracked; revert with
  `git checkout HEAD -- <path>` only when the working tree has no other uncommitted change to that
  file, or by editing the section back out. Prefer committing each phase separately so a revert is
  a single-file, single-commit operation.
- **Branch deletion (Phase 4)**: fully reversible from the archive. Restore any branch with
  `git fetch /home/benjamin/branch-archive/ModelChecker/<file>.bundle refs/heads/<branch>:refs/heads/<branch>`.
  This is why Phase 3 bundles all nine regardless of verdict and why the Phase 4 gate blocks on
  bundle verification.
- **If Phase 3 cannot produce a verifying bundle for any branch**: stop. Do not proceed to Phase 4
  for any branch. Record the failure in the task artifacts, keep all nine branches, and report the
  blocker; partial deletion of the verifiable subset is not an acceptable fallback because it makes
  the verdict table's "all nine bundled" claim false.
- **If a phase needs to touch the working tree beyond the listed files**: run
  `bash .claude/scripts/git-snapshot.sh` first. The tree currently has uncommitted changes in
  `specs/TODO.md`, `specs/state.json`, and `specs/events.jsonl`; nothing in this plan should
  disturb them.
- **Never**: `git push` in any form, `git merge` of any stale branch, deletion of any `origin/*`
  ref, or `git branch -D` before the Phase 4 gate passes.
