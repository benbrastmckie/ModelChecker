# Implementation Plan: Documentation Refresh for the Restored Framework

- **Task**: 124 - documentation_refresh_for_the_restored_framework
- **Status**: [IMPLEMENTING]
- **Effort**: 2.25 hours
- **Dependencies**: The full green test gate and release baseline are established (see `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/RELEASE-BASELINE.md`); this task consumes that definitive state as ground truth.
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md; parent plan phase 12 (specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md)
- **Artifacts**: plans/01_docs-refresh.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; no-task-references-in-deliverables.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Refresh all user-facing documentation so it describes the definitive, working state of the
restored ModelChecker framework rather than an in-progress restoration. The framework now ships
four registered theories (logos, exclusion, imposition, bimodal), keeps the differential oracle
in a standalone top-level `oracle/` tree excluded from the wheel, has removed first-order
quantification from logos, and has restored the `builder`/`iterate` infrastructure — all
confirmed by a full green test gate. This task corrects concrete documentation defects (path
casing, dead links, stale first-order references, an empty CHANGELOG release entry, an empty
ROADMAP), aligns the theory/component descriptions across seven files, and seeds the durable
identity decision. Definition of done: every file in scope describes the restored state
accurately, no dead links remain, and no deliverable cites an ephemeral task number.

### Research Integration

The spawn-analysis report (task #117 decomposition) establishes that this documentation work is
gated on the green test gate specifically so docs describe the definitive theory list, component
layout, and restored-vs-relocated module descriptions rather than a state that could still
change. The report also notes this task reads/verifies but does **not** re-edit `code/MANIFEST.in`
(that file is owned by the package-identity task); the MANIFEST cross-check here is read-only.
Parent plan phase 12 enumerates the specific per-file defects addressed below.

### Prior Plan Reference

No prior plan for this task. The parent plan's phase 12 ("Documentation Refresh") supplies the
per-file defect checklist and is the authoritative reference; it is not copied verbatim — its
seven bullet items are regrouped here into dependency-ordered phases.

### Roadmap Alignment

`specs/ROADMAP.md` currently exists but is an empty template (placeholder items only). Phase 12
of the parent plan lists seeding the ROADMAP with the durable package-identity decision as a
non-blocking task; Phase 5 below performs that seeding. No `roadmap_flag` was set for this
dispatch, so no roadmap review/update wrapper phases are added.

## Goals & Non-Goals

**Goals**:
- Correct all confirmed documentation defects: `cd Code` / `cd ModelChecker/Code` casing, the
  dead `docs/theory/QUANTIFIER_SOLVERS.md` link, and the `jupyter[...]` quick-start / dead
  `jupyter/README.md` link in the root README.
- Make the theory list and component descriptions honest across README.md, code/README.md, and
  CLAUDE.md: four registered theories, restored `builder`/`iterate`, and the relocated oracle.
- Add an honest CHANGELOG release entry (identity restore, theory set, first-order removal,
  oracle relocation).
- Remove stale first-order / quantifier references from `docs/usage/SEMANTICS.md`.
- Seed `specs/ROADMAP.md` with the durable package-identity decision.
- Ensure every edited deliverable references durable anchors, never task numbers.

**Non-Goals**:
- Editing `code/MANIFEST.in` (read-only cross-check only; owned by the package-identity task).
- Any Nix flake or release-pipeline documentation (separate tasks).
- Restructuring or rewriting docs beyond the accuracy corrections in scope.
- Changing source code, tests, or packaging metadata.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A doc edit cites a task number, violating the deliverables rule | M | M | Phase 1 fixes the durable-anchor vocabulary up front; Phase 6 greps every edited file for `task \d` / `task-\d` patterns before completion. |
| Theory list or component description asserts something not actually registered/present | H | L | Phase 1 verifies the registered theory set (`AVAILABLE_THEORIES`) and on-disk component layout before any prose is written. |
| A "fixed" link points to another non-existent path | M | M | Phase 6 validates every relative link touched resolves to a real file on disk. |
| SEMANTICS.md edit removes a legitimate "first-order formula" reference (Z3 constraint language, not removed logos quantifiers) | M | M | Phase 4 distinguishes Z3-constraint first-order language (keep) from removed-logos first-order quantification (remove); each hit is classified before editing. |
| Root `CLAUDE.md` edit confused with auto-generated `.claude/CLAUDE.md` | H | L | Scope is the repo-root `CLAUDE.md` only; the `.claude/CLAUDE.md` is auto-generated and out of scope — Phase 2 edits only `./CLAUDE.md`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5 | 1 |
| 3 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

### Phase 1: Establish definitive-state reference [COMPLETED]

- **Goal:** Gather the ground-truth facts every subsequent doc edit depends on, and fix the
  durable-anchor vocabulary so no edit needs to reach for a task number.
- **Tasks:**
  - [x] Confirm the registered theory set from `code/src/model_checker/theory_lib/__init__.py`
        (`AVAILABLE_THEORIES`): expect logos, exclusion, imposition, bimodal. *(completed:
        confirmed `AVAILABLE_THEORIES = ['bimodal', 'logos', 'exclusion', 'imposition']`)*
  - [x] Confirm the restored component layout on disk: `builder/`, `iterate/`, `jupyter/`,
        `output/manager.py`, `output/progress/` present under `code/src/model_checker/`.
        *(completed: all present)*
  - [x] Confirm the oracle lives in a standalone top-level `oracle/` tree (not inside the shipped
        package) and is excluded from the wheel. *(completed: `./oracle` is top-level, outside
        `code/src/`; `[tool.setuptools.packages.find] where = ["src"]` in `code/pyproject.toml`
        naturally excludes it)*
  - [x] Read-only cross-check `code/MANIFEST.in` includes against real paths; note any mismatch
        for the package-identity task but do NOT edit MANIFEST.in. *(completed: no mismatch —
        MANIFEST.in only references `src/*` paths, none touch `oracle/`; not modified)*
  - [x] Confirm logos no longer exposes first-order quantification (source of the removal
        described in the CHANGELOG and SEMANTICS edits). *(completed: logos subtheories are
        constitutive, counterfactual, extensional, modal, relevance, spatial — no quantifier
        subtheory; no "quantifier" hits in non-test logos source)*
  - [x] Record the durable anchors to be used in all edits (e.g., "the framework restoration",
        "the four registered theories", "the standalone `oracle/` differential tree", "the
        first-order removal from logos") — no task-number references. *(completed: anchors
        recorded and used throughout Phases 2-5)*
- **Timing:** 20 minutes
- **Depends on:** none
- **Files to modify:** none (read/verify only)
- **Verification:** A short internal fact sheet exists covering the theory set, component layout,
  oracle location, and MANIFEST status; each fact traced to a file on disk.

### Phase 2: Refresh root entry docs (README.md, CLAUDE.md) [COMPLETED]

- **Goal:** Make the two top-level entry documents honest and free of dead links.
- **Tasks:**
  - [x] `README.md`: fix the `pip install model-checker[jupyter]` quick-start and the dead link
        to `code/src/model_checker/jupyter/README.md`; ensure the four-theory framing matches the
        Phase 1 registered set. *(completed: both the `[jupyter]` extra and the link already
        resolved correctly — verified, no change needed; also fixed a stale "19 operators"
        count to the verified "18 operators" in two places, and repointed four other dead
        relative links discovered in the same file — code/docs/DEVELOPMENT.md (x2),
        docs/architecture/ARCHITECTURE.md, code/MAINTENANCE.md (x2), and the logos notebooks
        link — to their existing on-disk equivalents)*
  - [x] `README.md`: verify the theory bullets (logos, exclusion, imposition, bimodal) and any
        component references match the restored state. *(completed: matches
        `AVAILABLE_THEORIES`)*
  - [x] `CLAUDE.md` (repo root only — NOT `.claude/CLAUDE.md`): fix `cd Code` -> `cd code`
        casing; reconcile the canonical test command(s) and architecture/component description
        with reality (restored `builder`/`iterate`, relocated oracle). *(completed: fixed both
        `cd Code` casing occurrences, corrected the stale "Main Repository" path, and added the
        standalone `oracle/` tree to the Project Structure diagram; `builder`/`iterate` were
        already listed under Key Packages)*
  - [x] Ensure all provenance language uses durable anchors, not task numbers. *(completed: no
        task-number citations introduced)*
- **Timing:** 30 minutes
- **Depends on:** 1
- **Files to modify:**
  - `README.md` - jupyter quick-start, dead jupyter link, theory framing
  - `CLAUDE.md` - path casing, test command, architecture description
- **Verification:** No `cd Code` remains in `CLAUDE.md`; the jupyter link resolves or is removed;
  theory list matches Phase 1; no `task N` citations.

### Phase 3: Refresh package and scripts docs (code/README.md, code/scripts/README.md) [COMPLETED]

- **Goal:** Align the package-level docs with the restored component layout and remove the dead
  scripts link.
- **Tasks:**
  - [x] `code/README.md`: fix `cd ModelChecker/Code` casing to `cd code`; update the component
        table/description to reflect restored `builder`/`iterate` and the relocated oracle.
        *(completed: fixed the casing; the file has no dedicated component table and does not
        assert anything false about builder/iterate/oracle — its existing `run_tests.py iterate
        builder` example already correctly implies both are present, so no additional prose was
        added, consistent with the non-goal against restructuring beyond accuracy corrections.
        Also fixed a stale "19 operators" count to "18", and repointed two dead
        `github.com/.../blob/master/...` links — `docs/usage/COMPARE_THEORIES.md` (never
        existed) to `docs/usage/TOOLS.md`, and `docs/DEVELOPMENT.md` to
        `code/docs/development/README.md` — both discovered via the same link-scan used in
        Phase 2)*
  - [x] `code/README.md`: confirm the theory descriptions match the four registered theories.
        *(completed: matches)*
  - [x] `code/scripts/README.md`: fix the dead link to the deleted
        `../../docs/theory/QUANTIFIER_SOLVERS.md` (remove it or repoint to a live doc; do not
        recreate the deleted file). *(deviation: skipped — verified `docs/theory/QUANTIFIER_SOLVERS.md`
        exists on disk (592 lines, substantive content) and the relative link already resolves
        correctly; the file is no longer deleted as of this dispatch, so no edit was needed)*
  - [x] Ensure durable-anchor provenance language only. *(completed: no task-number citations)*
- **Timing:** 25 minutes
- **Depends on:** 1
- **Files to modify:**
  - `code/README.md` - path casing, component table, theory descriptions
  - `code/scripts/README.md` - dead QUANTIFIER_SOLVERS link
- **Verification:** No `cd ModelChecker/Code` remains; the QUANTIFIER_SOLVERS link is gone or
  repointed to an existing file; component table lists restored `builder`/`iterate` and the
  standalone oracle.

### Phase 4: Refresh semantics usage doc (docs/usage/SEMANTICS.md) [NOT STARTED]

- **Goal:** Remove stale first-order / quantifier references that no longer describe logos, while
  preserving legitimate Z3-constraint "first-order formula" language.
- **Tasks:**
  - [ ] Enumerate every first-order / quantifier / `forall` / `exists` reference in
        `docs/usage/SEMANTICS.md`.
  - [ ] Classify each: Z3-constraint-language usage (keep) vs. removed-logos first-order
        quantification (remove or correct).
  - [ ] Edit only the stale removed-logos references; leave accurate Z3-constraint descriptions
        intact.
- **Timing:** 20 minutes
- **Depends on:** 1
- **Files to modify:**
  - `docs/usage/SEMANTICS.md` - stale first-order references
- **Verification:** No reference implies logos still supports first-order quantification;
  Z3-constraint first-order language preserved where accurate.

### Phase 5: Add CHANGELOG release entry and seed ROADMAP [NOT STARTED]

- **Goal:** Record the release honestly in the changelog and capture the durable identity
  decision in the roadmap.
- **Tasks:**
  - [ ] `code/CHANGELOG.md`: add an honest entry for this release covering the package-identity
        restore, the four-theory set, the first-order removal from logos, and the oracle
        relocation to a standalone tree. Follow the existing Keep-a-Changelog structure. Reference
        durable anchors, not task numbers.
  - [ ] `specs/ROADMAP.md`: seed the durable package-identity decision (framework ships as
        `model_checker` with the four registered theories; oracle kept standalone/unpacked),
        replacing the placeholder items. This is a non-blocking addition.
- **Timing:** 20 minutes
- **Depends on:** 1
- **Files to modify:**
  - `code/CHANGELOG.md` - release entry
  - `specs/ROADMAP.md` - durable identity decision
- **Verification:** CHANGELOG has a coherent release entry naming the theory set / oracle
  relocation / first-order removal with no task-number citations; ROADMAP records the identity
  decision.

### Phase 6: Cross-reference and link validation [NOT STARTED]

- **Goal:** Confirm consistency across all edited files and that no dead link or task-number
  citation was introduced.
- **Tasks:**
  - [ ] Grep every edited file outside `specs/**` for `task \d` / `task-\d` citation patterns;
        replace any with durable anchors. (`specs/ROADMAP.md` is under `specs/` but should still
        avoid task numbers for durability.)
  - [ ] Validate every relative link touched or referenced resolves to a real file on disk
        (jupyter link, QUANTIFIER_SOLVERS removal, any component links).
  - [ ] Confirm the theory list and component descriptions agree across README.md,
        code/README.md, and CLAUDE.md.
- **Timing:** 20 minutes
- **Depends on:** 2, 3, 4, 5
- **Files to modify:** minor corrections only in already-touched files, if inconsistencies found
- **Verification:** Zero dead relative links in edited files; zero `task N` citations in
  deliverables; theory/component descriptions consistent across the three top-level docs.

## Testing & Validation

- [ ] No `cd Code` or `cd ModelChecker/Code` string remains in `CLAUDE.md` or `code/README.md`.
- [ ] The dead `docs/theory/QUANTIFIER_SOLVERS.md` link is removed/repointed in
      `code/scripts/README.md`; the target of any replacement exists.
- [ ] The root README jupyter quick-start and jupyter link are corrected (link resolves or is
      removed).
- [ ] Theory list (logos, exclusion, imposition, bimodal) is consistent across README.md,
      code/README.md, and CLAUDE.md and matches `AVAILABLE_THEORIES`.
- [ ] `code/CHANGELOG.md` has an honest release entry covering identity restore, theory set,
      first-order removal, and oracle relocation.
- [ ] `specs/ROADMAP.md` records the durable package-identity decision.
- [ ] `grep -rnE 'task[ -][0-9]+' README.md code/README.md CLAUDE.md code/CHANGELOG.md docs/usage/SEMANTICS.md code/scripts/README.md` returns no citation-style matches.
- [ ] `code/MANIFEST.in` was not modified by this task.

## Artifacts & Outputs

- plans/01_docs-refresh.md (this file)
- summaries/01_docs-refresh-summary.md (on completion)
- Edited docs: README.md, CLAUDE.md, code/README.md, code/scripts/README.md,
  docs/usage/SEMANTICS.md, code/CHANGELOG.md, specs/ROADMAP.md

## Rollback/Contingency

All changes are documentation-only and confined to seven tracked files. If any edit proves
incorrect, revert the individual file via `git checkout -- <path>` from a clean baseline (or
restore from the pre-edit commit). No source, test, or packaging state is touched, so there is
no build or test regression surface to unwind. If the registered theory set or component layout
turns out to differ from Phase 1's findings, halt and re-verify against
`code/src/model_checker/theory_lib/__init__.py` before continuing, since every prose edit depends
on that ground truth.
