# Blocker Analysis: Task #117

**Parent Task**: #117 - review_cli_pypi_parity_nix_flake_release
**Generated**: 2026-07-23
**Blocker**: The approved plan (`plans/01_restore-model-checker-release.md`) is a single 13-phase,
~30-hour, 9-wave implementation spanning git-history restoration, cross-API theory porting, a
package-identity rewrite, test-infrastructure repair, a Nix flake rewrite, documentation, and
release engineering. This is too large and too heterogeneous for one implementer dispatch to
execute reliably to a high quality bar; it needs to be decomposed into independently
research/plan/implement-able units that respect the plan's own dependency graph.

## Root Cause

Category: **Scope creep** (the plan itself documents 9 sequential/parallel dependency waves over
13 phases). The task was correctly researched and planned as a single task, but the plan's own
"Dependency Analysis" table (plan lines 143-155) shows 9 waves with phases that have materially
different risk profiles, tools, and verification criteria:

- Phases 1-2 are git/file mechanics (branch, baseline, relocate oracle).
- Phases 3-4 restore infrastructure from git history that is confirmed post-migration (low API
  risk) and wire up `logos`.
- Phases 5-6 are the highest-risk work: porting `exclusion` and `imposition` from a
  **pre-solver-migration** commit (`abb3bf7d^`) to the current `z3_shim`/`solver`/`models.*` API —
  explicitly called out in the plan's Risks section as High-Impact/High-Likelihood.
- Phases 7-8 are package-metadata and test-harness repair, gated on all theory restoration being
  registered.
- Phases 9-10 are verification/green-gate work requiring the relocated oracle and the full theory
  set.
- Phases 11-12 are infrastructure (Nix) and documentation, independent of each other but both
  gated on the green test gate.
- Phase 13 is release engineering, gated on both 11 and 12, and terminates in user-only actions
  (publish, push) per `pr-prohibition.md`.

No single phase is individually blocked by a missing prerequisite or external dependency — the
blocker is that the *plan as a whole* is too broad for one dispatch. The 8-task decomposition
below follows the plan's own wave boundaries exactly, so each new task is executable end-to-end
(research -> plan -> implement) without needing this conversation's context, and the original
plan's phase numbering and phase-level detail remain the authoritative reference for each task's
implementer.

## File Footprint Overlap Check (Component 4a)

Per `.claude/context/patterns/file-footprint-overlap.md`, a pairwise directory-prefix overlap scan
was run across all 8 tasks' `file_scope` arrays. Two overlaps were found; both are already
resolved by dependency edges that were derived independently from the plan's own wave structure
(no new edges were required):

- **Task 3 (exclusion/imposition) and Task 1 (core infra + logos)** both declare
  `code/src/model_checker/theory_lib/__init__.py` (theory registration). Task 3 already depends on
  Task 1 (`[1]`) for a separate, plan-derived reason (Phase 5 depends on Phase 3). Confirmed
  consistent — no new edge added.
- **Task 4 (cross-oracle differential + green gate) and Task 0 (bootstrap)** both declare
  `oracle/bimodal_logic`. Task 4 already depends on Task 0 (`[0, 3]`) for a separate, plan-derived
  reason (Phase 9 depends on Phase 2). Confirmed consistent — no new edge added.

No other pairs overlap. Task 6 (docs) intentionally excludes `code/MANIFEST.in` from its
`file_scope` even though its description mentions "cross-check" against Task 3's MANIFEST.in edit,
to avoid a spurious overlap edge; the description makes clear Task 6 reads/verifies but does not
re-edit that file.

## Proposed New Tasks

### New Task 1: Bootstrap — branch, baseline capture, and oracle relocation
- **Effort**: 3 hours
- **Task Type**: python
- **Covers**: Plan phases 1-2 of `specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md`
- **Rationale**: Every other task depends on a task branch existing and a documented before/after
  baseline; relocating the oracle out of the shipped package is a pure move that has no API risk
  and unblocks Phase 7's package-identity work (the wheel must exclude the oracle) as well as
  Phase 9's oracle-side differential testing.
- **Depends on**: None

### New Task 2: Restore core infrastructure and reconcile the logos theory
- **Effort**: 4.5 hours
- **Task Type**: python
- **Covers**: Plan phases 3-4
- **Rationale**: `builder/`, `iterate/`, `jupyter/`, and `output/manager.py`/`output/progress/`
  must exist before `logos` (which imports `model_checker.iterate`) can be reconciled and
  registered, and before any theory-registration work in later tasks can proceed.
- **Depends on**: New Task 1, because Phase 3 restores git-history paths onto the branch created
  in Phase 1 and needs the Phase 1 baseline/inventory of restore-point SHAs to select the correct
  `git checkout <sha>^ -- <path>` commands.

### New Task 3: Restore and port the exclusion and imposition theories
- **Effort**: 6 hours
- **Task Type**: python
- **Covers**: Plan phases 5-6
- **Rationale**: This is the highest-risk work in the plan (pre-solver-migration API porting,
  flagged High/High in the plan's Risks section). Isolating it as its own task lets the
  implementer focus exclusively on the exclusion/imposition port without also carrying
  infrastructure-restore or package-identity concerns, and lets a fresh agent devote its full
  budget to the two theories using `bimodal`/`logos` as the reference pattern.
- **Depends on**: New Task 2, because `exclusion`/`imposition` porting explicitly uses the
  restored, already-current-API `bimodal` and `logos` theories (Task 2's output) as the concrete
  reference pattern for the `z3_shim`/`solver`/`models.*` API shape being ported to, and because
  both theories register into the same `theory_lib/__init__.py` `AVAILABLE_THEORIES` table that
  Task 2 first touches for `logos`.

### New Task 4: Restore package identity and repair test infrastructure
- **Effort**: 3.5 hours
- **Task Type**: python
- **Covers**: Plan phases 7-8
- **Rationale**: `pyproject.toml`/`MANIFEST.in` can only be finalized once the full theory set
  (Phase 2's oracle exclusion, Phase 2/3's `logos`, Phase 3's `exclusion`/`imposition`) is known,
  and the pytest `testpaths` widening depends on the same set being registered and collectible.
- **Depends on**: New Task 1 (oracle relocation must be reflected in package-data
  include/exclude), New Task 2 (`logos` registration status), New Task 3 (`exclusion`/
  `imposition` registration status) — the plan's own table lists Phase 7 as blocked by phases
  2, 4, 6 and Phase 8 by phases 4, 6.

### New Task 5: Root-cause cross-oracle differential failures and establish the full green test gate
- **Effort**: 4 hours (plus Z3 solve wall-clock)
- **Task Type**: python
- **Covers**: Plan phases 9-10
- **Rationale**: Confirming the in-package `bimodal` suite is green without the external harness,
  and root-causing the relocated differential test's failures, requires the oracle already moved
  (Task 1) and the widened, collectible test suite (Task 4). The full green-gate run is the
  release baseline every downstream infra/doc/release task cites.
- **Depends on**: New Task 1 (oracle already relocated, so the differential harness runs in its
  new standalone context), New Task 4 (test infrastructure widened and collectible before a
  full-suite run is meaningful).

### New Task 6: Rewrite the Nix flake for multi-system build and test
- **Effort**: 2.5 hours
- **Task Type**: nix
- **Covers**: Plan phase 11
- **Rationale**: The flake's `checks.default` runs the canonical pytest suite, which must already
  be green (Task 5's output) to be a meaningful gate; the flake's `packages.default` build target
  depends on the final package identity (Task 4's `pyproject.toml`) but the plan's own table
  places Phase 11 behind Phase 10 specifically because the flake check is meant to validate the
  already-green suite, not discover new failures.
- **Depends on**: New Task 5, because the flake's `checks.default` pytest run is only meaningful
  against a test suite already confirmed green — running it earlier would conflate flake bugs
  with unresolved theory-porting bugs.

### New Task 7: Documentation refresh
- **Effort**: 2 hours
- **Task Type**: markdown
- **Covers**: Plan phase 12
- **Rationale**: Docs must describe the final restored theory set, the relocated oracle, and the
  actual (post-Task-4) component list; writing docs before the green gate risks describing
  not-yet-working functionality as working. Independent of the Nix flake (Task 6) — both are
  gated only on Phase 10's green gate, not on each other.
- **Depends on**: New Task 5, because Phase 12's doc content (theory list, component table,
  restored-vs-relocated module descriptions) must reflect the definitive, green-gated state Task 5
  establishes, not an in-progress state that could still change.

### New Task 8: Release engineering and rehearsal
- **Effort**: 2.5 hours
- **Task Type**: general
- **Covers**: Plan phase 13
- **Rationale**: The release checklist and TestPyPI rehearsal need both the Nix-verified build
  (Task 6, confirming `nix build`/`nix flake check` succeed against the final package) and the
  refreshed docs/CHANGELOG (Task 7) before a coherent, user-facing release checklist can be
  written. Terminates in user-only actions (PyPI publish, `git push`) per `pr-prohibition.md` —
  this task prepares the checklist but does not execute those steps.
- **Depends on**: New Task 6, because the wheel-content parity diff and `check-wheel-contents`
  rehearsal need the flake-verified `packages.default` build target as ground truth for what a
  clean build looks like. New Task 7, because the release checklist references the refreshed
  `CHANGELOG.md` entry and doc state as part of what ships.

## Dependency Reasoning

- **Task 2 depends on Task 1**: Task 2 executes `git checkout <sha>^ -- <path>` restores that
  require the task branch (created in Task 1's Phase 1) to exist, and uses Task 1's inventory of
  confirmed restore-point SHAs (`013a486c^`, `c21b3709^`, `71ef79a1^`) rather than re-deriving
  them.
- **Task 3 depends on Task 2**: Task 3's exclusion/imposition API port is a direct copy-the-pattern
  exercise against `bimodal`/`logos` as already-ported reference implementations — those
  implementations are Task 2's output, not merely a completed prerequisite. Task 3 also appends to
  the same `AVAILABLE_THEORIES` table Task 2 first modifies for `logos`.
- **Task 4 depends on Task 1, Task 2, Task 3**: `pyproject.toml`'s package-data include/exclude
  list and `MANIFEST.in` can only be written once the final theory/oracle layout is known — which
  theories are registered (Task 2, Task 3) and where the oracle now lives (Task 1). This mirrors
  the plan's explicit Phase 7 dependency on phases 2, 4, 6.
- **Task 5 depends on Task 1, Task 4**: The relocated oracle (Task 1) must exist in its new
  location before the differential harness can be root-caused there, and the widened test
  collection (Task 4) must be in place before a "full green test gate" claim is meaningful.
- **Task 6 depends on Task 5**: The flake's `checks.default` target is defined as "run the
  canonical pytest suite" — it is only useful as a reproducibility gate once that suite is known
  to be green from Task 5; running it against a red suite would just duplicate Task 5's failures
  inside Nix rather than validating build reproducibility.
- **Task 7 depends on Task 5**: Doc content (theory list, component descriptions) must describe
  the definitive post-green-gate state, not an in-progress one that could still change during
  Task 3/4/5's work.
- **Task 6 and Task 7 are independent**: both depend only on Task 5's green gate; the Nix flake
  (build/CI infra) and the documentation (prose) touch disjoint files and neither's implementation
  choices affect the other's.
- **Task 8 depends on Task 6, Task 7**: the release rehearsal's wheel-content parity check needs
  the flake-verified build (Task 6) as its comparison baseline, and the publish checklist narrates
  the refreshed CHANGELOG/docs (Task 7) as part of what is being released.

## After Completion

Once all 8 spawned tasks are complete, resume the parent task #117 — there is no remaining work
under #117 itself once the spawned tasks finish; the parent task can be marked complete once Task
8's user-gated release checklist is handed to the user. If any residual verification is desired at
the parent level, run `/implement 117` to confirm the plan's own Testing & Validation checklist
against the final state.

The blocker will be resolved because: each of the 8 tasks is independently research/plan/
implement-able in a single dispatch, respects the plan's own 9-wave dependency structure exactly
(so no phase runs before its prerequisites are satisfied), and preserves every scope decision the
user already made (bimodal stays as a theory; oracle/harness moves to standalone `oracle/`,
excluded from the wheel; exclusion is restored; the first-order removal from logos is preserved;
PyPI publish and `git push` remain user-only gated steps in Task 8).
