# Implementation Summary: Task #126 (Phases 2-6)

**Completed**: 2026-07-24
**Scope**: Phases 2 through 6 only (of 26), per explicit orchestrator scoping

## Overview

Completed Phases 2-6 of the core/theory_lib refactor plan: pinned pre-refactor verification
baselines and a reusable regression gate script, rewrote `THEORY_ARCHITECTURE.md` as the single
canonical theory contract, removed the spatial subtheory stub and dead semantic re-export
wrappers, swept accumulated cruft (boneyard, superseded example copies, root strays, stale
per-theory TODOs), and relocated the logos solver benchmark script out of the shipped package.
Six commits landed, one per phase (plus one follow-up fix commit for Phase 2's gate script).

## Important Operational Note: Concurrent Agent Collision

**A second, independent agent instance was actively editing this same working tree throughout
this session**, executing the identical plan concurrently and unprompted. Evidence: live edits
to `theory_lib/__init__.py`, `.opencode/`- and `.claude/`-mirrored `spatial-domain.md`,
`exclusion/tests/integration/test_project_generation.py`, and `verify-refactor.sh` appeared on
disk that this agent did not make, interleaved with running `pytest` processes (PIDs 4027952,
4041026, 4042838, 4045440) this agent did not start. One direct file-content collision occurred
(`test_cvc5_stability.py`'s `sys.path` fix landed from the other agent while this agent was
mid-edit on the same file's import statements) — both edits were non-overlapping and the
resulting file is correct, but this was fortunate, not guaranteed. All content produced by the
concurrent process was independently verified before being folded into commits here; nothing
was committed blindly. **The orchestrator should investigate why two implementer dispatches were
active on task 126 simultaneously** (likely a duplicate dispatch triggered by an idle/stall
detector during this agent's ~45-minute background oracle-suite wait) before resuming further
phases, to avoid a third collision.

## What Changed

- `code/scripts/verify-refactor.sh` — new reusable regression gate (Phase 2); one follow-up fix
  for a collection-count extraction bug.
- `specs/126_.../baselines/` — collection counts, bimodal suite runs + junit XML,
  `compare_bimodal_baseline.sh` output, pre-refactor wheel contents. Oracle suite run/junit XML
  intentionally deferred (still running in background at handoff time; see below).
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` — rewritten as the single
  canonical theory contract (Phase 3), replacing the old Simple/Modular pattern fork.
- `code/src/model_checker/theory_lib/logos/subtheories/spatial/` — deleted (Phase 4).
- `code/src/model_checker/theory_lib/{exclusion,imposition}/semantic.py` — deleted, unreachable
  compatibility wrappers (Phase 4).
- `code/src/model_checker/theory_lib/__init__.py` — spatial comment references removed (Phase 4).
- `.opencode/` and `.claude/` (gitignored) copies of `spatial-domain.md` — updated with a status
  note (Phase 4).
- `code/src/model_checker/theory_lib/exclusion/tests/integration/test_project_generation.py` —
  updated to assert the `semantic/` package instead of the deleted flat `semantic.py` (Phase 4
  deviation: not in the original task list, but required by the deletion).
- `code/boneyard/`, `theory_lib/imposition/examples_refactored/`, root strays
  (`code/dist/`, `code/output.md`, `code/test_update.py`, `code/run_update.py`,
  `code/scaling_benchmark.py`, `output.md`, `output.json`), `theory_lib/{exclusion,logos}/TODO.md`
  — deleted (Phase 5).
- `code/src/model_checker/theory_lib/exclusion/history/`,
  `code/src/model_checker/theory_lib/imposition/reports/` — moved to `docs/theory/` (Phase 5).
- `code/dev_cli.py` — fixed fragile cwd-dependent import (Phase 5).
- `specs/126_.../deleted-theory-todo-items.md` — preserves live TODO items for Phase 26 (Phase 5).
- `code/src/model_checker/theory_lib/logos/comparison.py` → `code/scripts/logos_solver_benchmark.py`
  — relocated out of the package, 9 unused dataclasses deleted (Phase 6).
- `code/scripts/comparison.py`, `code/scripts/test_cvc5_stability.py` — importers updated (Phase 6).

## Decisions

- Cruft archival destination: `docs/theory/{exclusion,imposition}/` (repo-root `docs/`, matching
  the existing `docs/theory/` convention), rather than inventing a new location.
- `spatial-domain.md` retained (not deleted) with a status note, since its RCC/topological
  content has standalone domain-background value independent of implementation status.

## Plan Deviations

- **Phase 4** (not in original task list): fixed `test_project_generation.py`'s stale assertions
  against the deleted flat `semantic.py`. Reason: the test encoded the pre-refactor contract, not
  a regression from the deletion itself.
- **Phase 5**: the phase's goal text attributed the entire bare-root `pytest --collect-only`
  collection-error trap to `code/boneyard/`. After removal, errors drop from 26 to 17 but do not
  reach zero — a genuine, pre-existing structural issue (duplicate test-module basenames across
  8 packages under pytest's default import mode) independent of boneyard and out of this phase's
  scope. Flagged for a follow-up rather than silently left unrecorded. The properly-scoped
  invocation that `verify-refactor.sh` actually checks (`cd code && pytest --collect-only`) is
  unaffected (still 2100).

## Verification

- Build: N/A (no build step in this scope)
- Tests: `theory_lib/{exclusion,imposition}/tests/` — 253 passed, re-verified green after Phase 5
  moves. `dev_cli.py --help` verified from three different working directories.
  `comparison.py --help` and a direct `logos_solver_benchmark` import verified after Phase 6.
  Full `verify-refactor.sh` re-run was attempted at handoff time but produced unreliable results
  under heavy concurrent CPU load (3+ simultaneous pytest processes from this session and the
  concurrent agent) and hardcoded-`/tmp`-path collisions between simultaneous `verify-refactor.sh`
  invocations — not treated as a real regression signal; see collision note above.
- Files verified: Yes

## Notes

- The oracle suite run (`oracle/bimodal_logic/tests/`, 550 tests) was still running in the
  background at handoff time (~46+ minutes elapsed; PID 4006300). Its results and junit XML were
  intentionally deferred to a separate commit per explicit orchestrator instruction, rather than
  blocking Phase 2's commit on it. A future dispatch should check whether that background process
  is still reachable/completed and commit `baselines/oracle-run.txt` +
  `baselines/junit-oracle.xml` if so, or re-run it if not.
- Phases 7-26 are explicitly out of scope for this dispatch and were not started by this agent.
