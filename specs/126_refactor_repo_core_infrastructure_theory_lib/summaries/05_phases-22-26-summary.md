# Implementation Summary: Task #126 (Phases 22-26, final)

**Completed**: 2026-07-24
**Duration**: single continuation session, resumed at 21/26 phases

## Overview

Completed the final five phases of the core/theory_lib refactor: restored bimodal's missing
`iterate.py` (closing the plan's last theory-contract gap), flipped the conformance and layering
tests fully green with a permanent zero-xfail guard, reconciled documentation across `docs/`,
`code/docs/`, and `theory_lib/docs/` with the enforced reality, ran the full regression gate and
wheel parity diff as final acceptance evidence, and recorded the refactor's durable decisions in
`specs/ROADMAP.md`. 25 of 26 phases are now `[COMPLETED]`; Phase 2 remains `[PARTIAL]` per its
already-documented, accepted sandbox constraint (no `pytest-xdist`, resource contention blocks a
full serial 550-test oracle run) -- unchanged by this session and not attempted again per explicit
instruction.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/iterate.py` -- restored via `git show
  9b76ffa2^:...iterate.py` and ported to the current `iterate_example_generator` convention using
  `imposition/iterate.py` as the template. Fixed a genuine bug in the restored source's
  `_create_difference_constraint` (referenced `semantics.W`/`semantics.T`/
  `semantics.world_history[w][t]`, none of which exist on the current `BimodalSemantics`) by
  rewriting it against real attributes (`world_function`, `max_world_id`, `M`). Confirmed via
  `iterate/iterator.py`/`core.py` that this method is dead code in the active search path (the
  loop always excludes previous models via the shared `ConstraintGenerator` in
  `iterate/constraints.py`), documented in both the module and `ITERATE.md`.
- `code/src/model_checker/theory_lib/bimodal/__init__.py` -- re-exports `BimodalModelIterator`,
  `iterate_example`, `iterate_example_generator`.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` -- new, written
  fresh (not restored from the old 156-line Mock-heavy version). 7 tests: 4 mock-based unit-style
  tests plus 3 real (non-mocked) functional tests building an actual `BuildExample` with bimodal
  theory and exercising `iterate_example`/`iterate_example_generator` end to end.
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` -- reconciled with the restored
  module (fixed `iterator.iteration_count`/`isomorphic_count` to the real
  `checked_model_count`/`isomorphic_model_count`; rewrote the "Advanced Topics" section, which
  incorrectly described the theory-specific difference/isomorphism methods as driving search-time
  model diversity).
- `code/tests/e2e/test_project_creation.py` -- theory parametrization extended from `['bimodal']`
  to all four theories.
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` -- emptied
  `ITERATE_MODULE_XFAIL_REASON` (bimodal's entry); added `TestZeroXfailGuard` (two tests: no
  `XFAIL_REASON` dict is ever re-populated, and `discover_theories()` reports zero registry
  drift). All 50 tests pass, zero xfail.
- Documentation reconciliation (16 files): `theory_lib/docs/CONTRIBUTING.md`, six module test
  READMEs (settings/models/syntactic/utils/output/builder), four per-theory `docs/ARCHITECTURE.md`
  files (logos, bimodal, exclusion, imposition), and stale `semantic.py`-as-bare-file links across
  `docs/architecture/SEMANTICS.md`, `docs/architecture/SETTINGS.md`, `docs/usage/SEMANTICS.md`, and
  `code/docs/standards/AUDIENCE.md`. `CLAUDE.md` (gitignored, on-disk only) corrected too.
- `code/tests/integration/test_system_imports.py` -- fixed a genuine, previously-undetected
  regression from an earlier phase (Phase 12's core/upper-layer split): `test_theory_components`
  called the now-pure `utils.api.get_theory(name)` with a single argument, relying on auto-load
  behavior that phase 12 correctly moved to `model_checker.api.get_theory`. Updated the call site.
- `code/src/model_checker/theory_lib/exclusion/semantic/{core,constraints,registry,model}.py` and
  `imposition/semantic/{core,helpers}.py` -- fixed the scaffolded-project relative-import depth
  defect Phase 20's summary already identified and deliberately deferred (3-dot relative imports
  only resolve at the exact `theory_lib.{theory}.semantic.{file}` nesting depth, one level deeper
  than a `BuildProject`-scaffolded project). Converted each to its absolute form, mirroring
  bimodal's own Phase 20 fix. Phase 25's "scaffold and run" verification step made this an
  acceptance blocker, not merely a documented gap.
- `specs/ROADMAP.md` -- two new Durable Decisions (enforced three-layer model; theory_lib
  extraction REJECTED for now, with revisit trigger), the "Merge and publish 1.3.0" priority
  rewritten (not merely checked off) to record refactor-first sequencing, a new Deferred Items
  section, and Success Metrics replacing the placeholder.
- `specs/126_.../baselines/post-refactor/` -- six new files: collection counts, scaffold+CLI-smoke
  results, the final `verify-refactor.sh` run, and the wheel contents plus both diffs (vs the
  Phase 2 baseline and vs task 125's rehearsal manifest).

## Decisions

- Left `BimodalModelIterator._create_difference_constraint` / `_create_non_isomorphic_constraint`
  / `_create_stronger_constraint` in place for interface parity with the other three theories even
  though confirmed dead code in the active search path, matching the existing convention rather
  than special-casing bimodal.
- `bimodal/tests/integration/test_iterate.py`'s real functional tests treat "zero additional
  models found within the timeout budget" as a legitimate outcome (soft-asserted), not a failure:
  bimodal's heavier frame constraints make the generic `is_world`-keyed difference constraint
  slower to satisfy than for the flatter state-based theories, and the property actually being
  guarded is that the mechanism runs without `ImportError`, not that Z3 finds a second model
  within an arbitrary budget.
- Fixed two regressions discovered by broader test sweeps than any single prior phase ran
  (`test_system_imports.py`'s stale `utils.api.get_theory` call site, and the exclusion/imposition
  scaffolded-project relative-import defect) even though neither was named in Phases 22-26's
  original file lists, because both are genuine task-126-introduced or task-126-blocking defects
  discovered while executing this session's own verification work, not pre-existing gaps.
- Did not chase pre-existing, unrelated broken markdown links found incidentally in
  `docs/architecture/SEMANTICS.md` and `code/docs/standards/AUDIENCE.md` (`model.py`,
  `syntactic.py`, `logos/registry.py`, etc. -- artifacts of a pre-src-layout repository structure)
  since they predate task 126 and are outside Phase 24's stated scope.

## Plan Deviations

- **Task 25** (oracle suite full run): deviation, consistent with Phases 2/21/23 -- the full
  serial 550-test oracle run was not attempted per explicit instruction and the documented
  `pytest-xdist`/resource-contention sandbox constraint. `verify-refactor.sh --skip-oracle`
  substituted; collection count and xfail line locations independently re-verified.
- **Task 25** (scaffold exclusion/imposition): altered -- discovered a real defect during this
  verification step (not merely re-confirmed a known one) and fixed it in-phase rather than
  merely documenting it, since Phase 25's own acceptance criteria required all four theories to
  succeed.
- Additional deviation beyond any single phase's task list: fixed
  `code/tests/integration/test_system_imports.py`'s stale `utils.api.get_theory` call site
  (Phase-12-introduced regression, discovered via a broader sweep than prior phases ran).

## Verification

- Build: N/A (no compiled artifacts beyond the wheel, see below)
- Tests: `verify-refactor.sh --skip-oracle` passes at every checkpoint through this session's end
  (final run: 298 bimodal / 2175 full / 550 oracle-collection-only, 0 regressions via
  `compare_bimodal_baseline.sh`). Full theory_lib + layering + builder + `code/tests/` sweep:
  1310+ passed with only the already-documented 9 pre-existing failures (7 originally briefed +
  `test_bimodal_batch_output`, confirmed pre-existing and already tracked in `specs/ROADMAP.md`'s
  "28 documented everything-else failures" item, + the two this session fixed). Wheel built with
  `python -m build --wheel --no-isolation` and diffed clean against both reference manifests.
- Files verified: Yes -- all four theories scaffold via `BuildProject` and run their `examples.py`
  to completion via the `model-checker` CLI; `--maximize` and `--save markdown` both smoke-tested
  successfully.

## Notes

Three test failures this session's broader sweeps surfaced were independently confirmed
pre-existing and unrelated to task 126 (via `git diff` over the whole task-126 commit range on
the relevant source files, returning empty): `test_attribute_initialization_order`
(`unittest.mock`'s `assert_*`-prefix safety check tripping on `assert_and_track`, Category E in
`specs/ROADMAP.md`'s existing 28-failures tracking), the 5 `test_timeout_resources.py` tests
(sandbox CPU-contention timing flakes), and `test_bimodal_batch_output` (a malformed `"A[]"`
formula literal, already named in `specs/ROADMAP.md`'s Category B/G). All three were already
recorded in `specs/ROADMAP.md`'s pre-existing follow-up item before this session began,
confirming these are known, tracked gaps rather than new discoveries requiring fresh tracking.
