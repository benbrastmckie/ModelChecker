# Teammate C Findings (Critic): Task 126 — Refactor Repo into Core Infrastructure + theory_lib

**Task**: 126 - Systematically refactor the ModelChecker repo (core vs theory_lib, remove spatial subtheory)
**Role**: Critic — gaps, unvalidated assumptions, blind spots in the research effort
**Date**: 2026-07-24
**Branch context**: `task-117-restore-model-checker` (51 commits ahead of `master`, zero commits behind; nothing merged)

## Key Findings

### F1. The task description rests on a false premise: theory_lib is ALREADY inside src/

The task says "If it makes more sense, move theory_lib/ into src/". It is already there:
`code/src/model_checker/theory_lib/` (bimodal, exclusion, imposition, logos). Any researcher who
takes the description at face value will design a no-op or, worse, will reinterpret it as "split
theory_lib into a sibling top-level package `src/theory_lib/`" — which is a **breaking public API
change** (`model_checker.theory_lib.logos` → `theory_lib.logos`) for a package that:

- is named `model-checker`, version `1.3.0` on PyPI (code/pyproject.toml:6,9);
- just had release engineering, OIDC trusted publishing, and a NixOS build rehearsal completed
  (tasks 123/125, commits 9754db81, 45b28c88);
- has 49 docs files referencing `src/model_checker` paths and 51 referencing `theory_lib`,
  refreshed only days ago in task 124.

**The single most important unasked question**: does "core vs theory_lib" mean a *filesystem/namespace
split* (high-churn, breaking) or an *internal decoupling* (dependency-direction cleanup inside the
existing layout)? The team must get the user to disambiguate before planning. My reading of the
evidence: the layout is already correct; the real defects are coupling and non-uniformity (F4, F5).

### F2. The spatial subtheory is a documentation stub, not code — "removal" is trivial, and researchers who assume otherwise will overscope

`logos/subtheories/spatial/` contains exactly one file: a 320-line `README.md`. There is no
`semantic.py`, `operators.py`, `examples.py`, or tests. Verified dependents:

- `AVAILABLE_SUBTHEORIES` in `logos/subtheories/__init__.py:19-25` already excludes spatial
  (extensional, modal, constitutive, counterfactual, relevance only).
- Zero Python references to "spatial" anywhere in `code/` outside two *comment lines* in
  `theory_lib/__init__.py` (lines 16, 64).
- Zero references in any `.ipynb`, zero in `docs/` or `code/docs/`.
- The only live cross-references are in the agent-system context layer
  (`.claude/context/project/logic/domain/spatial-domain.md`, `spatial` mentions in
  `.claude/context/project/logic/README.md`, mirrored under `.opencode/`) — removing the README
  dangles those, a cleanup nobody has flagged.

Risk in the other direction: any effort estimate that budgets "remove spatial subtheory" as a real
code-removal phase is padding. Conversely, the 320-line README is real intellectual content
(restored/kept during task 119's logos reconciliation — see
`specs/119_restore_core_infrastructure_and_reconcile_the_logo/handoffs/phase-3-handoff-20260724.md`);
nobody has asked whether the user wants it *deleted* or *archived* (e.g., to docs/ or specs/).
That question should be asked, not assumed.

### F3. In-flight work collision: task 117 is still [PLANNING] and this refactor sits on an unmerged 51-commit restoration branch

- `specs/state.json`: task 117 (`review_cli_pypi_parity_nix_flake_release`, type python) is status
  `planning` — its 13-phase program (baseline capture, oracle relocation, theory restoration,
  package identity, differential root-cause, flake, docs, release) spawned tasks 118-125, all now
  completed, but 117 itself has a pending "full green gate" / release terminus and two rounds of
  team research (`specs/117_.../reports/01_*`, `03_*` plus `02_spawn-analysis.md`).
- The entire restoration (tasks 117-126) lives on `task-117-restore-model-checker`, 51 commits
  ahead of master; `master` contains none of it. A sweeping refactor layered on an unmerged
  restoration branch compounds merge risk and makes the task-125 release rehearsal (local build
  parity diff, publish checklist) stale before it is ever exercised.
- The working tree is **dirty during this research**: `code/src/model_checker/models/structure.py`
  has uncommitted modifications, and `code/specs/state.json` is deleted-but-uncommitted. Any
  researcher reading `models/structure.py` right now is analyzing unreviewed, uncommitted state
  without knowing it.

**Unasked sequencing question**: should task 126 land before or after (a) task 117 closes and
(b) the branch merges to master / the 1.3.0+ release ships? Refactoring first invalidates the
just-completed docs refresh (124), release rehearsal (125), and baselines (F6).

### F4. Hidden coupling is real, specific, and worse than "imports": name-keyed registries and module-path serialization

Researchers proposing to move/rename theories must account for these concrete mechanisms (all
verified in source):

- `builder/serialize.py:49,118-126` serializes semantics/proposition/model/operator classes **by
  `__module__` string** and rehydrates via `importlib.import_module` (lines 71, 145). Any module
  path change silently breaks cross-process (maximize/compare) round-trips unless both ends move
  together; docstring example hardcodes `"model_checker.theory_lib.bimodal.operators"` (line 26).
- `builder/loader.py:186-197` hardcodes a class-name→theory-name map (`'BimodalProposition':
  'bimodal'`, `'Bimodal': 'bimodal'`, ...).
- `jupyter/adapters.py:91-94` hardcodes a per-theory adapter registry
  (`logos/exclusion/imposition/bimodal` → adapter classes).
- Theory-name references appear in 37 non-test core files/dirs spanning `builder/` (loader,
  project, runner, serialize), `iterate/` (errors, graph, models), `jupyter/` (adapters,
  builder_utils, interactive, unicode), `solver/z3_adapter.py`, `utils/api.py`, `utils/version.py`
  — plus ~20 core test modules that pin these names.
- `code/dev_cli.py:22` imports `from src.model_checker.__main__ import main` — it depends not just
  on `code/src` on sys.path but on `src` itself being importable as a package. This is fragile,
  arguably already a bug (it shadows the installed package namespace), and will break under most
  restructurings. Nobody has flagged it.

### F5. The oracle/ tree is a live external consumer of the exact paths under refactor

`oracle/bimodal_logic/provider.py:119-121` imports `model_checker.utils.context`,
`model_checker` top-level (ModelConstraints, Syntax), and `model_checker.theory_lib.bimodal`
(plus `serialization.py`, four test modules). The oracle was deliberately relocated OUT of the
package (task 118) to be a standalone differential-oracle tree excluded from the wheel, with its
own `bimodal_harness.oracle_providers` entry point. It is not covered by
`PYTHONPATH=code/src pytest code/tests/` and is easy to forget: a refactor that greens the package
suite can still break the oracle silently. Also `code/scripts/compare_bimodal_baseline.sh` binds
to current paths.

### F6. Baselines exist but not where CLAUDE.md says, and they encode current behavior

- `specs/baselines/` (per CLAUDE.md "Specs Directory Protocol") does not exist. Actual baselines:
  `specs/118_.../baselines/` and `specs/122_.../baselines/`. CLAUDE.md's whole specs protocol
  section (specs/plans/, specs/research/, ...) is stale relative to the real `{NNN}_{SLUG}` layout
  — a researcher trusting CLAUDE.md will look in the wrong places.
- Task 122's hard-won green state is precise and fragile: bimodal in-package suite 286/286 green
  only with `-n 6` (an `-n auto` CPU-contention flake was root-caused), 5 cross-oracle
  differential failures are `xfail(strict=True)` pinned to a Z3-timeout-conflated-with-UNSAT
  mechanism, oracle suite 533/550 raw / 541/550 isolation-verified. A refactor that reorders
  test collection, changes conftest scope, or alters Z3 context isolation
  (`model_checker.utils.context.isolated_z3_context` — imported by the oracle) can flip
  strict-xfails to XPASS (which *fails* the suite) without touching any semantics.

### F7. Structural non-uniformity is real, but the "standardized set of modules" target is underdetermined — and the codebase contradicts CLAUDE.md's claimed standard

CLAUDE.md asserts "All theories follow standard structure (semantic.py, operators.py,
examples.py)". Reality (verified by directory listing):

| Theory | Extra top-level modules | `semantic/` subpackage contents | Tests | Cruft |
|---|---|---|---|---|
| bimodal | no `iterate.py` (only theory without it) | witness_constraints, witness_registry | unit+integration+**e2e** (only theory with e2e) | — |
| exclusion | iterate.py | constraints, core, model, registry | unit+integration | `history/`, `notebooks/` |
| imposition | iterate.py | core, helpers, model | unit+integration | `examples_refactored/`, `reports/`, `notebooks/` |
| logos | iterate.py, comparison.py, protocols.py | none (monolithic semantic.py) | unit+integration | `spatial/` stub |

All four ship BOTH `semantic.py` and a `semantic/` package except logos (which has neither split
nor witness registry). Additionally, `code/` root carries refactor-relevant clutter nobody has
scoped: `boneyard/` (legacy `theory_lib/exclusion`, `theory_lib/imposition` copies — dead weight
or reference?), `output.md`, `scaling_benchmark.py`, `test_update.py`, `run_update.py`,
`jupyter_link.py`, `run_jupyter.sh`. A "uniformity" plan that only touches the four theory dirs
misses half the disorder; one that standardizes without deciding the `semantic.py`-vs-`semantic/`
question (and whether bimodal *should* have `iterate.py`, or whether e2e tests should exist for
all theories) is just reshuffling. Current test inventory to protect: 273 collected under
`code/tests/`, 1,002 under `theory_lib/` (both collect cleanly today, 0.7-1.0s).

### F8. State/metadata hygiene issues that will bite the postflight

Tasks 119-121 have `status: completed` with `completion_summary: null`, violating the state.json
schema ("Required when status=completed"). Not a refactor blocker, but any tooling/archival
(`/todo`) run mid-refactor may choke or mis-archive; it also signals that "completed" statuses in
this restoration series are not uniformly trustworthy — verify claims against the tree, not
state.json.

## Recommended Approach (for the synthesis)

1. **Force disambiguation before planning.** Present the user with the validated current layout
   and ask: (a) namespace split vs in-place decoupling? (b) delete vs archive the spatial README?
   (c) sequence relative to task 117 closure / master merge / next PyPI release? Do not let the
   plan encode a guess on any of these.
2. **Reframe the refactor as dependency-direction enforcement, not relocation.** The valuable,
   non-breaking version of this task: theories register themselves (adapter/loader/serializer
   registries become theory-owned registrations instead of core-owned hardcoded maps in
   `builder/loader.py`, `jupyter/adapters.py`), core never imports theory names. That achieves
   "core vs theory_lib" without breaking PyPI users, oracle/, docs, or baselines.
3. **Treat oracle/ as a first-class regression surface.** Add its suite (and
   `compare_bimodal_baseline.sh`) to the refactor's verification gate explicitly; it is invisible
   to the default test commands.
4. **Pin the behavioral baseline before any move**: record `pytest --collect-only` inventories
   (273 + 1,002), the `-n 6` bimodal invocation, and the strict-xfail set from task 122 as the
   task-126 baseline; verify after every phase. Strict-xfail XPASS flips are the most likely
   silent casualty.
5. **Scope the cruft explicitly**: boneyard/, exclusion/history/, imposition/examples_refactored/,
   imposition/reports/, root-level stray files. Either in-scope with a deletion decision per item,
   or explicitly out-of-scope — not unmentioned.
6. **Budget doc updates honestly**: ~50 docs files reference current paths, freshly rewritten in
   task 124. If paths change, task 124's output is a casualty and must be redone; if paths don't
   change, say so and save the effort.

## Evidence/Examples

- theory_lib location: `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}` (ls verified)
- spatial contents: `find .../logos/subtheories/spatial -type f` → only `README.md` (320 lines)
- spatial registry absence: `logos/subtheories/__init__.py:19-25` (`AVAILABLE_SUBTHEORIES`)
- serialization by module path: `code/src/model_checker/builder/serialize.py:49,71,118-126,145`
- hardcoded theory maps: `code/src/model_checker/builder/loader.py:186-197`,
  `code/src/model_checker/jupyter/adapters.py:91-94`
- oracle imports: `oracle/bimodal_logic/provider.py:119-121`
- dev_cli fragile import: `code/dev_cli.py:22` (`from src.model_checker.__main__ import main`)
- branch state: `git log --oneline master..task-117-restore-model-checker | wc -l` → 51; `master`
  is a strict ancestor
- state.json: task 117 `status: planning`; tasks 119-121 `completion_summary: null`;
  task 122 summary documents 286/286 with `-n 6`, 5 strict xfails, oracle 533/550→541/550
- test collection: `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` → 273;
  same for `theory_lib` → 1,002
- docs exposure: 51 files match `theory_lib`, 49 match `src/model_checker` across `docs/` + `code/docs/`
- dirty tree during research: `git status` shows modified `code/src/model_checker/models/structure.py`,
  deleted `code/specs/state.json` (uncommitted)
- packaging: `code/pyproject.toml` — name `model-checker`, version `1.3.0`, setuptools find under
  `src/`, package-data includes `*.md`/`*.ipynb` (so the spatial README currently ships in the wheel)

## Confidence Level

**High** for F1-F7 (each claim verified directly against the working tree, git history, or
state.json during this session; no claim rests on memory or documentation alone).
**Medium** for F8's practical impact (schema violation confirmed; downstream tooling behavior on
null summaries not exercised) and for the exact blast radius of serialize.py (runtime round-trips
are within-run; no evidence of *persisted* serialized module paths was found, so it constrains
atomicity of a rename rather than backward compatibility of saved artifacts).
