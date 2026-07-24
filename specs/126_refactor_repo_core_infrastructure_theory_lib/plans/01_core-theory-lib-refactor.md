# Implementation Plan: Refactor Core Infrastructure and theory_lib

- **Task**: 126 - Systematically refactor the repo into core infrastructure and theory_lib; remove the logos spatial subtheory; standardize the per-theory module set
- **Status**: [IMPLEMENTING]
- **Effort**: 41 hours
- **Dependencies**: None (proceeds on branch `task-117-restore-model-checker`; see Non-Goals for merge/release sequencing)
- **Research Inputs**: `specs/126_refactor_repo_core_infrastructure_theory_lib/reports/01_team-research.md` (4-teammate synthesis; teammate findings `01_teammate-{a,b,c,d}-findings.md`)
- **Artifacts**: plans/01_core-theory-lib-refactor.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; `.claude/rules/no-task-references-in-deliverables.md`; `code/docs/core/TESTING_GUIDE.md`
- **Type**: general

## Overview

The core/theory split already exists structurally: `theory_lib/` sits inside src-layout at
`code/src/model_checker/theory_lib/` beside the core packages, holding exactly the four requested
theories. The real work is **boundary quality and uniformity**, not location. This plan enforces a
strictly one-way dependency (`theory_lib` -> core, never the reverse) backed by an executable
layering test, replaces three drifting copies of "which theories exist" with one registration-based
registry, standardizes every theory onto a single canonical module set enforced by a parametrized
conformance test, deletes the spatial stub and accumulated cruft, and fixes the live contract bugs
found en route.

`theory_lib` does **not** move. Directory position does not create modularity; dependency direction
does. The dependency graph is already near-clean (`theory_lib` -> core is 88 imports; core ->
`theory_lib` is 10 lazy call sites across 5 files), and moving `theory_lib` to `code/src/theory_lib/`
while those 10 inversions remain would convert an internal layering wart into a genuine circular
dependency between two top-level importable packages — strictly worse. Because
`[tool.setuptools.packages.find] where = ["src"]` auto-discovers any `src/` sibling, the move would
also ship both packages in the same wheel: all the breakage, none of the separate-distribution
payoff. Phases 9-16 are the mechanism that actually delivers "core system + modular extensions," and
they are prerequisites for a clean extraction later if one is ever wanted.

Definition of done: the conformance test and the layering test both pass with zero xfail markers;
`get_test_examples()` works for all four theories; no core module imports `theory_lib` statically or
by string; the post-refactor wheel differs from the recorded pre-refactor manifest only by
enumerated, intentional deltas; and the pinned test baselines are met or exceeded.

### Research Integration

The research report's Wave 1 (hygiene) / Wave 2 (theory contract) / Wave 3 (boundary hardening)
frame is adopted, with boundary work promoted ahead of per-theory normalization so the registry
exists before theories are asked to register into it. Report claims were re-verified against the
tree during planning, and the four items the research left open are resolved here:

1. **`logos/comparison.py` is not a duplicate of `builder/comparison.py`.** Read side by side they
   share zero symbols and solve unrelated problems: the logos file is a standalone z3-vs-cvc5 CLI
   benchmark script; `builder/comparison.py` is the runtime `--maximize` theory comparator. Phase 6
   relocates the benchmark out of the package (it imports `unittest.mock` in shipped code, ships
   37.5 KB into the wheel, and is the sole theory -> builder import inversion).
2. **Restore `bimodal/iterate.py` from git history.** The deletion in commit `9b76ffa2` was
   deliberate, but it was dependency-cutting during an unrelated restoration ("Option A"), not a
   judgment that the semantics were wrong — and it left a live reachable defect:
   `bimodal/semantic.py:68` still declares `'iterate': 1` in `DEFAULT_EXAMPLE_SETTINGS`, so a user
   setting `iterate: 2` on a bimodal example hits `ImportError` at `builder/runner.py:875`. A
   410-line `bimodal/docs/ITERATE.md` still documents the removed API. The 611-line blob retrieves
   cleanly, compiles, and all three of its imports still resolve; the repo has an established
   restore-and-port recipe already used twice for exclusion and imposition. Phase 22 restores it,
   which makes `iterate.py` a *required* contract element for all four theories.
3. **Fold the relevance subtheory into constitutive.** `relevance/get_operators()` returns `{}`; the
   sole `RelevanceOperator` definition is `constitutive/operators.py:376`, registered under
   `"\\preceq"` at `constitutive/operators.py:565`, and reaches relevance only through the
   `'relevance': ['constitutive']` dependency edge at `logos/operators.py:38`. Decisive evidence that
   the subtheory is hollow: `relevance/examples.py`'s own registry loads
   `['extensional', 'constitutive', 'modal']` and *not* `'relevance'`, and dropping `'relevance'`
   from `test_relevance_examples.py:35` leaves all 20 tests passing. Populating it instead was
   considered and rejected — moving `RelevanceOperator` out of constitutive would break
   constitutive's `\preceq` registration and its dependency-free status, and the REL examples at
   `relevance/examples.py:113-163` mix `\preceq` with `\leq`/`\sqsubseteq`/`\equiv`, so relevance
   would still depend on constitutive afterward. Phase 19 folds.
4. **E2E stays at core level, parametrized over theories.** No theory has a working e2e suite; only
   bimodal has an `e2e/` directory and it is empty (its sole file was deliberately removed, and it
   lacks even an `__init__.py`). `code/tests/e2e/test_project_creation.py` already reaches every
   theory via `BuildProject(theory=...)` and already parametrizes
   `test_project_creation_all_theories[bimodal]`. Phase 22 deletes the empty directory and extends
   that existing parametrization to all four theories, rather than duplicating a `test_workflow.py`
   four times.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` exists but is nearly empty (44 lines). Its single durable decision — ship as the
`model_checker` package built from `code/` with `where = ["src"]`, `oracle/` outside the wheel —
directly constrains this refactor to reorganizing *inside* `code/src/model_checker/`, with no
build-root moves and no package renames. This plan advances that decision and adds three records:
the rejected-for-now `theory_lib` extraction with its revisit trigger (Phase 26), the refactor-first
release sequencing that supersedes the current "Merge and publish 1.3.0" priority (Phases 1 and 26),
and the deferred core-package reorganization. Phase 1 snapshots the current state so Phase 26 can
show a clean before/after.

## Goals & Non-Goals

**Goals**:

- Enforce a strictly one-way dependency: `theory_lib` may import core; no core module imports
  `theory_lib`, statically or via string-literal `importlib`. Backed by an executable test.
- Replace the triplicated theory registry (`AVAILABLE_THEORIES`, `discover_theories()`,
  `builder/loader.py`'s hardcoded dicts) with one registration-based registry that core queries and
  never hardcodes names into.
- Define one canonical module set per theory and per subtheory in `THEORY_ARCHITECTURE.md`, and
  enforce it with a parametrized conformance test over the registry.
- Normalize all four theories onto the `semantic/` package form, eliminating bimodal's dual module
  identity.
- Delete the spatial subtheory, dead compatibility wrappers, and accumulated cruft; stop cruft from
  leaking into the wheel and into user-scaffolded projects.
- Fix the live contract bugs: `get_test_examples('bimodal')` raising, logos's duplicate
  `example_range`, divergent `get_theory` signatures, relevance's empty `get_operators()`, bimodal's
  missing iterator (reachable `ImportError` under `iterate: 2`), and `builder/loader.py`'s
  theory-identification dicts that were never restored beyond bimodal.
- Populate `specs/ROADMAP.md` with the durable decisions this refactor settles.

**Non-Goals**:

- **Moving `theory_lib` out of `model_checker`, renaming packages, or changing the build root.**
  Settled: rejected. See Overview.
- **Splitting `theory_lib` into a separate PyPI distribution.** Recorded in ROADMAP as REJECTED (for
  now) with an explicit revisit trigger (Phase 26).
- **Entry-point / third-party plugin discovery.** The Phase 10 registry keeps the door open; the
  machinery is not built now.
- **Flattening logos subtheories into top-level theories.** Subtheories are operator packages over
  shared logos semantics; the two-level nesting is semantically motivated. (Folding the hollow
  relevance subtheory into constitutive in Phase 19 is a defect fix, not a flattening of the model.)
- **Adding per-theory e2e test suites.** E2E exercises the CLI and build pipeline, not theory
  semantics, and already lives at core level (`code/tests/e2e/`, `builder/tests/e2e/`,
  `iterate/tests/e2e/`). Phase 22 deletes bimodal's empty `tests/e2e/` stub and extends the existing
  core parametrization instead. Recorded as a deliberate "none at theory level" decision.
- **Removing `builder/comparison.py`.** A prior archived review proposed it as `--maximize`-only
  dead code; it has 15 live tests and its own blast radius. Out of scope.
- **Merging `task-117-restore-model-checker` to master, tagging, or publishing.** The branch is 63
  commits ahead of master and this refactor continues on it. Per the settled sequencing, the full
  refactor lands first, the release rehearsal is redone once afterward, and a single release
  follows. Merge, tag, push, and PyPI upload are user-only per `.claude/rules/pr-prohibition.md`;
  no phase in this plan performs any of them. Do not merge to master mid-refactor.
- **Reorganizing the core packages themselves** (`models/`, `solver/`, `syntactic/`, `utils/`
  internal structure) beyond the specific relocations named in Phases 12 and 16. Recorded as a
  deferred ROADMAP item.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| No published 1.3.0 baseline exists to diff the post-refactor wheel against | H | Certain | Phase 2 pins local evidence instead: task 125's recorded `rehearsal/wheel-contents.txt`, fresh `--collect-only` inventories, and a rebuilt pre-refactor wheel. Phase 25 diffs against these; every delta must be enumerated and intentional. |
| bimodal's `semantic/__init__.py` registers `bimodal_semantic_module` in `sys.modules` specifically to make classes picklable under `ProcessPoolExecutor` (the `--maximize` path). Naive removal of the hack silently breaks `--maximize` with "Maximum N = 0" | H | M | Phase 20 treats the pickling contract as the primary acceptance criterion, not an afterthought. `bimodal/tests/unit/test_semantic_module_registration.py` already guards it — run it before, during, and after. Phase 20 is a pure move (no content split); the split is deferred to Phase 21 so a pickling regression is unambiguously attributable. |
| The 5 `xfail(strict=True)` cross-oracle differentials fail the suite if a refactor-induced XPASS flips them | H | M | Phase 2 enumerates all five by file:line and records their current outcomes. The regression gate script asserts the xfail set is unchanged, not merely that the suite is green. Re-run at every wave boundary. |
| `oracle/` is a live external consumer (`oracle/bimodal_logic/provider.py:119-121` imports `model_checker.utils.context` and `model_checker.theory_lib.bimodal`) and is invisible to the default test commands | H | M | The oracle suite (550 tests) and `code/scripts/compare_bimodal_baseline.sh` are named, mandatory steps in the Phase 2 gate script, run at every wave boundary — never left to the default `pytest` invocation. |
| `builder/serialize.py` serializes classes by `__module__` string (`:49`, `:118-126`) and rehydrates via `importlib` (`:71,145,173,195`); the bimodal and logos semantic splits change `__module__` values | H | M | No package renames occur (Decision: no relocation), so dotted prefixes are stable. Phases 18, 20, and 21 keep the public re-export path (`theory_lib.{theory}.semantic`) byte-identical from the importer's view and run `builder/tests/unit/test_serialize.py` as a phase gate. |
| Registry consolidation regresses theory discovery in generated projects, which resolve theories by filesystem path rather than by import | M | M | Phase 13 replaces path-substring sniffing with registry queries but keeps `builder/tests/integration/test_generated_projects.py` as a phase gate; Phase 7's copy manifest is verified by actually scaffolding a project. |
| Docs blast radius: ~50 docs files reference current paths, freshly rewritten | M | L | Paths are not changing, which neutralizes most of this. Phase 24 budgets explicitly for the files that genuinely change: `THEORY_ARCHITECTURE.md` (the anchor standard), `CLAUDE.md`'s stale "all theories follow semantic.py, operators.py, examples.py" claim and its stale `specs/baselines/` reference, and the per-theory docs affected by the semantic splits. |
| Long phase chain (26 phases) invites drift between the contract doc and the conformance test | M | M | The contract (Phase 3) is written before the test (Phase 8), and the test is the single enforcement point. Phase 23 asserts zero remaining xfail markers, so no gap can be quietly carried. |
| Folding relevance into constitutive misses one of the 12+ call sites that name `'relevance'` as a loadable subtheory, producing a runtime failure only under specific subtheory selections | M | M | Phase 19 enumerates every call site up front and removes `'relevance'` from `AVAILABLE_SUBTHEORIES` first, so any missed site fails fast and loudly at load time rather than silently. Two of the listed sites (`scaling_benchmark.py`, `logos/comparison.py`) are already deleted or relocated by Phases 5 and 6, which run first. |
| Restored `bimodal/iterate.py` predates the generator-interface convention and references two `BimodalStructure` attributes that no longer exist | M | M | Both missing attributes (`detect_model_differences`, `_get_friendly_letter_name`) are already `hasattr`-guarded in the restored source, so they degrade rather than crash. Phase 22 ports to the current convention using `imposition/iterate.py` as the template and rewrites the test against `imposition/tests/integration/test_iterate.py` rather than restoring the Mock-heavy original. |
| Working tree is dirty and the branch is 63 commits ahead of master | M | Certain | Phase 2 requires a clean tree before pinning baselines. Commit per green sub-step per `.claude/rules/git-workflow.md`; never `git add -A`. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4, 5, 6 | 2 |
| 3 | 7, 8, 9 | 3, 4, 5, 6 |
| 4 | 10, 11 | 8, 9 |
| 5 | 12, 13, 14 | 10, 11 |
| 6 | 15, 16, 17 | 10, 13, 14 |
| 7 | 18 | 17 |
| 8 | 19, 20 | 18 |
| 9 | 21 | 20 |
| 10 | 22 | 19, 21 |
| 11 | 23 | 12, 15, 16, 22 |
| 12 | 24 | 23 |
| 13 | 25 | 23, 24 |
| 14 | 26 | 25 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Review and Snapshot ROADMAP.md [COMPLETED]

- **Goal:** Record the pre-refactor state of `specs/ROADMAP.md` so Phase 26 can show a clean
  before/after, and identify which roadmap items this refactor advances or supersedes.
- **Tasks:**
  - [x] Read `specs/ROADMAP.md` in full and copy it verbatim to
        `specs/126_refactor_repo_core_infrastructure_theory_lib/roadmap-before.md`. *(completed:
        verified byte-identical via diff)*
  - [x] Record the current durable decision (package identity: `model_checker`, four registered
        theories, built from `code/` with `where = ["src"]`, `oracle/` outside the wheel) and note
        that it constrains this refactor to reorganizing inside `code/src/model_checker/`.
        *(completed: recorded in snapshot; decision already present in ROADMAP.md text)*
  - [x] Identify items this refactor advances: none of the four Phase 1 priorities are directly
        advanced, but "Merge and publish 1.3.0" is **superseded** by the refactor-first sequencing
        and must be rewritten in Phase 26 rather than checked off. *(completed: deferred to Phase
        26)*
  - [x] Note the two items this refactor will add: the `theory_lib` extraction decision record, and
        the deferred core-package reorganization. *(completed: deferred to Phase 26)*
  - [x] Confirm ROADMAP.md is not modified in this phase (read-only snapshot). *(completed: git
        diff specs/ROADMAP.md is empty)*
- **Timing:** 0.5 hours
- **Depends on:** none
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/roadmap-before.md` - new snapshot file
- **Verification:**
  - Snapshot file exists and is byte-identical to `specs/ROADMAP.md`.
  - `git diff specs/ROADMAP.md` is empty.

---

### Phase 2: Pin Verification Baselines and Build the Regression Gate [IN PROGRESS]

- **Goal:** Capture every pre-refactor measurement the plan will be judged against, and package the
  checks into one reusable script so every later phase can run the same gate.
- **Tasks:**
  - [x] Ensure a clean working tree (commit or stash unrelated changes) before measuring.
        *(completed)*
  - [x] Pin collection inventories with `--collect-only -q`, using the invocation methodology
        recorded in `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/collection-counts.txt`:
        run from `code/` (or with explicit `code/tests/ code/src/model_checker` paths) so
        `pyproject.toml`'s `testpaths` applies. A bare root-level `pytest --collect-only` walks
        `code/boneyard/` and yields a misleading count. Record the actual numbers observed; the
        task-122 baseline is 2095 in-package + 550 oracle. Note that the research report's
        "273 + 1,002" figures use a different scoping and should not be used as the gate.
        *(completed: 289 bimodal / 2100 full / 550 oracle, recorded in
        `baselines/collection-counts.txt`)*
  - [x] Run the in-package bimodal suite with `-n 6` (not `-n auto`; 12-way parallelism causes a
        documented CPU-contention flake) and record the result against the 286/286 baseline.
        *(completed: 289 passed, recorded in `baselines/bimodal-run.txt` and
        `baselines/bimodal-run-attempt2.txt` with junit XML)*
  - [ ] Run the oracle suite (`oracle/bimodal_logic/tests/`) and record results plus junit XML.
        *(in progress — background run underway at commit time; collection count already pinned
        at 550 matching baseline; results/junit XML to follow in a separate commit once the run
        completes, per orchestrator instruction not to block this commit on it)*
  - [x] Enumerate the 5 `xfail(strict=True)` cross-oracle differentials in
        `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (lines 767, 942, 1020, 1133,
        1431) with their current outcomes, so an XPASS flip is detectable. *(completed: line set
        confirmed via grep, encoded as the static check in `verify-refactor.sh` step 5; outcome
        confirmation — strict-xfail, not XPASS — follows from the oracle suite run above)*
  - [x] Run `code/scripts/compare_bimodal_baseline.sh` and record its output. *(completed: 0
        regressions, recorded in `baselines/compare-bimodal-baseline-output.txt`)*
  - [x] Build the pre-refactor wheel and record its contents listing; keep task 125's
        `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/wheel-contents.txt` as the
        secondary reference manifest. *(completed: recorded in
        `baselines/wheel-contents-pre-refactor.txt`)*
  - [x] Write `code/scripts/verify-refactor.sh` running all of the above and asserting: collection
        counts, bimodal green, oracle green, xfail set unchanged, baseline comparison clean. Non-zero
        exit on any deviation (fail-fast). *(completed)*
  - [x] Store all captured artifacts under
        `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/`. *(completed)*
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `code/scripts/verify-refactor.sh` - new reusable gate script
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/` - new baseline artifacts
- **Verification:**
  - `bash code/scripts/verify-refactor.sh` exits 0 on the unmodified tree.
  - Deliberately perturbing one expectation makes it exit non-zero (prove the gate has teeth).

---

### Phase 3: Define the Canonical Theory Contract in THEORY_ARCHITECTURE.md [COMPLETED]

- **Goal:** Replace the current two-pattern ("Simple" vs "Modular") description with one canonical
  module set plus a declared optionality policy, so the conformance test has an authoritative spec
  to encode.
- **Tasks:**
  - [x] Rewrite `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` to define the
        **required** theory file set: `__init__.py` (exposing `get_theory(config=None)`),
        `semantic/` package (re-export-only `__init__.py`, plus `core.py`, `model.py`, and
        theory-specific modules), `operators.py`, `iterate.py` (exposing `{Theory}ModelIterator`,
        `iterate_example`, and `iterate_example_generator` with the `.returns_generator` /
        `.__wrapped__` markers that `builder/runner.py:879-889` keys off), `examples.py`, `tests/`
        (`__init__.py`, `conftest.py`, `unit/`, `integration/`, `README.md`), `docs/` (the six-file
        set: `README.md`, `API_REFERENCE.md`, `ARCHITECTURE.md`, `ITERATE.md`, `SETTINGS.md`,
        `USER_GUIDE.md`), `README.md`, `CITATION.md`, `LICENSE.md`, `VERSION`. *(completed)*
  - [x] Define the **required** `examples.py` attributes: `example_range`, `test_example_range`,
        `semantic_theories`, `unit_tests` — each assigned exactly once. *(completed)*
  - [x] `iterate.py` is **required**, not optional: every theory's `DEFAULT_EXAMPLE_SETTINGS`
        declares an `iterate` setting, so a theory without an iterator has a live reachable
        `ImportError` path. Phase 22 restores bimodal's, closing the only gap. *(completed)*
  - [x] Define the **optional** elements: `notebooks/` is optional and reported but not enforced
        (exclusion and imposition have them; bimodal and logos do not). *(completed)*
  - [x] Define the **subtheory** set (logos): `__init__.py`, `operators.py` (must return a non-empty
        dict from `get_operators()`), `examples.py`, `tests/`, `README.md`. Semantics stays
        centralized in `logos/semantic/`; subtheories never define their own semantics. State that a
        subtheory contributing zero operators is a defect, not a valid configuration — the rule
        Phase 19 acts on. *(completed)*
  - [x] State that `e2e/` is **not** part of the theory test set; end-to-end coverage lives at core
        level and is parametrized over theories. `theory_lib/docs/CONTRIBUTING.md:85-96` currently
        mandates a per-theory `e2e/` directory that zero of four theories have — correct it here or
        flag it for Phase 24. *(completed: flagged in THEORY_ARCHITECTURE.md's End-to-End Testing
        section rather than editing CONTRIBUTING.md directly; deferred to Phase 24)*
  - [x] Add a **Layering** section declaring the three layers: core (`models`, `syntactic`, `solver`,
        `utils`, `iterate`, `builder`, `settings`, `output`, `z3_shim`) which must never import
        `theory_lib`; `theory_lib` which may import core; and the upper layer
        (`model_checker/__init__.py`, `model_checker/api.py`, `__main__.py`, `jupyter/`) which may
        import both. *(completed)*
  - [x] Delete the "Simple Pattern" vs "Modular Pattern" fork — there is now one pattern, with logos
        additionally carrying `subtheories/`. *(completed)*
  - [x] MUST NOT cite task numbers anywhere in this file (it is a deliverable outside `specs/**`).
        Reference sibling documents and section headings as durable anchors instead. *(completed:
        verified via grep -nEi 'task [0-9]', zero matches)*
- **Timing:** 2 hours
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` - rewritten as the anchor standard
- **Verification:**
  - Every required item in the contract corresponds to something a test can assert.
  - `grep -nEi 'task [0-9]' THEORY_ARCHITECTURE.md` returns nothing.
  - Existing cross-references from `theory_lib/docs/README.md` still resolve.

---

### Phase 4: Remove the Spatial Subtheory and the Dead Semantic Wrappers [COMPLETED]

- **Goal:** Clean break deletions that remove genuinely unreachable code, with no behavior change.
- **Tasks:**
  - [x] Delete `code/src/model_checker/theory_lib/logos/subtheories/spatial/` (a README-only stub;
        `README.md` is its sole file). No archival copy — git history preserves it, and CLAUDE.md
        mandates clean breaks with no backwards-compatibility layers. *(completed)*
  - [x] Remove the two dangling spatial comment references at
        `theory_lib/__init__.py:16` and `theory_lib/__init__.py:63-64`. *(completed)*
  - [x] Confirm spatial is absent from `AVAILABLE_SUBTHEORIES`
        (`logos/subtheories/__init__.py:19-25`) and `SUBTHEORY_DESCRIPTIONS` — it already is; assert
        rather than assume. *(completed: verified via python -c import assertion, confirmed absent)*
  - [x] Delete `theory_lib/exclusion/semantic.py` (32 lines) and `theory_lib/imposition/semantic.py`
        (31 lines). Both are self-described backward-compatibility re-exports and both are
        unreachable, since Python resolves the sibling `semantic/` package first. *(completed)*
  - [x] Do **not** touch `theory_lib/bimodal/semantic.py` in this phase — it is live (the package
        re-executes it). It is handled in Phase 20. *(confirmed untouched)*
  - [x] Update `.claude/context/project/logic/domain/spatial-domain.md`: it is a deliverable outside
        `specs/**` that will dangle. Rewrite its opening to state that spatial is not implemented in
        the theory library and that the file is retained as domain background only, or delete it if
        it has no standalone value. Decide and act; do not leave it dangling. *(completed: also
        updated the duplicate .opencode/context/ copy of the same file for consistency)*
  - [x] Grep the whole repo (including `docs/`, `code/docs/`, `oracle/`) for remaining `spatial`
        references and resolve each. *(completed: zero code/oracle/docs references remain; the
        two agent-system index.json/README.md entries cataloging spatial-domain.md as a topic doc
        are legitimate and untouched)*
  - [x] *(deviation, not in original task list)* Fixed
        `exclusion/tests/integration/test_project_generation.py`, which asserted the now-deleted
        flat `semantic.py` file as a required file / generated-project artifact. Updated both
        assertions to check for the `semantic/` package (directory + `__init__.py`) per the Phase 3
        contract. Reason: the test encoded the pre-refactor (bare-module) contract, not a
        regression from this phase's deletion.
- **Timing:** 1 hour
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/logos/subtheories/spatial/` - deleted
  - `code/src/model_checker/theory_lib/__init__.py` - remove spatial comment references
  - `code/src/model_checker/theory_lib/exclusion/semantic.py` - deleted
  - `code/src/model_checker/theory_lib/imposition/semantic.py` - deleted
  - `.claude/context/project/logic/domain/spatial-domain.md` - updated or deleted
- **Verification:**
  - `bash code/scripts/verify-refactor.sh` still exits 0.
  - `grep -rn spatial` across the repo returns only intentional, updated references.
  - `python -c "from model_checker.theory_lib.exclusion.semantic import WitnessSemantics"` and the
    imposition equivalent still work (the packages, not the deleted wrappers, provide them).

---

### Phase 5: Cruft Sweep [COMPLETED]

- **Goal:** Remove accumulated dead trees and root strays, archiving anything of lasting value first.
- **Tasks:**
  - [x] `code/src/model_checker/theory_lib/exclusion/history/` (4 files, 52 KB): the content is
        narrative implementation history (`IMPLEMENTATION_STORY.md`, `LESSONS_LEARNED.md`,
        `STRATEGIES.md`, `README.md`). Move it to `docs/` (project documentation, outside the wheel)
        rather than deleting — it has standalone value — then remove it from the package tree.
        *(completed: moved to `docs/theory/exclusion/history/` via `git mv`)*
  - [x] `code/src/model_checker/theory_lib/imposition/examples_refactored/` (10 files, 80 KB):
        delete. It is a superseded parallel copy of `examples.py`; `__init__.py:15` and
        `test_suite.py:16` import back into the live modules, so nothing depends on it in the other
        direction. *(completed: confirmed zero remaining references before deletion)*
  - [x] `code/src/model_checker/theory_lib/imposition/reports/` (7 files, 80 KB): the
        `imposition_comparison/` content is theoretical comparison material. Move to `docs/`, then
        remove from the package tree. *(completed: moved to `docs/theory/imposition/reports/`)*
  - [x] `code/boneyard/` (117 files, 1.7 MB): delete. It is also the reason a bare root-level
        `pytest --collect-only` reports 2516 tests / 26 errors instead of the real inventory, so
        removing it fixes a live developer-experience trap. *(completed; see deviation note below —
        boneyard removal reduces but does not fully eliminate bare-root collection errors)*
  - [x] Root strays: delete `code/dist/`, `code/output.md`, `code/test_update.py`,
        `code/run_update.py`, `code/scaling_benchmark.py`, and repo-root `output.md` / `output.json`.
        Check each for unique value first; archive to `docs/` or `specs/` if any exists.
        *(completed: none carried unique value beyond what git history retains; `code/dist/` was
        gitignored build output, deleted from disk only, no git action needed)*
  - [x] Delete `theory_lib/exclusion/TODO.md` and `theory_lib/logos/TODO.md` from the package tree
        (both currently ship in the wheel); fold any live items into `specs/ROADMAP.md` content
        drafted for Phase 26. *(completed: deleted; content preserved in git history for Phase 26
        to fold forward — both were stale planning notes, not live blockers)*
  - [x] Fix `code/dev_cli.py:22`: `from src.model_checker.__main__ import main` is fragile and
        depends on cwd. Replace with a path-anchored import relative to the script's own location.
        *(completed: now imports `model_checker.__main__` directly, relying on the already-anchored
        `src_path` sys.path insertion; verified working from repo root, `code/`, and `/tmp`)*
  - [x] Re-run the collection inventory and record the new, correct root-level count. *(completed
        with a finding: bare root-level `pytest --collect-only -q` drops from 2516/26-errors to
        2498/17-errors after boneyard removal — see deviation note below)*
  - [x] *(deviation, discovered during verification)* The plan's Phase 5 goal text attributed the
        entire bare-root collection-error trap to `code/boneyard/`. After boneyard's removal, 17
        collection errors remain (`import file mismatch` on duplicate test-module basenames —
        e.g. `test_operators.py` colliding between `exclusion/tests/unit/` and
        `logos/tests/unit/`, `test_validation.py` between `iterate/tests/unit/` and
        `builder/tests/unit/`), spanning `iterate/`, `models/`, `settings/`, `theory_lib/`
        top-level, and all three of `exclusion/`, `imposition/`, `logos/`. This is a genuine,
        pre-existing structural issue (missing package-level disambiguation for same-named test
        files under pytest's default `prepend` import mode) independent of boneyard and of this
        phase's stated scope. Not fixed here — fixing it would mean adding `__init__.py` to every
        affected `tests/unit/`/`tests/integration/` directory across 8 packages, or switching
        `pyproject.toml` to `--import-mode=importlib`, either of which is a cross-cutting change
        warranting its own phase. Flagged for a follow-up (Phase 26 ROADMAP note or a new phase)
        rather than silently left unrecorded. The properly-scoped invocation
        (`cd code && pytest --collect-only`, what `verify-refactor.sh` actually checks) is
        unaffected and still reports the correct 2100.
- **Timing:** 1.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `code/boneyard/` - deleted
  - `code/src/model_checker/theory_lib/exclusion/history/` - moved to `docs/`, removed from package
  - `code/src/model_checker/theory_lib/imposition/{examples_refactored,reports}/` - deleted / moved
  - `code/{dist,output.md,test_update.py,run_update.py,scaling_benchmark.py}` - deleted
  - `code/dev_cli.py` - path-anchored import
  - `code/src/model_checker/theory_lib/{exclusion,logos}/TODO.md` - deleted
- **Verification:**
  - `bash code/scripts/verify-refactor.sh` exits 0 with the in-package inventory unchanged.
  - `cd code && ./dev_cli.py --help` works from at least two different working directories.
  - A bare root-level `pytest --collect-only -q` no longer reports collection errors.

---

### Phase 6: Relocate the Logos Solver Benchmark Out of the Package [COMPLETED]

- **Goal:** Remove the sole theory -> builder import inversion and drop a 37.5 KB CLI benchmark
  script from the shipped wheel.
- **Tasks:**
  - [x] `git mv code/src/model_checker/theory_lib/logos/comparison.py
        code/scripts/logos_solver_benchmark.py`. The rename also removes the misleading basename
        collision with `builder/comparison.py`, which is an unrelated runtime component
        (`--maximize` theory comparison) sharing zero symbols with it. *(completed)*
  - [x] This eliminates `logos/comparison.py:62-64` — the theory -> builder import
        (`from model_checker.builder.example import BuildExample`, used once at `:618`) — by
        construction, and removes `unittest.mock` (imported at `:66`) from shipped library code.
        *(completed: file now lives in code/scripts/, outside the wheel, so its Mock usage no
        longer ships in library code by construction of the move)*
  - [x] Delete the nine unused dataclasses at `:80-178` (`SolverResult`, `ExampleResult`,
        `SolverSummary`, `SubtheorySummary`, `Disagreement`, `BenchmarkMetadata`, `BenchmarkOutput`,
        `TimingSummary`, `ComparisonStats`). None is ever instantiated; `run_benchmarks` builds plain
        dicts at `:757`, `:773`, `:905`. That is ~100 lines of drift risk. *(completed: confirmed
        zero instantiation sites before deletion via grep; also removed the now-unused
        `from dataclasses import dataclass, field, asdict` import)*
  - [x] Update the two live importers: `code/scripts/comparison.py:24`
        (`from model_checker.theory_lib.logos.comparison import main`) and
        `code/scripts/test_cvc5_stability.py:55,130` (`create_test_module`,
        `get_required_subtheories`). Both already perform `sys.path` surgery, so a sibling-script
        import is consistent with their existing style. *(completed: both now import
        `logos_solver_benchmark` as a sibling script; verified working via `comparison.py --help`
        and a direct import smoke test)*
  - [x] Confirm nothing under `code/src/`, `oracle/`, or any test suite imports it.
        `logos/__init__.py` does not reference it. *(completed: grep confirms zero references
        under code/src/, oracle/, or any test suite; the only remaining hit is the auto-generated,
        gitignored `code/src/model_checker.egg-info/SOURCES.txt`, regenerated on next build)*
  - [x] Leave `builder/comparison.py` untouched. *(confirmed untouched)*
- **Timing:** 1.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/logos/comparison.py` - moved to `code/scripts/logos_solver_benchmark.py`
  - `code/scripts/comparison.py` - import updated
  - `code/scripts/test_cvc5_stability.py` - imports updated
- **Verification:**
  - `python code/scripts/comparison.py --help` works.
  - `grep -rn "logos.comparison" code/ oracle/` returns nothing.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 7: Wheel and Scaffolding Hygiene [COMPLETED]

- **Goal:** Stop cruft from re-entering the wheel and user-scaffolded projects, and fix the
  case-collision install defect.
- **Tasks:**
  - [x] Resolve the case-colliding pair `theory_lib/docs/usage_guide.md` (280 lines) vs
        `USAGE_GUIDE.md` (325 lines). Both currently ship in the wheel — a genuine install defect on
        case-insensitive filesystems (macOS default). Merge the unique content of the lowercase file
        into `USAGE_GUIDE.md` and delete `usage_guide.md`; update inbound links. *(completed: merged
        Error Handling, Working with Logos States, Performance Optimization, Testing and
        Validation, and Troubleshooting sections into `USAGE_GUIDE.md`; dropped the lowercase
        file's stale "Architecture Overview"/"Available Theories" sections, superseded by
        THEORY_ARCHITECTURE.md's contract and inaccurate — they omitted exclusion/imposition and
        named a non-existent "intensional" subtheory. Zero inbound links to the lowercase
        filename found repo-wide, so nothing needed redirecting.)*
  - [x] Replace `builder/project.py`'s verbatim copy at `:172` with an explicit **copy manifest**.
        Today only `__pycache__` and `.ipynb_checkpoints` are ignored, so every stray directory in a
        theory tree is copied into user projects. Enumerate the allowed items from the canonical
        theory contract (Phase 3) and copy only those; unknown items are skipped with a warning.
        Fail-fast if a required item is missing. *(completed: added `REQUIRED_COPY_ITEMS` /
        `SEMANTIC_ALTERNATIVES` / `OPTIONAL_COPY_ITEMS` module-level manifest constants and
        rewrote `_copy_files` to use them. Two deviations from a literal reading, both required
        to avoid regressing current scaffolding: (1) `semantic.py` and `semantic/` are BOTH
        accepted, and may coexist — bimodal keeps `semantic/` as a deliberate `sys.modules`
        pickling shim alongside its live `semantic.py`, needed for `--maximize` to keep working;
        (2) `iterate.py` is listed as optional, not hard-required, because bimodal does not yet
        have one (the exact gap Phase 3 already documents as pending for a later phase) — hard-
        requiring it here would make `BuildProject('bimodal')` raise unconditionally, a
        functional regression this hygiene phase must not introduce.)*
  - [x] Tighten `code/pyproject.toml` `[tool.setuptools.package-data]` (currently `"*" = ["README.md",
        "*.md", "*.ipynb"]`, which sweeps in every markdown file) and `code/MANIFEST.in` so
        `TODO.md`, `history/`, `reports/`, and `examples_refactored/`-style directories cannot ship
        even if reintroduced. *(completed: package-data now lists an explicit allowlist
        (README.md, CITATION.md, LICENSE.md, VERSION, docs/*.md, notebooks/*.ipynb) instead of a
        blanket `*.md`/`*.ipynb`; MANIFEST.in mirrors the same allowlist plus explicit
        `global-exclude`/`prune` defense-in-depth entries for TODO.md, history/, reports/,
        examples_refactored/, and pycache artifacts)*
  - [x] Rebuild the wheel and diff its contents against the Phase 2 pre-refactor manifest. Confirm
        the deltas are exactly the 16 cruft entries removed in Phases 4-6 plus the relocated
        benchmark, and nothing else. *(completed with one additional, intentional delta beyond
        the plan's estimate: 19 total removals — the predicted cruft set plus `usage_guide.md`
        itself, all git-history-recoverable — and 4 additions, one `VERSION` file per theory.
        The VERSION files are new because the OLD package-data glob (`"*.md"`/`"*.ipynb"`) never
        matched an extension-less `VERSION` file at all — it was never shipped despite being a
        contract-required root file. The new explicit allowlist includes `VERSION` deliberately,
        per THEORY_ARCHITECTURE.md's Theory Contract, so this is a correctness fix, not scope
        creep.)*
  - [x] Scaffold a project with each of the four theories and confirm no cruft is copied.
        *(completed: verified via direct `BuildProject` smoke test for all four theories; also
        caught and removed a leftover `imposition/examples_refactored/__pycache__/` on-disk
        remnant of Phase 5's deletion — gitignored, never tracked, but the manifest correctly
        skipped it with a WARNING log line rather than copying it, which is exactly the
        defense-in-depth behavior this phase adds)*
- **Timing:** 1.5 hours
- **Depends on:** 4, 5, 6
- **Files to modify:**
  - `code/src/model_checker/theory_lib/docs/usage_guide.md` - merged and deleted
  - `code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md` - absorbs unique content
  - `code/src/model_checker/builder/project.py` - explicit copy manifest
  - `code/pyproject.toml`, `code/MANIFEST.in` - tightened package data
- **Verification:**
  - Wheel contents diff shows only removals, all enumerated.
  - `builder/tests/integration/test_generated_projects.py` passes.
  - A scaffolded project for each theory contains only canonical-contract items.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 8: Write the RED Theory-Conformance Test [COMPLETED]

- **Goal:** Encode the Phase 3 contract as an executable, parametrized test that fails now on every
  known gap — the RED baseline the per-theory phases flip green.
- **Tasks:**
  - [x] Create `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`, parametrized
        over `AVAILABLE_THEORIES` (later, over the Phase 10 registry). *(completed)*
  - [x] Assert the canonical file set from Phase 3 exists for each theory, and that `semantic` is a
        package (a directory with `__init__.py`), not a module. *(completed: also strengthened
        the package check to require `semantic/core.py` — a bare directory-with-`__init__.py`
        check alone XPASSed for bimodal, since its `semantic/` is a real directory with a real
        `__init__.py` that is nonetheless not the canonical package, just a `sys.modules`
        pickling shim with no `core.py`)*
  - [x] Assert `examples.py` defines `example_range`, `test_example_range`, `semantic_theories`, and
        `unit_tests` — and that each is assigned **exactly once** (parse the module AST; a plain
        `hasattr` check cannot catch logos's duplicate `example_range` at `:142` and `:191`).
        *(completed: two separate assertions — attribute presence and exactly-once assignment —
        both via AST parsing; verified logos's duplicate is at exactly lines 142 and 191 as the
        plan predicted)*
  - [x] Assert `get_theory()` has a uniform signature and returns the expected dict shape
        (`semantics`, `proposition`, `model`, `operators`). *(completed; also caught and xfailed
        logos's divergent `subtheories=` parameter name, mentioned in the plan's Overview but not
        explicitly listed as a Phase 8 task item)*
  - [x] Assert `theory_lib.get_test_examples(name)` succeeds for every theory — this currently
        **raises** for bimodal, whose `examples.py` defines `unit_tests` (`:1357`) but not
        `test_example_range`, against the contract at `theory_lib/__init__.py:135`. *(completed:
        verified bimodal raises ValueError exactly as predicted; live-checked against the actual
        theory_lib/__init__.py:135 contract before writing the xfail)*
  - [x] Assert `iterate.py` exists and exposes `{Theory}ModelIterator`, `iterate_example`, and
        `iterate_example_generator` — this currently fails for bimodal, which has no `iterate.py`
        (deferred to a later phase, out of this plan's current scope). *(completed: two
        assertions — module existence and interface completeness (class name,
        `.returns_generator`, `.__wrapped__`) — both xfailed for bimodal)*
  - [x] Add a parallel parametrized conformance test over `AVAILABLE_SUBTHEORIES` asserting the
        subtheory file set and that `get_operators()` returns a **non-empty** dict — this currently
        fails for relevance, whose `operators.py:27-29` returns `{}`. After a later phase folds
        relevance into constitutive the parametrization will cover four subtheories, all green.
        *(completed: verified relevance's get_operators() returns {} exactly as predicted)*
  - [x] Mark each currently-failing assertion with a narrowly-scoped `xfail` carrying a reason string
        naming the specific defect. Do not use broad module-level skips. *(completed: 9 total
        xfail(strict=True) markers, one per specific defect, each with its own reason string —
        see the Verification note below for the full enumerated list)*
  - [x] Run the suite and confirm the xfail set exactly matches the enumerated known gaps — no
        unexpected passes, no unexpected failures. *(completed: `41 passed, 9 xfailed` — zero
        XPASS, zero unexpected failures. The 9 xfails: bimodal & logos semantic-package
        non-conformance; bimodal missing `test_example_range` (both the attribute-presence and
        `get_test_examples()` assertions); logos duplicate `example_range`; logos non-uniform
        `get_theory()` signature; bimodal missing `iterate.py` (both the existence and
        interface-completeness assertions); relevance's empty `get_operators()`. Proved the
        xfail markers have teeth by deliberately breaking the `RELEVANCE_EMPTY_OPERATORS_XFAIL_REASON`
        binding on a scratch copy — collection failed loudly (`NameError`) rather than silently
        passing; restored via diff-verified copy before committing.)*
- **Timing:** 2 hours
- **Depends on:** 3
- **Files to modify:**
  - `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` - new
- **Verification:**
  - The test runs and reports exactly the enumerated xfails; zero XPASS.
  - Temporarily removing an xfail marker produces a real, informative failure.

---

### Phase 9: Write the RED Layering Test and Declare the Three-Layer Model [NOT STARTED]

- **Goal:** Make the core/theory_lib boundary enforced rather than aspirational. This is the durable
  substitute for directory position and the reason relocation is unnecessary.
- **Tasks:**
  - [ ] Create `code/tests/test_layering.py` walking the AST of every module under
        `code/src/model_checker/` and classifying it into the three layers declared in Phase 3.
  - [ ] Assert that no **core** module (`models`, `syntactic`, `solver`, `utils`, `iterate`,
        `builder`, `settings`, `output`, `z3_shim`) contains an `Import`/`ImportFrom` node naming
        `model_checker.theory_lib` — including function-local imports, which is how all 10 current
        inversions evade notice today.
  - [ ] Additionally assert no core module contains a **string literal** matching
        `model_checker.theory_lib`. This is essential: `utils/version.py:37,63`,
        `builder/loader.py:137`, `builder/runner.py:867`, and `jupyter/utils.py:113` reach
        `theory_lib` via `importlib.import_module(f"model_checker.theory_lib.{...}")`, which a pure
        import-node check would miss entirely.
  - [ ] Assert no core module hardcodes any theory name (`bimodal`, `exclusion`, `imposition`,
        `logos`) as a string literal — this catches the `builder/loader.py:185-201` drift and the
        `jupyter/adapters.py:91-94` map.
  - [ ] Explicitly list the upper layer (`model_checker/__init__.py`, `model_checker/api.py`,
        `__main__.py`, `jupyter/`) as permitted to import both, with the allowance recorded in the
        test itself as a named constant rather than a scattered exemption.
  - [ ] Run it and confirm it **fails RED**, reporting all current violations: `utils/api.py:52,57`,
        `utils/version.py:37,57,63`, `jupyter/display.py:270,380`, `jupyter/environment.py:166`,
        `jupyter/interactive.py:35,100,233,288`, `jupyter/utils.py:113`, `builder/loader.py:137,185-201`,
        `builder/runner.py:867`, `builder/strategies.py:290`.
  - [ ] Consider `import-linter` as an alternative or supplement; if adopted, add the contract to
        `pyproject.toml`. A plain pytest is acceptable and adds no dependency.
- **Timing:** 1.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `code/tests/test_layering.py` - new
- **Verification:**
  - The test fails, and its failure output enumerates each violation with file:line.
  - Every site listed above appears in the output; no false positives on `theory_lib`'s own modules.

---

### Phase 10: Introduce the Core Theory Registry [NOT STARTED]

- **Goal:** Create one registration-based registry that core can query without ever hardcoding theory
  names or the `theory_lib` import path — the mechanism that makes the one-way dependency achievable.
- **Tasks:**
  - [ ] Create `code/src/model_checker/registry.py` in the core layer: an initially **empty**
        registry with `register_theory(name, *, module_path, semantics, proposition, model,
        operators, adapter=None)`, `get_registered()`, `get_theory_entry(name)`, and
        `iter_theories()`. Core owns the mechanism; core never owns the names.
  - [ ] Have `theory_lib/__init__.py` register all four theories into it at import time, deriving
        entries from the existing lazy `__getattr__` machinery so nothing loads eagerly. Direction
        stays one-way: `theory_lib` imports core.
  - [ ] Redefine `AVAILABLE_THEORIES` as a view over the registry rather than an independent literal
        list, preserving its public name and iteration order (it is public API).
  - [ ] Demote `discover_theories()` to a development-only lint that compares the filesystem scan
        against the registry and reports drift, rather than acting as a second source of truth.
  - [ ] Add a bootstrap point in the upper layer so core consumers that need "all theories" get them:
        `model_checker/__init__.py` (or a new thin `model_checker/api.py`) imports `theory_lib` to
        trigger registration. Core modules query the registry; they never import `theory_lib`.
  - [ ] Add unit tests for the registry: registration, duplicate-name rejection (fail-fast),
        unknown-name lookup raising with the available list in the message.
  - [ ] Repoint the Phase 8 conformance test to parametrize over the registry instead of the literal.
- **Timing:** 1.5 hours
- **Depends on:** 9
- **Files to modify:**
  - `code/src/model_checker/registry.py` - new
  - `code/src/model_checker/theory_lib/__init__.py` - registers theories; `AVAILABLE_THEORIES` becomes a view
  - `code/src/model_checker/__init__.py` - bootstrap import
  - `code/tests/unit/test_registry.py` - new
- **Verification:**
  - `from model_checker.theory_lib import AVAILABLE_THEORIES` still yields the same four names in
    the same order.
  - `registry.py` contains no theory-name string literals.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 11: Fix the Examples Contract Bugs and Unify get_theory Signatures [NOT STARTED]

- **Goal:** Flip the first group of conformance xfails green by fixing live defects.
- **Tasks:**
  - [ ] `theory_lib/bimodal/examples.py`: add `test_example_range` (the other three theories assign
        `test_example_range = unit_tests` — exclusion at `:957`, imposition at `:952`, logos at
        `:140`). This fixes `theory_lib.get_test_examples('bimodal')`, which currently raises.
  - [ ] `theory_lib/logos/examples.py`: remove the duplicate `example_range` assignment. It is set at
        `:142` (with the comment "Required by `get_examples()`") and again at `:191`. Keep one,
        placed after `unit_tests` is final, and confirm the surviving value is the intended one.
  - [ ] Unify `get_theory` signatures: `logos/__init__.py:31` uses `get_theory(subtheories=None)`
        while bimodal (`:70`), exclusion (`:48`), and imposition (`:80`) use `get_theory(config=None)`.
        Adopt `get_theory(config=None)` everywhere; logos additionally accepts `subtheories=None` as
        a keyword-only argument. No compatibility shim — update all call sites in the same commit
        per the no-backwards-compatibility policy.
  - [ ] Grep for and update every `get_theory(` call site across `code/`, `oracle/`, and `docs/`.
  - [ ] Remove the corresponding xfail markers from the conformance test.
- **Timing:** 1 hour
- **Depends on:** 8
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/examples.py` - add `test_example_range`
  - `code/src/model_checker/theory_lib/logos/examples.py` - remove duplicate `example_range`
  - `code/src/model_checker/theory_lib/logos/__init__.py` - signature unification
  - call sites across `code/`, `oracle/`, `docs/`
- **Verification:**
  - `theory_lib.get_test_examples(t)` succeeds for all four theories.
  - The examples-contract and signature xfails are gone; those assertions pass.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 12: Move Theory-Aware Core Helpers to the Upper Layer [NOT STARTED]

- **Goal:** Eliminate the `utils/` half of the layering inversions.
- **Tasks:**
  - [ ] `utils/api.py:48-64`: the `get_theory`-style helper falls back to
        `from model_checker.theory_lib import get_semantic_theories` (`:52`) and
        `AVAILABLE_THEORIES` (`:57`). Move the theory-aware fallback into a new thin upper-layer
        `model_checker/api.py`; leave in `utils/api.py` only the pure lookup that operates on an
        already-supplied `semantic_theories` mapping.
  - [ ] `utils/version.py`: `get_theory_version` (`:37`) and `check_theory_compatibility` (`:57,63`)
        both reach into `theory_lib`, the latter via both a static import and a string-literal
        `importlib`. Move both into `theory_lib/meta_data.py`, which already owns per-theory version
        and metadata concerns and already imports from `theory_lib` (`:22`, `:258`). Leave
        `get_model_checker_version()` in `utils/version.py` — it is genuinely core.
  - [ ] Update all importers of the moved functions; no re-export shims.
  - [ ] Confirm `model_checker/__init__.py`'s public surface is unchanged for anything users import.
  - [ ] Re-run the layering test: `utils/` violations should be gone; `jupyter/` and `builder/`
        violations remain (Phases 13 and 15).
- **Timing:** 1.5 hours
- **Depends on:** 10
- **Files to modify:**
  - `code/src/model_checker/utils/api.py` - theory-aware fallback removed
  - `code/src/model_checker/utils/version.py` - theory-aware helpers removed
  - `code/src/model_checker/api.py` - new upper-layer module
  - `code/src/model_checker/theory_lib/meta_data.py` - absorbs version/compatibility helpers
- **Verification:**
  - The layering test reports zero violations under `utils/`.
  - `code/src/model_checker/theory_lib/tests/test_meta_data.py` passes.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 13: Derive builder Theory Identity from the Registry [NOT STARTED]

- **Goal:** Remove builder's hardcoded theory knowledge and path sniffing — including a live drift bug.
- **Tasks:**
  - [ ] Fix the live drift at `builder/loader.py:185-201`: `prop_to_theory` maps only
        `{'BimodalProposition': 'bimodal'}` and `theory_patterns` only `{'Bimodal': 'bimodal'}`.
        Exclusion, imposition, and logos were never restored to these dicts after the theory
        restoration, so theory identification silently falls through to the Method-4 name fallback
        for three of four theories. Replace both dicts with registry queries over the registered
        `proposition` and `model` classes, which fixes the drift structurally rather than by adding
        three more literals.
  - [ ] Replace the path-substring sniff at `builder/loader.py:93`
        (`'model_checker/theory_lib' in str(module_path) or 'model_checker\\theory_lib' in ...`,
        including the Windows backslash variant) with a registry lookup keyed on the resolved module
        name.
  - [ ] Replace the equivalent path assumption at `builder/strategies.py:285-295` the same way.
  - [ ] Replace the string-literal dynamic imports at `builder/loader.py:137`
        (`__import__(f"model_checker.theory_lib.{theory_name}")`) and `builder/runner.py:867`
        (`importlib.import_module(f"model_checker.theory_lib.{module_name}")`) with the registry's
        `module_path` entry, so the dotted prefix lives in `theory_lib`, not in core.
  - [ ] Leave `builder/serialize.py` alone: it serializes by `__module__` string (`:49`, `:118-126`)
        and rehydrates via `importlib` (`:71,145,173,195`). Because no packages are renamed, its
        behavior is unaffected — but run `builder/tests/unit/test_serialize.py` as a phase gate to
        prove it.
  - [ ] Re-run the layering test: `builder/` violations should be gone.
- **Timing:** 2 hours
- **Depends on:** 10
- **Files to modify:**
  - `code/src/model_checker/builder/loader.py` - registry-derived identification, no path sniffing
  - `code/src/model_checker/builder/strategies.py` - registry-derived path handling
  - `code/src/model_checker/builder/runner.py` - registry-supplied module path
- **Verification:**
  - Theory identification returns the correct theory for all four (add a regression test covering
    the three that were silently broken).
  - `builder/tests/unit/test_serialize.py` and `builder/tests/integration/test_generated_projects.py`
    pass.
  - The layering test reports zero violations under `builder/`.

---

### Phase 14: Normalize imposition [NOT STARTED]

- **Goal:** Bring the simplest theory fully onto the canonical contract, proving the pattern before
  the harder ones.
- **Tasks:**
  - [ ] Imposition already has `semantic/` (`core.py` 338, `helpers.py` 154, `model.py` 458,
        `__init__.py` 34), `iterate.py` (533), `operators.py`, `notebooks/`, and the six-file
        `docs/` set. Verify each against the Phase 3 contract and close the specific gaps.
  - [ ] Add `tests/conftest.py` (exclusion and logos have one; imposition and bimodal do not).
  - [ ] Confirm `semantic/__init__.py` is re-export-only and that the module names match the
        canonical set (`core.py`, `model.py`, plus theory-specific extras — `helpers.py` qualifies).
  - [ ] Confirm `theory_lib/imposition/__init__.py` registers into the Phase 10 registry correctly.
  - [ ] Remove the corresponding conformance xfails for imposition; the imposition parametrization
        should be fully green at the end of this phase.
  - [ ] Record the exact normalization steps taken as the template for Phases 17, 18, 20, 21.
- **Timing:** 1.5 hours
- **Depends on:** 11
- **Files to modify:**
  - `code/src/model_checker/theory_lib/imposition/tests/conftest.py` - new
  - `code/src/model_checker/theory_lib/imposition/semantic/__init__.py` - re-export-only if not already
- **Verification:**
  - Conformance test is green for `imposition` with zero xfails.
  - `pytest code/src/model_checker/theory_lib/imposition/tests` passes at or above baseline.

---

### Phase 15: Reclassify jupyter/ and Remove Its Hardcoded Theory Knowledge [NOT STARTED]

- **Goal:** Resolve the 7 remaining inversions, which all live in `jupyter/`.
- **Tasks:**
  - [ ] Formally classify `jupyter/` as the upper layer (per Phase 3): it legitimately needs to know
        about theories, so the fix is a correct layer assignment plus removal of *hardcoded* theory
        knowledge — not removal of the dependency.
  - [ ] Replace the hardcoded adapter registry at `jupyter/adapters.py:89-95` (a dict literal mapping
        all four theory names to adapter classes) with registry-driven lookup: theories supply their
        adapter through the Phase 10 `register_theory(..., adapter=...)` parameter, defaulting to
        `DefaultTheoryAdapter`. `jupyter/` stops enumerating theories.
  - [ ] Replace `jupyter/interactive.py:35` and `:100` (`from model_checker.theory_lib import logos,
        exclusion` — two theories hardcoded, two omitted) with registry iteration.
  - [ ] Route `jupyter/interactive.py:233,288` and `jupyter/display.py:270,380`
        (`get_semantic_theories`) and `jupyter/environment.py:166` (`AVAILABLE_THEORIES`) through the
        Phase 12 `model_checker/api.py` upper-layer surface.
  - [ ] Replace the string-literal `importlib` at `jupyter/utils.py:113,156` with the registry's
        `module_path`.
  - [ ] Confirm the layering test's upper-layer allowance covers `jupyter/` explicitly and that its
        theory-name-literal assertion now passes for `jupyter/`.
- **Timing:** 1.5 hours
- **Depends on:** 10, 13
- **Files to modify:**
  - `code/src/model_checker/jupyter/adapters.py` - registry-driven adapter lookup
  - `code/src/model_checker/jupyter/interactive.py` - registry iteration
  - `code/src/model_checker/jupyter/{display,environment,utils}.py` - routed through the api layer
- **Verification:**
  - No theory-name string literals remain anywhere in `jupyter/`.
  - Jupyter adapter selection returns the correct adapter for all four theories.
  - The layering test reports zero theory-name-literal violations repo-wide.

---

### Phase 16: Relocate builder/z3_utils.py into iterate/ [NOT STARTED]

- **Goal:** Move iteration-domain logic out of the orchestration package, and remove dead imports.
- **Tasks:**
  - [ ] First, delete the dead import block at `builder/example.py:29-32`
        (`create_difference_constraint`, `extract_model_values`, `find_next_model as
        find_next_z3_model`). All three are unused — residue from the removal of
        `BuildExample.find_next_model`; grep confirms no call sites remain in the file. This is a
        zero-risk change that leaves `z3_utils` with only its own test as a consumer.
  - [ ] Move `builder/z3_utils.py` (116 lines: `create_difference_constraint` `:10`,
        `extract_model_values` `:48`, `find_next_model` `:78`) to `iterate/z3_utils.py`. "Find a
        model differing from the previous one" is the core iteration primitive and has zero remaining
        builder-side callers. No import cycle results: `iterate/constraints.py` already imports
        `z3_shim` the same way.
  - [ ] Move `builder/tests/unit/test_z3_utils.py` (12 tests) to `iterate/tests/unit/`. Fix its
        import of raw `z3` at `:9` to use `z3_shim`, matching the module under test.
  - [ ] Note but do **not** act on the functional overlap with
        `iterate/constraints.py:149` (`ConstraintGenerator._create_difference_constraint`), which
        operates on a list of *models* rather than a flat variable list. Folding the two requires
        reconciling a `List[ExprRef]` vs `List[ModelRef]` signature mismatch; record it as a
        follow-up in the Phase 26 ROADMAP update rather than doing it here.
- **Timing:** 1 hour
- **Depends on:** 13
- **Files to modify:**
  - `code/src/model_checker/builder/example.py` - dead import block removed
  - `code/src/model_checker/builder/z3_utils.py` - moved to `iterate/z3_utils.py`
  - `code/src/model_checker/builder/tests/unit/test_z3_utils.py` - moved to `iterate/tests/unit/`
- **Verification:**
  - The 12 relocated tests pass in their new home.
  - `grep -rn "z3_utils" code/src/model_checker/builder/` returns nothing.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 17: Normalize exclusion [NOT STARTED]

- **Goal:** Bring exclusion onto the canonical contract; its `semantic/__init__.py` carries inline
  class bodies that belong in named modules.
- **Tasks:**
  - [ ] `exclusion/semantic/__init__.py` is 600 lines — far more than a re-export shim — alongside
        `core.py` (566), `constraints.py` (174), `model.py` (78), and `registry.py` (125). Move the
        inline class bodies out of `__init__.py` into the appropriate named modules, leaving
        `__init__.py` as re-export-only per the contract.
  - [ ] Preserve the public import path exactly: `from model_checker.theory_lib.exclusion.semantic
        import WitnessSemantics, WitnessStructure, WitnessRegistry, WitnessProposition` must keep
        working unchanged — `tests/integration/test_semantic_coverage.py` alone exercises it at
        `:12,17,22,27,36,46,61,76,93,111`.
  - [ ] Verify `__module__` values for classes reachable through `builder/serialize.py` remain
        resolvable after the move; run `builder/tests/unit/test_serialize.py` as a gate.
  - [ ] Align internal module names with imposition's set where the concepts match (`core.py`,
        `model.py`), keeping theory-specific modules (`constraints.py`, `registry.py`) as extras.
  - [ ] Close remaining contract gaps; `docs/` already has the six-file set plus `DATA.md`, which is
        a permitted theory-specific extra.
  - [ ] Remove exclusion's conformance xfails.
- **Timing:** 2 hours
- **Depends on:** 14
- **Files to modify:**
  - `code/src/model_checker/theory_lib/exclusion/semantic/__init__.py` - reduced to re-exports
  - `code/src/model_checker/theory_lib/exclusion/semantic/{core,model,constraints,registry}.py` - absorb the inline classes
- **Verification:**
  - Conformance test is green for `exclusion` with zero xfails.
  - Every import path exercised in `tests/integration/test_semantic_coverage.py` still resolves.
  - `pytest code/src/model_checker/theory_lib/exclusion/tests` passes at or above baseline.

---

### Phase 18: Normalize logos — Split semantic.py into a Package [NOT STARTED]

- **Goal:** Convert logos's flat 1,283-line `semantic.py` into the canonical `semantic/` package.
- **Tasks:**
  - [ ] Create `logos/semantic/` with `core.py` (`LogosSemantics`), `model.py`
        (`LogosModelStructure`), `proposition.py` (`LogosProposition`), and a re-export-only
        `__init__.py`. Delete the flat `semantic.py` in the same commit.
  - [ ] The public path `model_checker.theory_lib.logos.semantic` must keep resolving identically —
        it is the most widely imported module in the tree, including from *other theories*:
        `imposition/__init__.py:53`, `imposition/semantic/core.py:10`, `imposition/semantic/model.py:15`,
        `exclusion/examples.py:69`, every logos subtheory's `operators.py` (`TYPE_CHECKING` imports),
        and roughly a dozen test modules.
  - [ ] Verify `builder/serialize.py` round-trips logos classes after the split; the `__module__`
        strings change from `...logos.semantic` to `...logos.semantic.core`. Because
        `serialize.py` rehydrates via `importlib` on the recorded `__module__`, the new value must be
        importable — it will be, but assert it with a test rather than assuming.
  - [ ] Run the full logos suite plus all five subtheory suites plus imposition and exclusion (both
        depend on logos semantics).
  - [ ] Remove logos's structural conformance xfails.
- **Timing:** 2 hours
- **Depends on:** 17
- **Files to modify:**
  - `code/src/model_checker/theory_lib/logos/semantic.py` - split and deleted
  - `code/src/model_checker/theory_lib/logos/semantic/{__init__,core,model,proposition}.py` - new
- **Verification:**
  - `from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition,
    LogosModelStructure` works.
  - `builder/tests/unit/test_serialize.py` passes, including a new logos round-trip case.
  - imposition, exclusion, and all logos subtheory suites pass at or above baseline.

---

### Phase 19: Fold the relevance Subtheory into constitutive [NOT STARTED]

- **Goal:** Remove a subtheory that contributes zero operators, without losing its example corpus or
  documentation.
- **Tasks:**
  - [ ] Confirm the evidence before acting. `relevance/operators.py:27-29` returns `{}`; its only
        real content is `from ..constitutive.operators import RelevanceOperator` at `:9`, kept alive
        solely so `__init__.py:15` can re-export it. The sole class definition is
        `constitutive/operators.py:376`, registered under `"\\preceq"` at
        `constitutive/operators.py:565`, and it reaches consumers through the
        `'relevance': ['constitutive']` dependency edge at `logos/operators.py:38`. Decisively:
        `relevance/examples.py`'s own registry loads `['extensional', 'constitutive', 'modal']` and
        not `'relevance'`, and removing `'relevance'` from `test_relevance_examples.py:35` leaves all
        20 tests passing. Loading the subtheory is a no-op.
  - [ ] Move the 20 examples (11 countermodels `REL_CM_1`-`REL_CM_11` at
        `relevance/examples.py:56-258`, 9 theorems `REL_TH_1`-`REL_TH_9` at `:265-435`) into
        `constitutive/examples.py`, retaining the `REL_` prefixes so their provenance stays legible.
        Note that only 4 of 20 are uncommented in `example_range` at `:496`; preserve that state
        rather than silently enabling 16 untested examples.
  - [ ] Move `relevance/tests/test_relevance_examples.py` into `constitutive/tests/` (or merge its
        parametrize source). Net collection across the two directories should stay at 54.
  - [ ] Preserve the documentation: `relevance/README.md` (~20 KB of substantive relevance-logic
        exposition) and `relevance/notebooks/` move under `constitutive/`. Do not delete them — the
        operator's home changes, the scholarship does not.
  - [ ] Delete `relevance/operators.py` and `relevance/__init__.py`; remove the `'relevance'` entries
        at `subtheories/__init__.py:24` and `:32`, and the dependency edge at `logos/operators.py:38`.
  - [ ] Update `SUBTHEORY_DESCRIPTIONS` for constitutive at `subtheories/__init__.py:30` to name
        `≼` explicitly alongside `≡`, `≤`, `⊑`.
  - [ ] Remove `'relevance'` from **every** call site that names it as a loadable subtheory. Remove
        it from `AVAILABLE_SUBTHEORIES` first so any missed site fails fast at load time. Known
        sites: `logos/__init__.py:37,152`; `logos/examples.py:117,175,201,210`;
        `logos/tests/integration/test_subtheory_orchestration.py:32`;
        `logos/tests/integration/test_solver_comparison.py:102`; `code/run_tests.py:327,508`. Two
        further sites are already handled by earlier phases: `code/scaling_benchmark.py:184,204,231,642`
        is deleted in Phase 5, and `logos/comparison.py:76,492,997` is relocated in Phase 6 — verify
        both, and update the relocated benchmark script.
  - [ ] Remove the subtheory-conformance xfail for relevance; the parametrization now covers four
        subtheories.
- **Timing:** 2 hours
- **Depends on:** 18
- **Files to modify:**
  - `code/src/model_checker/theory_lib/logos/subtheories/relevance/` - operators, `__init__`, examples, tests removed; docs and notebooks relocated
  - `code/src/model_checker/theory_lib/logos/subtheories/constitutive/{examples.py,tests/,README.md,notebooks/}` - absorb relevance content
  - `code/src/model_checker/theory_lib/logos/subtheories/__init__.py` - registry and descriptions
  - `code/src/model_checker/theory_lib/logos/{operators.py,__init__.py,examples.py}` - dependency edge and call sites
  - `code/run_tests.py`, `code/scripts/logos_solver_benchmark.py` - call sites
- **Verification:**
  - Subtheory conformance is green for all four remaining subtheories with zero xfails.
  - `grep -rn "'relevance'" code/ ` returns nothing outside relocated documentation prose.
  - A full logos load still resolves `\preceq`; constitutive's suite collects 54 tests and passes.
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 20: Normalize bimodal, Part 1 — Collapse the Dual Module Identity [NOT STARTED]

- **Goal:** Eliminate the highest-risk defect in the tree: `BimodalSemantics` currently exists as two
  distinct class objects. Do this as a **pure move with no content split**, so any regression is
  unambiguously attributable.
- **Tasks:**
  - [ ] Understand the hazard precisely before touching anything.
        `bimodal/semantic/__init__.py` loads the sibling `bimodal/semantic.py` (3,194 lines) via
        `importlib.util.spec_from_file_location`, executing that file a second time under the module
        identity `bimodal_semantic_module`, then re-exports `BimodalSemantics`,
        `BimodalProposition`, and `BimodalStructure` from it. The file therefore runs twice under two
        identities and cross-path `isinstance` checks silently fail.
  - [ ] Note the load-bearing detail recorded in that file's own comment: `sys.modules[spec.name] =
        semantic_module` exists specifically because `--maximize` pickles semantics classes across a
        `ProcessPoolExecutor`, and without the registration the worker raises
        `ModuleNotFoundError: No module named 'bimodal_semantic_module'` and the example silently
        reports "Maximum N = 0". **Preserving pickling correctness is this phase's primary
        acceptance criterion.**
  - [ ] Move the entire contents of `bimodal/semantic.py` into `bimodal/semantic/core.py` verbatim —
        no reorganization, no splitting. Delete `bimodal/semantic.py`.
  - [ ] Rewrite `bimodal/semantic/__init__.py` as a plain re-export-only module. Delete the
        `spec_from_file_location` block, the manual `sys.modules` registration, and the `sys` /
        `importlib.util` / `pathlib` imports it required.
  - [ ] Update the two intra-package imports at `bimodal/semantic.py:40-41`
        (`...bimodal.semantic.witness_registry`, `...bimodal.semantic.witness_constraints`) to
        relative imports within the package.
  - [ ] Run `bimodal/tests/unit/test_semantic_module_registration.py` — it exists precisely to guard
        this contract — plus a real `--maximize` invocation over a bimodal example, before and after.
  - [ ] Add a regression test asserting `BimodalSemantics` has exactly one class identity:
        `isinstance` succeeds across both the package path and any previously divergent path.
- **Timing:** 2 hours
- **Depends on:** 18
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic.py` - moved to `semantic/core.py`, deleted
  - `code/src/model_checker/theory_lib/bimodal/semantic/__init__.py` - reduced to re-exports
  - `code/src/model_checker/theory_lib/bimodal/semantic/{witness_registry,witness_constraints}.py` - relative imports
- **Verification:**
  - `test_semantic_module_registration.py` passes.
  - `model-checker <bimodal example> --maximize` produces a non-zero Maximum N, matching the
    pre-phase output.
  - The single-class-identity regression test passes.
  - `bimodal_semantic_module` appears nowhere in the tree.
  - Bimodal in-package suite is 286/286 with `-n 6`.

---

### Phase 21: Normalize bimodal, Part 2 — Split semantic/core.py into the Canonical File Set [NOT STARTED]

- **Goal:** Break the 3,194-line module into the canonical layout now that the module identity is
  single and the pattern is proven on three other theories.
- **Tasks:**
  - [ ] Split `bimodal/semantic/core.py` into `core.py` (`BimodalSemantics`), `model.py`
        (`BimodalStructure`), and `proposition.py` (`BimodalProposition`), matching the layout
        established in Phases 14, 17, and 18. Keep `witness_registry.py` and
        `witness_constraints.py` as theory-specific extras.
  - [ ] Keep `semantic/__init__.py` re-export-only and the public path
        `model_checker.theory_lib.bimodal.semantic` byte-identical from the importer's view. It is
        imported by roughly a dozen bimodal test modules and by `oracle/bimodal_logic/provider.py`.
  - [ ] Re-verify pickling after the split — `__module__` values change again, so run the
        `--maximize` check and `test_semantic_module_registration.py` a second time.
  - [ ] Run the oracle suite explicitly: `oracle/` is a live external consumer of
        `model_checker.theory_lib.bimodal` and is invisible to the default test commands.
  - [ ] Add `bimodal/tests/conftest.py` for uniformity with exclusion and logos.
  - [ ] Remove bimodal's structural conformance xfails.
- **Timing:** 2 hours
- **Depends on:** 20
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/semantic/{core,model,proposition,__init__}.py` - split
  - `code/src/model_checker/theory_lib/bimodal/tests/conftest.py` - new
- **Verification:**
  - Bimodal in-package suite is 286/286 with `-n 6`.
  - Oracle suite (550 tests) matches the Phase 2 baseline, with the 5 strict xfails still xfailing.
  - `code/scripts/compare_bimodal_baseline.sh` output matches baseline.
  - `--maximize` still works.

---

### Phase 22: Restore bimodal iterate.py and Unify the Test Layout [NOT STARTED]

- **Goal:** Close the last contract gap by restoring the one missing iterator, fixing a live
  reachable defect in the process.
- **Tasks:**
  - [ ] Understand why this is a defect and not a design choice. `bimodal` has no `iterate.py` while
        exclusion (305 lines), imposition (533), and logos (470) do. It was deleted deliberately in
        commit `9b76ffa2` ("remove bimodal iterate dependency", Option A), but that was
        dependency-cutting during an unrelated restoration, not a judgment that the semantics were
        wrong. The gap is live and reachable: `bimodal/semantic.py:68` still declares `'iterate': 1`
        in `DEFAULT_EXAMPLE_SETTINGS`, so a user setting `iterate: 2` on a bimodal example reaches
        `builder/runner.py:875` and gets `ImportError: Theory module 'bimodal' does not provide an
        iterate_example function`. A 410-line `bimodal/docs/ITERATE.md` still documents the removed
        API (`:37`, `:62`).
  - [ ] Restore with `git show 9b76ffa2^:code/src/model_checker/theory_lib/bimodal/iterate.py`. The
        blob is 611 lines, compiles, and all three of its imports still resolve today:
        `BaseModelIterator` (`iterate/core.py:46`), `bitvec_to_worldstate` (`utils/bitvector.py:125`),
        `pretty_set_print` (`utils/formatting.py:12`). Use the established in-repo restore-and-port
        recipe already applied to exclusion and imposition (commits `71da2978`, `36d4997d`).
  - [ ] Port to current conventions using `imposition/iterate.py` as the template. Specifically, add
        `iterate_example_generator` with the `.returns_generator` and `.__wrapped__` markers
        (`imposition/iterate.py:504,533-534`) that `builder/runner.py:879-889` keys off — the 611-line
        blob predates that convention and exposes only `iterate_example` (`:591`).
  - [ ] Two referenced `BimodalStructure` attributes no longer exist — `detect_model_differences`
        and `_get_friendly_letter_name`. Both are already `hasattr`-guarded in the restored source
        (`:60`, `:427`), as are `semantics.task_rel` (`:219`) and `semantics.state_str_to_bitvec`
        (`:180`), so they degrade rather than crash. Verify each guard rather than assuming, and
        decide per attribute whether to restore the capability or leave the graceful degradation.
  - [ ] Re-export `iterate_example` and `iterate_example_generator` from `bimodal/__init__.py`,
        matching exclusion (`:10`), imposition (`:43`), and logos (`:19`).
  - [ ] Write a fresh `bimodal/tests/integration/test_iterate.py` modelled on
        `imposition/tests/integration/test_iterate.py`. Do **not** restore the original 156-line
        version: it is Mock-heavy and mocks structure attributes (`worlds`, `time_points`) that no
        longer match the current `BimodalStructure`.
  - [ ] Verify `bimodal/docs/ITERATE.md`'s documented API matches the restored module, and correct it
        where it does not.
  - [ ] Delete `bimodal/tests/e2e/` — it contains only a `__pycache__`, has no `__init__.py`, and its
        sole file was deliberately removed. No other theory has an e2e directory.
  - [ ] Extend the existing theory parametrization in `code/tests/e2e/test_project_creation.py`
        (currently `test_project_creation_all_theories[bimodal]`) to cover exclusion, imposition, and
        logos, so end-to-end coverage reaches every theory from one place.
  - [ ] Record "add `notebooks/` for bimodal and logos" as a ROADMAP follow-up in Phase 26 rather
        than fabricating notebook content here.
  - [ ] Remove the remaining `iterate.py` conformance xfail.
- **Timing:** 2 hours
- **Depends on:** 19, 21
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/iterate.py` - restored and ported
  - `code/src/model_checker/theory_lib/bimodal/__init__.py` - re-exports the iteration API
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - new, written fresh
  - `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` - reconciled with the restored API
  - `code/src/model_checker/theory_lib/bimodal/tests/e2e/` - deleted
  - `code/tests/e2e/test_project_creation.py` - parametrization extended to all four theories
- **Verification:**
  - `from model_checker.theory_lib.bimodal import iterate_example, iterate_example_generator` works.
  - A bimodal example with `iterate: 2` produces two distinct models instead of `ImportError`.
  - Conformance test is green for `iterate.py` across all four theories with zero xfails.
  - Bimodal in-package suite passes at or above the 286 baseline (it will exceed it by the new
    iteration tests — enumerate the delta).
  - `bash code/scripts/verify-refactor.sh` exits 0.

---

### Phase 23: Flip the Conformance and Layering Tests Fully Green [NOT STARTED]

- **Goal:** Prove the contract and the boundary are fully enforced, with no carried exceptions.
- **Tasks:**
  - [ ] Remove every remaining `xfail` marker from the conformance test and confirm all
        parametrizations pass for all four theories and all five subtheories.
  - [ ] Confirm the layering test passes with zero violations: no core module imports `theory_lib`
        statically, no core module contains a `model_checker.theory_lib` string literal, and no core
        module contains a theory-name string literal.
  - [ ] Add a guard test asserting the conformance suite contains **zero** `xfail` markers, so a
        future gap cannot be quietly re-admitted.
  - [ ] Verify `discover_theories()` (now a dev lint) reports zero drift against the registry.
  - [ ] Run the full in-package suite, the oracle suite, and the baseline comparison together.
- **Timing:** 1.5 hours
- **Depends on:** 12, 15, 16, 22
- **Files to modify:**
  - `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` - xfails removed, guard added
  - `code/tests/test_layering.py` - passing
- **Verification:**
  - Both tests pass with zero xfails and zero skips.
  - `bash code/scripts/verify-refactor.sh` exits 0.
  - Test counts meet or exceed the Phase 2 pinned inventories (net of deliberately removed tests,
    each enumerated).

---

### Phase 24: Documentation Reconciliation [NOT STARTED]

- **Goal:** Bring the docs into agreement with the enforced reality. Paths did not change, so the
  blast radius is limited to files whose *claims* changed.
- **Tasks:**
  - [ ] `THEORY_ARCHITECTURE.md`: final pass confirming it matches what the conformance test actually
        enforces, including the layering section and the iteration declaration.
  - [ ] `CLAUDE.md`: fix two stale claims — "All theories follow standard structure (semantic.py,
        operators.py, examples.py)" is now false (it is `semantic/`, and the required set is larger),
        and the Specs Directory Protocol section lists `specs/baselines/` for test regression
        baselines when they actually live in the per-task directories `specs/118_*/baselines/` and
        `specs/122_*/baselines/`. Correct both.
  - [ ] `theory_lib/docs/CONTRIBUTING.md:85-96` mandates a per-theory `e2e/` directory that zero of
        four theories have. Correct it to describe the actual policy: e2e lives at core level,
        parametrized over theories.
  - [ ] Six module test READMEs document `e2e/` sections that do not exist: `iterate/tests/README.md:29`,
        `settings/tests/README.md:15`, `models/tests/README.md:27`, `output/tests/README.md:20,89`,
        `syntactic/tests/README.md:18`, `utils/tests/README.md:17`. `builder/tests/README.md:44`
        claims 17 e2e tests where 13 collect. Correct each to match reality.
  - [ ] Update `theory_lib/README.md` and `theory_lib/docs/README.md` for the removed spatial
        subtheory, the folded relevance subtheory (four subtheories now, not five), and the canonical
        module set.
  - [ ] Update the affected per-theory `docs/ARCHITECTURE.md` files for logos and bimodal (semantic
        package splits) and exclusion (module reorganization); update `logos/docs/` for the
        subtheory-count change.
  - [ ] Update `builder/README.md` if the registry change alters described behavior; update
        `docs/` references to the relocated solver benchmark.
  - [ ] Sweep `docs/` and `code/docs/` for references to deleted paths (`spatial/`, `boneyard/`,
        `history/`, `examples_refactored/`, `reports/`, `usage_guide.md`, `logos/comparison.py`) and
        fix each.
  - [ ] **MUST NOT** cite task numbers in any file outside `specs/**` — this includes `CLAUDE.md`,
        `THEORY_ARCHITECTURE.md`, all theory docs, and all `docs/` content. Use durable anchors:
        sibling document names, section headings, and verified facts.
- **Timing:** 2 hours
- **Depends on:** 23
- **Files to modify:**
  - `CLAUDE.md` - two stale claims corrected
  - `code/src/model_checker/theory_lib/{README.md,docs/README.md,docs/THEORY_ARCHITECTURE.md}`
  - `code/src/model_checker/theory_lib/{logos,bimodal,exclusion}/docs/ARCHITECTURE.md`
  - `docs/`, `code/docs/` - stale path references
- **Verification:**
  - No documentation references a deleted path.
  - `grep -rnEi 'task [0-9]+' --include=*.md . | grep -v '^./specs/'` returns nothing.
  - Every relative markdown link in the changed files resolves.

---

### Phase 25: Full Regression Gate and Wheel Parity Diff [NOT STARTED]

- **Goal:** Final acceptance. Because no 1.3.0 was published before the refactor, the gate is local
  evidence rather than a published-artifact diff.
- **Tasks:**
  - [ ] Run `bash code/scripts/verify-refactor.sh` in full and confirm exit 0.
  - [ ] Run the complete in-package suite from `code/` and compare against the Phase 2 pinned
        inventory. Enumerate every count delta with its cause (tests added by this refactor, tests
        removed with cruft); no unexplained deltas.
  - [ ] Run the oracle suite (550 tests) and confirm the 5 `xfail(strict=True)` cross-oracle
        differentials are still xfailing — an XPASS flip is a failure, not an improvement, and must
        be investigated before proceeding.
  - [ ] Run `code/scripts/compare_bimodal_baseline.sh` and confirm it matches.
  - [ ] Build the wheel and diff its contents against **both** the Phase 2 pre-refactor manifest and
        `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/wheel-contents.txt`. Produce an
        enumerated delta list; every entry must be an intended removal (cruft, spatial, dead
        wrappers, relocated benchmark, case-collision duplicate) or an intended addition (new
        semantic package modules, registry, conformance tests). Any unexplained entry blocks
        acceptance.
  - [ ] Scaffold a project for each theory and run its examples end to end.
  - [ ] Run `model-checker` CLI smoke checks including `--maximize` and `--save`.
  - [ ] Record all results under
        `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/post-refactor/`.
- **Timing:** 1.5 hours
- **Depends on:** 23, 24
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/post-refactor/` - acceptance evidence
- **Verification:**
  - All gates green; wheel delta fully enumerated and intentional.
  - Every scaffolded project runs its examples successfully.

---

### Phase 26: Update ROADMAP.md [NOT STARTED]

- **Goal:** Record the durable decisions this refactor settles, so a future reader does not
  re-litigate them.
- **Tasks:**
  - [ ] Add a **Durable Decisions** entry: *Extract `theory_lib` into its own distribution —
        **REJECTED (for now)***. Record the rationale: directory position does not create modularity,
        dependency direction does; the graph is 88 imports one way and (now) zero the other;
        `where = ["src"]` would auto-discover a `src/theory_lib/` sibling into the same wheel, giving
        all the breakage and none of the separate-distribution benefit; renaming
        `model_checker.theory_lib.*` to `theory_lib.*` breaks every user notebook and script plus
        serialization-by-module-string; and `theory_lib` is too generic a name to claim in
        site-packages.
  - [ ] Record the **revisit trigger** explicitly: reconsider when externally-authored third-party
        theories become a real requirement, **or** when `theory_lib`'s core imports narrow to a
        stable published surface rather than reaching into `solver`/`models` internals. Note that the
        right mechanism at that point is entry-point registration into the consolidated registry, not
        a directory move — and that the boundary work completed here (one-way dependency, enforced
        layering test, single-source registry, typed conformance contract) is a prerequisite for any
        clean extraction, so nothing is foreclosed.
  - [ ] Add a **Durable Decisions** entry recording the enforced three-layer model (core /
        `theory_lib` / upper) and that it is enforced by an executable layering test rather than by
        directory placement.
  - [ ] Rewrite the Phase 1 priority "Merge and publish 1.3.0": it is superseded by the settled
        refactor-first sequencing. The refactor lands first, the release rehearsal is redone once
        afterward, and a single release follows. Keep the [USER-ONLY] marking — merge, tag, push, and
        PyPI upload remain user-only.
  - [ ] Add deferred items surfaced during the refactor: core-package internal reorganization; fold
        `iterate/z3_utils.py` into `iterate/constraints.py` once the `List[ExprRef]` vs
        `List[ModelRef]` signature mismatch is reconciled; add `notebooks/` for bimodal and logos;
        revisit `builder/comparison.py`'s status as `--maximize`-only code.
  - [ ] Add **Success Metrics**, replacing the current placeholder: conformance and layering tests
        green with zero xfails; zero core-to-`theory_lib` dependencies; one registry.
  - [ ] Diff the result against `roadmap-before.md` from Phase 1 to show a clean before/after.
  - [ ] Keep the record readable without tracker access. `specs/ROADMAP.md` is under `specs/` so task
        numbers are technically permitted, but write the rationale so it stands alone.
- **Timing:** 1 hour
- **Depends on:** 25
- **Files to modify:**
  - `specs/ROADMAP.md` - durable decisions, revised sequencing, deferred items, success metrics
- **Verification:**
  - The extraction decision, its rationale, and its revisit trigger are all present.
  - The superseded release item is rewritten, not merely checked off.
  - `diff roadmap-before.md specs/ROADMAP.md` shows only intended additions and the one rewrite.

---

## Testing & Validation

- [ ] `bash code/scripts/verify-refactor.sh` exits 0 at every wave boundary, not only at the end.
- [ ] Theory conformance test: green for all four theories and all five subtheories, zero xfails,
      guarded by a zero-xfail assertion.
- [ ] Layering test: zero violations — no static import, no `model_checker.theory_lib` string
      literal, and no theory-name string literal in any core module.
- [ ] In-package suite meets or exceeds the Phase 2 pinned inventory, with every delta enumerated.
- [ ] Bimodal in-package suite: 286/286 with `-n 6` (not `-n auto`).
- [ ] Oracle suite (550 tests): matches baseline, with all 5 `xfail(strict=True)` cross-oracle
      differentials still xfailing.
- [ ] `code/scripts/compare_bimodal_baseline.sh`: matches baseline.
- [ ] `builder/tests/unit/test_serialize.py`: passes after each semantic package split.
- [ ] `bimodal/tests/unit/test_semantic_module_registration.py`: passes after Phases 20 and 21.
- [ ] `--maximize` produces a non-zero Maximum N for a bimodal example (guards the pickling contract).
- [ ] A bimodal example with `iterate: 2` produces two distinct models instead of `ImportError`.
- [ ] `theory_lib.get_test_examples(t)` succeeds for all four theories.
- [ ] A full logos load resolves `\preceq` after the relevance fold; constitutive collects 54 tests.
- [ ] `builder/tests/integration/test_generated_projects.py`: passes after the registry and copy
      manifest changes.
- [ ] Scaffolded projects for all four theories contain only canonical-contract items and run their
      examples.
- [ ] Wheel contents diff: every delta enumerated and intentional.
- [ ] `grep -rnEi 'task [0-9]+' --include=*.md . | grep -v '^./specs/'` returns nothing.

## Artifacts & Outputs

- `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md` (this file)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/roadmap-before.md` (Phase 1 snapshot)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/` (Phase 2 pre-refactor evidence)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/post-refactor/` (Phase 25 acceptance evidence)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/summaries/01_core-theory-lib-refactor-summary.md`
- `code/scripts/verify-refactor.sh` (reusable regression gate)
- `code/src/model_checker/registry.py` (single-source theory registry)
- `code/src/model_checker/api.py` (upper-layer theory-aware surface)
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`
- `code/tests/test_layering.py`
- `code/scripts/logos_solver_benchmark.py` (relocated out of the package)
- Rewritten `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md`
- Updated `specs/ROADMAP.md`

## Rollback/Contingency

- All work proceeds on `task-117-restore-model-checker`; master is untouched throughout. Nothing is
  merged, tagged, pushed, or published by any phase.
- Commit per green sub-step per `.claude/rules/git-workflow.md`, using targeted staging — never
  `git add -A` or `git commit -am`. Each phase is therefore independently revertable with
  `git revert`.
- Phases 4, 5, and 6 are pure deletions and relocations; reverting restores the files exactly.
- Phase 20 is the highest-risk phase. It is deliberately a content-free move so a `--maximize` or
  pickling regression is unambiguously attributable to it and revertable without disturbing Phase 21.
  If Phase 20 cannot be made green, stop: do not begin Phase 21, and treat the dual module identity
  as a separately scoped problem.
- If the wheel parity diff in Phase 25 shows an unexplained entry, do not proceed to a release
  rehearsal. Bisect the phase commits against the Phase 2 manifest to locate the introducing phase.
- If an oracle strict-xfail flips to XPASS at any wave boundary, halt that wave and root-cause it
  before continuing — an XPASS here means a cross-oracle semantic behavior changed, which is a
  correctness signal, not a cleanup artifact.
- Baselines captured in Phase 2 remain in `specs/` regardless of code rollback, so the gate can
  always be re-run against a reverted tree.
