# Research Report: Task #126

**Task**: Refactor repo into core infrastructure and theory_lib; remove logos spatial subtheory; standardize theory/subtheory module sets
**Date**: 2026-07-24
**Mode**: Team Research (4 teammates: Primary, Alternatives, Critic, Horizons)
**Session**: sess_1784909138_bee998
**Effort**: hard | **Model**: fable

## Summary

All four teammates independently converged on a decisive reframing: **two of the task's three headline premises are already satisfied**. `theory_lib/` is *already* inside src-layout at `code/src/model_checker/theory_lib/` with exactly the four requested theories (bimodal, exclusion, imposition, logos), and the spatial subtheory is a **README-only stub** (one 320-line `README.md`, absent from `AVAILABLE_SUBTHEORIES`, referenced by only two comment lines in `theory_lib/__init__.py:16,63-64`) whose removal is a one-commit hygiene item, not a refactor phase.

The task's real substance is its fourth clause — **standardizing the per-theory/subtheory module set and improving organization, code quality, and uniformity** — plus **hardening the core ⇄ theory boundary**. The recommended shape is: do NOT relocate `theory_lib` (dotted-name registries, serialization by `__module__` string, and template-copy coupling make it costly for zero gain, and it would break the PyPI public API at `model_checker.theory_lib.*`); instead enforce a single canonical theory layout with a conformance test, delete dead/transitional cruft, single-source the theory registry, and fix layering inversions.

Three decisions require user input before planning (see Gaps).

## Key Findings

### Primary Approach (from Teammate A)

- **The core/theory split already exists structurally**; the problem is boundary quality and uniformity, not location. Core packages (`builder/`, `iterate/`, `models/`, `solver/`, `syntactic/`, `utils/`, etc.) already sit beside `theory_lib/`.
- **Four theories, four different `semantic` module conventions** — the worst uniformity defect:
  - **bimodal**: 3,194-line `semantic.py` AND a `semantic/` package whose `__init__.py` re-executes the sibling `semantic.py` via `spec_from_file_location` — the file runs twice under two module identities, so `BimodalSemantics` exists as two distinct class objects (`isinstance` checks across paths silently fail). This is a live hazard.
  - **exclusion**: `semantic/` package with a 600-line `__init__.py` holding inline class bodies, plus a dead 32-line `semantic.py` wrapper (unreachable — package wins resolution).
  - **imposition**: `semantic/` package + dead `semantic.py` wrapper; internal file names differ from exclusion's.
  - **logos**: flat 1,283-line `semantic.py`, no package.
- **Concrete contract drift** (verified matrix): bimodal is missing `iterate.py` (stale `.pyc` proves it existed) and `notebooks/`; live bug — `theory_lib.get_test_examples('bimodal')` raises because `bimodal/examples.py` defines `unit_tests` but not `test_example_range` (contract at `theory_lib/__init__.py:135`); logos assigns `example_range` twice (`examples.py:142,191`); `get_theory` signatures diverge (logos: `get_theory(subtheories=None)` vs `config=None` elsewhere).
- **Coupling leaks both directions**: `utils/api.py:45-64` and `utils/version.py:37-57` import `theory_lib` (layering inversion — lowest layer importing highest); `logos/comparison.py:64` imports `builder` (theory reaching into orchestration); `builder/loader.py:93` and `builder/strategies.py:290` use path-substring sniffing (incl. a Windows `\\` variant); `builder/z3_utils.py` holds iteration-domain logic that belongs in `iterate/`.
- **Relevance subtheory defines zero operators** (`get_operators()` returns `{}`; `RelevanceOperator` actually lives in constitutive) — carry-forward or fold is a deliberate decision to make.
- Confidence: **high** on structural facts; medium on keep-theory_lib-in-package judgment.

### Alternative Approaches (from Teammate B)

- **The repo already has a written standard** — `theory_lib/docs/THEORY_ARCHITECTURE.md` (Simple vs Modular patterns). The highest-leverage framing is "reconcile the tree with the standard (updating it where reality is better) and enforce it," not inventing a novel layout.
- **In-repo precedent exists**: the theory-removal playbook in `specs/archive/028_archive_unused_theories/` (6-phase reference sweep) and the Keep/Drop/Fix + dependency-wave ADR format in `specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md` are directly reusable.
- **Registry triplication with live drift**: theory identity is encoded in (1) `AVAILABLE_THEORIES` (4 theories), (2) `discover_theories()` filesystem scan, and (3) `builder/loader.py:185-201` `prop_to_theory`/`theory_patterns` dicts — which **still contain only bimodal**, never restored after the exclusion/imposition restoration. Recommendation: one explicit Django-`INSTALLED_APPS`-style registry; loader derives from it; `discover_theories()` kept as dev lint only.
- **External prior art rejects the exotic options**: entry-point discovery (pytest/stevedore-style) is right only for third-party plugin distributions — defer, but the registry consolidation keeps that door open; namespace packages have silent-failure modes at n=4; per-theory PyPI packages lose (theories co-evolve with core; per-theory `VERSION`/`LICENSE`/`CITATION` already give scholarly identity).
- **Flattening logos subtheories to top-level theories: rejected** — subtheories are operator packages over shared logos semantics (no `semantic.py` of their own); the two-level nesting is semantically motivated.
- **Clean break for spatial** (no staged deprecation, no boneyard copy) per CLAUDE.md no-backwards-compat policy; the compat shims (`exclusion/semantic.py`, `imposition/semantic.py` — explicitly "backward compatibility" per their docstrings) violate that same policy and should be deleted.
- Confidence: **high** on registry/shim/spatial findings; medium-high on layout rejections.

### Gaps and Shortcomings (from Critic)

- **False premise must be surfaced, not silently absorbed**: "move theory_lib into src/" is either a no-op or a breaking namespace split (`model_checker.theory_lib.*` → `theory_lib.*`) for a v1.3.0 PyPI package with release engineering just completed. The user must disambiguate: namespace split vs in-place decoupling.
- **In-flight collision**: parent task 117 is still `planning`; the entire restoration (117-126) sits on unmerged branch `task-117-restore-model-checker`, 51 commits ahead of master; the working tree was dirty during research (uncommitted `models/structure.py` modifications). Sequencing vs merge/release is an unasked question.
- **Hidden coupling is name-keyed, not just import-based**: `builder/serialize.py:49,118-126` serializes classes by `__module__` string and rehydrates via `importlib` (constrains atomicity of any rename); `builder/loader.py:186-197` hardcodes class-name→theory maps; `jupyter/adapters.py:91-94` hardcodes a per-theory adapter registry; ~37 non-test core files reference theory names; `code/dev_cli.py:22` does `from src.model_checker.__main__ import main` (fragile, arguably already broken).
- **oracle/ is a live external consumer** (`oracle/bimodal_logic/provider.py:119-121` imports `model_checker.utils.context`, `model_checker.theory_lib.bimodal`) and is **invisible to the default test commands** — must be an explicit regression gate.
- **Fragile baseline**: task 122's green state is 286/286 bimodal in-package only with `-n 6`, plus 5 `xfail(strict=True)` cross-oracle differentials — refactor-induced XPASS flips fail the suite silently. Baselines live in `specs/118_*/` and `specs/122_*/` directories, NOT `specs/baselines/` (CLAUDE.md is stale on this).
- **Docs blast radius**: ~50 docs files reference current paths, freshly rewritten in task 124 — path changes trash that work; the plan must budget docs honestly or hold paths stable.
- **Cruft must be scoped explicitly** (in-scope with a per-item decision, or explicitly out-of-scope): `code/boneyard/`, `exclusion/history/`, `imposition/examples_refactored/` + `reports/`, root-level strays (`output.md`, `test_update.py`, `run_update.py`, `scaling_benchmark.py`, `dist/`). Test inventory to protect: 273 (code/tests) + 1,002 (theory_lib) collecting cleanly today.
- Confidence: **high** (all claims tree-verified).

### Strategic Horizons (from Teammate D)

- **ROADMAP.md is nearly empty**; its single durable decision (ship as `model_checker` package, 4 registered theories, built from `code/` with `where=["src"]`, `oracle/` outside the wheel) **constrains the refactor to reorganizing inside `code/src/model_checker/`** — no build-root moves, no package renames. Populating ROADMAP.md should be a refactor deliverable.
- **Timing is the biggest strategic call**: task 125 left a fully rehearsed, checklist-ready 1.3.0 wheel (hashes, twine-verified, parity diff vs published 1.2.12). Any refactor invalidates that evidence. **Strongest recommendation: user publishes 1.3.0 first; refactor targets 1.4.0**, using a wheel-parity-diff against published 1.3.0 as the refactor's acceptance gate.
- **Theory-layout uniformity is user-facing product, not internal hygiene**: `builder/project.py:172` copies theory dirs verbatim into user-scaffolded projects (only `__pycache__`/`.ipynb_checkpoints` ignored), so `exclusion/history/`, `imposition/examples_refactored/`, `imposition/reports/` leak into both user projects AND the 1.3.0 wheel (verified in task 125's `wheel-contents.txt`). Add an explicit copy manifest/ignore list so cruft can never leak again.
- **Case-colliding pair `theory_lib/docs/usage_guide.md` vs `USAGE_GUIDE.md` ships in the wheel** — a genuine install defect on case-insensitive filesystems (macOS default).
- **Extensibility seams already exist** — lazy `__getattr__` registry, `discover_theories()`, per-theory `VERSION` registry, `logos/protocols.py`, `builder/protocols.py`, and the `solver/` backend abstraction. Harden these (typed protocols + parametrized conformance test over `AVAILABLE_THEORIES`; express the contract against `solver/protocols.py` where feasible) rather than inventing new machinery. Defer entry-point plugin packaging as a ROADMAP item with an explicit trigger.
- Confidence: **high** on repo/wheel facts; medium on publish-first sequencing (user's call).

## Synthesis

### Conflicts Resolved

1. **"Dead wrapper" vs "back-compat shim" (A vs B, exclusion/imposition `semantic.py`)**: not a real conflict — the files are self-described backward-compatibility re-exports (B) that are also unreachable because Python resolves the `semantic/` package first (A). Both analyses mandate the same action: delete under the no-backwards-compat policy. → Resolved: delete.
2. **Which side of the `semantic.py`/`semantic/` duplication is live (D flagged for depth confirmation)**: A's depth analysis settles it — for exclusion/imposition the *package* is live and `semantic.py` is dead; for bimodal the package is live but re-executes `semantic.py`'s content under a second module identity (the shadowing hack). → Resolved: normalize on the `semantic/` package form everywhere (including splitting logos's flat `semantic.py`), delete all sibling `semantic.py` files, and eliminate bimodal's `spec_from_file_location` hack.
3. **A's 6-phase migration vs D's 3-wave release-aligned scoping**: complementary granularities. → Resolved: adopt D's wave structure as the release-facing frame with A's phases nested inside (Wave 1 = A's Phases 0-1; Wave 2 = A's Phases 2-3 + conformance test + protocols; Wave 3 = A's Phase 4-5 boundary/docs/packaging work; core reorganization beyond that is propose-don't-do, recorded in ROADMAP).
4. **CLAUDE.md's claimed standard ("all theories follow semantic.py, operators.py, examples.py") vs reality (C)**: reality contradicts it and the written standard in `THEORY_ARCHITECTURE.md` is the better anchor (B). → Resolved: the target contract is defined by updating `THEORY_ARCHITECTURE.md`; CLAUDE.md and stale docs follow.

### Gaps Identified (user decisions required before planning)

1. **Scope disambiguation**: confirm the refactor means *in-place decoupling + standardization* (unanimous team recommendation), NOT a namespace split moving `theory_lib` out of `model_checker`. A namespace split is a breaking public-API change contradicting the ROADMAP durable decision.
2. **Release sequencing**: publish rehearsed 1.3.0 first and target the refactor at 1.4.0 (D's recommendation), vs folding Wave-1 hygiene deletions into the pre-publish window, vs refactoring first and re-rehearsing. Also: sequence relative to task 117 closure and the `task-117-restore-model-checker` → master merge.
3. **Spatial README disposition**: delete outright (task says "remove"; git history preserves it) vs archive the 320-line theoretical content to `docs/` or `specs/`. Note the agent-system context layer (`.claude/context/project/logic/domain/spatial-domain.md`) references spatial and will dangle either way.
4. Smaller planner-verification items: overlap between `logos/comparison.py` and existing `builder/comparison.py` (not read side-by-side); relevance subtheory fold-vs-populate; whether bimodal's `iterate.py` should be restored from git history or rewritten; e2e tests for all theories or none.

### Recommendations

1. **Do not move `theory_lib`; do not rename packages; do not touch `oracle/` placement or the `code/` build root** (durable decision + verified blast radius: `flake.nix:82`, `release.yml`, ~50 docs files, serialization-by-module-path).
2. **Wave 1 — Hygiene (non-breaking deletions, one commit each)**: spatial stub + two comment lines; dead `semantic.py` shims (exclusion, imposition); `imposition/examples_refactored/` + `reports/`; `exclusion/history/` (archive content of value into `specs/`/`docs/` first); `code/boneyard/`; root strays (`output.md`, `test_update.py`, `run_update.py`, `scaling_benchmark.py`, `dist/`); resolve `usage_guide.md`/`USAGE_GUIDE.md` case collision. Gate: wheel-contents diff shows only removals; both test inventories (273 + 1,002) still collect and pass.
3. **Wave 2 — Standardized theory/subtheory contract (the core of the task)**:
   - Canonical theory set: `__init__.py` (uniform `get_theory(config=None)`, logos adds `subtheories=None` kw), `semantic/` package (re-export-only `__init__.py`, `core.py`, `model.py`, `proposition.py`, theory-specific extras), `operators.py`, `iterate.py` (restore for bimodal), `examples.py` (required attrs: `example_range`, `test_example_range`, `semantic_theories`, `unit_tests`), `tests/{conftest.py,unit,integration}`, `notebooks/`, `docs/` (six-file set), `README.md`, `CITATION.md`, `LICENSE.md`, `VERSION`. Subtheory set (logos): `__init__.py`, `operators.py`, `examples.py`, `tests/`, `notebooks/`, `README.md` — semantics stays centralized in `logos/semantic/`.
   - Enforce via a **parametrized conformance test** over `AVAILABLE_THEORIES` (files exist, examples contract attrs present, `get_theory()` dict shape) — written first as the RED baseline, xfail-marked per known gap, flipped green per phase (TDD per CLAUDE.md).
   - Semantic normalization order: imposition → exclusion → logos → bimodal (easiest to hardest; bimodal's 3,194-line split + shadow-hack removal last, after the pattern is proven).
   - Fix the contract bugs en route: bimodal `test_example_range`, logos duplicate `example_range`, signature unification.
   - Grow `logos/protocols.py` into shared `theory_lib/protocols.py` typed protocols; add a copy manifest/ignore list to `builder/project.py`.
4. **Wave 3 — Boundary hardening + registry single-sourcing**: move theory-aware halves of `utils/api.py`/`utils/version.py` up (into `theory_lib/meta_data.py` or a thin `model_checker/api.py`); relocate `builder/z3_utils.py` → `iterate/`; extract `logos/comparison.py`'s builder dependency; replace path-substring sniffing with registry queries; replace `builder/loader.py` and `jupyter/adapters.py` hardcoded maps with theory-owned registration derived from one registry. Update `THEORY_ARCHITECTURE.md`, tighten package-data (no `TODO.md`/`history/` in wheel), refresh affected docs, populate ROADMAP.md (wave structure, deferred core-reorg decision, plugin-ecosystem trigger).
5. **Verification gates throughout**: pin the task-122 baseline before any change (`--collect-only` inventories, `-n 6` bimodal invocation, strict-xfail set); run the oracle/ suite and `compare_bimodal_baseline.sh` explicitly at every wave boundary; final acceptance = wheel parity diff vs (ideally published) 1.3.0 showing only intended changes.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (structure, coupling, target layout, migration) | completed | high |
| B | Alternatives (prior art, registry patterns, in-repo precedent) | completed | high |
| C | Critic (false premises, in-flight collisions, hidden coupling, baselines) | completed | high |
| D | Horizons (roadmap, release sequencing, user-facing impact) | completed | high |

## References

- Teammate findings: `01_teammate-a-findings.md`, `01_teammate-b-findings.md`, `01_teammate-c-findings.md`, `01_teammate-d-findings.md` (this directory)
- `code/src/model_checker/theory_lib/__init__.py` (registry, contract, lazy loading)
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` (existing two-pattern standard)
- `code/src/model_checker/builder/{loader,serialize,strategies,project}.py` (coupling sites)
- `specs/ROADMAP.md` (durable package-identity decision)
- `specs/125_release_engineering_and_pypi_rehearsal/` (1.3.0 rehearsal evidence, wheel contents, publish checklist)
- `specs/archive/028_archive_unused_theories/`, `specs/archive/106_architecture_review_refactor/` (reusable playbooks)
- `oracle/bimodal_logic/provider.py` (external consumer)
- External prior art: Python Packaging Guide (plugin discovery, entry points), Django applications docs, stevedore essays (full list in teammate B's report)
