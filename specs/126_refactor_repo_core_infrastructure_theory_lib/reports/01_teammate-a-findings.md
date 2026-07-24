# Teammate A Findings: Primary Refactor Research (Task 126)

**Task**: 126 - Systematically refactor repo into core infrastructure + theory_lib; remove logos spatial subtheory
**Angle**: PRIMARY approach — deep structural enumeration, coupling analysis, target layout, migration strategy
**Date**: 2026-07-24
**Mode**: Hard (all claims verified against actual code with file:line references)

---

## Key Findings

### F1. The core/theory split already exists structurally — the refactor problem is boundary quality and internal uniformity, not location

`code/src/model_checker/` already separates core infrastructure from theories:

- **Core packages**: `builder/`, `iterate/`, `jupyter/`, `models/`, `output/`, `settings/`, `solver/`, `syntactic/`, `utils/`, plus root-level `z3_shim.py`, `__main__.py`
- **Theories**: `theory_lib/{bimodal, exclusion, imposition, logos}` plus shared `theory_lib/{__init__.py, errors.py, meta_data.py, types.py, docs/, tests/}`

The task prompt says "if it makes more sense, move theory_lib/ into src/" — **theory_lib is already under `code/src/model_checker/theory_lib/`**. The real decision is whether to promote it to a sibling top-level package (`src/theory_lib/`) outside `model_checker`. **Recommendation: do not.** Evidence against moving:

- The registry contract uses dotted names `model_checker.theory_lib.{name}` pervasively: `theory_lib/__init__.py:102,134,162,387`; `builder/runner.py:867`; `builder/loader.py:137`; `builder/serialize.py:26,198`; `builder/strategies.py:290` ("Theory library files must be under model_checker/theory_lib").
- `builder/project.py:54` computes the project-template source dir as `os.path.join(dirname(dirname(__file__)), 'theory_lib', theory)` — theory directories double as scaffolding templates for `model-checker` project generation.
- Single-wheel packaging (`pyproject.toml`: `package-dir = {"" = "src"}`, `packages.find where = ["src"]`) is simple and works; a second top-level package adds import-path and packaging risk for zero architectural gain.

The valuable move is instead to **formalize the boundary as a plugin contract** (see F2, R2) so core never needs theory names and theories never reach back into `builder`.

### F2. Coupling is leaky in BOTH directions

**Core → theory_lib** (verified, non-test code):

| Site | Nature |
|---|---|
| `builder/loader.py:64-142`, `builder/strategies.py:237-290` | Path-string sniffing (`'model_checker/theory_lib' in str(module_path)`, incl. a Windows `\\` variant) to decide import strategy — fragile |
| `builder/runner.py:795-867` | Reconstructs `model_checker.theory_lib.{module_name}` dotted paths from strings |
| `builder/project.py:54` | Uses theory dirs as file-copy templates |
| `builder/serialize.py:26,198` | Serializes operator module names with `theory_lib` substring checks |
| `jupyter/environment.py:166-177`, `jupyter/display.py:270,380`, `jupyter/builder_utils.py` | Imports `AVAILABLE_THEORIES` / `get_semantic_theories`, plus a manual directory-scan fallback |
| `utils/api.py:45-64`, `utils/version.py:37-57` | **Layering violation**: `utils` (the lowest layer, imported by everything) imports `theory_lib` (the highest layer). `utils/api.py` and `utils/version.py` belong above `theory_lib`, not below it |

**theory_lib → core (reverse coupling into builder)**:

- `theory_lib/logos/comparison.py:64` — `from model_checker.builder.example import BuildExample` in *non-test* theory code (1,110-line module). A theory importing the orchestration layer inverts the dependency direction. Integration tests also import builder (`logos/tests/integration/test_iterate.py`, `exclusion/tests/integration/test_iterate.py`, etc.), which is acceptable for tests but confirms `comparison.py` is doing runner-level work inside a theory package.
- Legitimate downward imports (fine, keep): theories import `z3_shim`, `syntactic`, `models.{structure, proposition, constraints}`, `solver.is_true/is_false`, `utils.{ForAll, Exists, context}` — this is the intended direction.

### F3. Four theories, four different `semantic` module conventions — including a dangerous shadowing hack

This is the single worst uniformity problem in the codebase:

| Theory | Layout | Line counts | Problem |
|---|---|---|---|
| **bimodal** | `semantic.py` (3,194 lines) **AND** `semantic/` package | `semantic/__init__.py` (26) + `witness_constraints.py` (182) + `witness_registry.py` (177) | The package **shadows** the module. `bimodal/semantic/__init__.py` re-loads the sibling `semantic.py` via `importlib.util.spec_from_file_location("bimodal_semantic_module", ...)` and `spec.loader.exec_module(...)` — the 3,194-line file **executes twice** under two module identities, so `BimodalSemantics` exists as two distinct class objects; `isinstance`/`issubclass` checks across the two paths silently fail |
| **exclusion** | `semantic/` package + dead `semantic.py` | `__init__.py` is **600 lines** and, per its own comment, holds "the remaining large classes directly" alongside `core.py` (566), `constraints.py` (174), `model.py` (78), `registry.py` (125) | `semantic.py` (32 lines) does `from .semantic import ...` — unreachable dead code, since the package always wins resolution |
| **imposition** | `semantic/` package + dead `semantic.py` (31 lines) | `core.py` (338), `model.py` (458), `helpers.py` (154), `__init__.py` (34) | Same dead wrapper; different internal file names than exclusion (`helpers.py` vs `constraints.py`/`registry.py`) |
| **logos** | flat `semantic.py` (1,283 lines) | — | No package at all |

### F4. Concrete per-theory module-set inconsistencies (verified matrix)

| Item | bimodal | exclusion | imposition | logos |
|---|---|---|---|---|
| `iterate.py` | **MISSING** (stale `__pycache__/iterate.cpython-312.pyc` proves it once existed) | yes (12,843 B) | yes (24,413 B) | yes (20,131 B) |
| `notebooks/` | **missing** | yes | yes | only in subtheories |
| `tests/e2e/` | yes (only theory with it) | no | no | no |
| `tests/conftest.py` | no | yes | no | yes |
| stray artifacts | — | `history/`, `TODO.md` | **`examples_refactored/`** (basic/complex/edge_cases/test_suite; zero references anywhere — orphaned abandoned refactor), `reports/imposition_comparison` | `TODO.md`, `comparison.py`, `protocols.py` |
| `get_theory` signature | `get_theory(config=None)` (`__init__.py:70`) | `get_theory(config=None)` (`:48`) | `get_theory(config=None)` (`:80`) | **`get_theory(subtheories=None)`** (`:31`) |
| `examples.py` contract | **BUG**: defines `unit_tests` (`:1357`) but NO `test_example_range` — `theory_lib.get_test_examples('bimodal')` (`theory_lib/__init__.py:135` reads `module.test_example_range`) raises | `test_example_range = unit_tests` (`:957`) | `test_example_range = unit_tests` (`:952`) | has it (`:140`), but assigns `example_range` **twice** (`:142` and `:191`) |
| examples size | 1,413 lines | 1,061 | 1,054 | 129 (aggregates subtheories) |

Additional wart: `theory_lib/docs/` contains case-duplicate files `usage_guide.md` (280 lines) **and** `USAGE_GUIDE.md` (325 lines).

### F5. Spatial subtheory removal is trivially small — it is documentation-only

Verified exhaustively:

- `theory_lib/logos/subtheories/spatial/` contains **exactly one file**: `README.md` ("Implementation Status: Planned"; `__init__.py`, `operators.py`, `examples.py`, tests all marked "(planned)").
- `spatial` is **not** in `AVAILABLE_SUBTHEORIES` (`logos/subtheories/__init__.py:19-25` lists only extensional, modal, constitutive, counterfactual, relevance).
- The only Python-side references are two docstring/comment mentions: `theory_lib/__init__.py:16` and `:63-64`.
- The only markdown reference outside the directory itself: none found (grep over `theory_lib/`, `docs/`, `code/docs/` matched only the spatial README itself; `logos/subtheories/README.md` should still be checked for a nav-link line during implementation).

**Removal = delete one directory + edit two comment lines** (plus any nav link in `subtheories/README.md`). Zero behavioral risk. If the theoretical content is worth keeping, relocate the README to `docs/` or the Logos theory docs; the task says remove, so default is deletion.

### F6. The relevance subtheory defines zero operators

`logos/subtheories/relevance/operators.py` contains **no classes** (`grep -c "^class"` = 0); it re-imports `RelevanceOperator` from `..constitutive.operators` and its `get_operators()` returns `{}` with a comment that it "exists for organizational purposes". This is a second candidate for structural cleanup (fold into constitutive, or actually move `RelevanceOperator` here) — the refactor should decide deliberately rather than carry the empty shell forward.

### F7. Z3 utility fragmentation across four locations

- `model_checker/z3_shim.py` (package root) — the import surface theories actually use (`from model_checker import z3_shim as z3`, 20+ occurrences in theory_lib)
- `solver/` — full backend abstraction (`z3_adapter.py`, `cvc5_adapter.py`, `expressions.py`, `registry.py`, `lifecycle.py`, `compat.py`)
- `utils/z3_helpers.py` — `ForAll`/`Exists` bitvector quantification (imports from `solver.expressions`)
- `builder/z3_utils.py` — `create_difference_constraint` and model-inspection utilities, which are **iteration-domain** logic living in `builder` (the `iterate/` package is its natural home)

### F8. Repo-level cruft inside `code/`

`code/` root contains: `boneyard/` (graveyard incl. an old `theory_lib/`), `dist/`, `output.md`, `test_update.py`, `run_update.py`, `jupyter_link.py`, `scaling_benchmark.py`, `run_jupyter.sh`. `pyproject.toml` ships `"*" = ["README.md", "*.md", "*.ipynb"]` as package-data, so every TODO.md, history/ doc, and notebook ships in the wheel. The triple nesting `ModelChecker/code/src/model_checker/` is unusual but orthogonal to this refactor — flattening `code/` into the repo root would churn CI/Nix/docs paths for cosmetic gain; recommend explicitly deferring it.

---

## Recommended Approach

### R1. Standardized per-theory module set (the target contract)

```
theory_lib/{theory}/
├── __init__.py          # uniform API: get_theory(config=None) [+ subtheories=None kw for logos],
│                        #   get_examples(), get_test_examples(), __version__, __model_checker_version__
├── semantic/            # ALWAYS a package; NEVER a sibling semantic.py
│   ├── __init__.py      # re-exports ONLY (<50 lines, no class bodies)
│   ├── core.py          # {Theory}Semantics
│   ├── model.py         # {Theory}ModelStructure
│   ├── proposition.py   # {Theory}Proposition
│   └── ...              # theory-specific: constraints.py, registry.py, helpers.py as needed
├── operators.py         # operator classes + get_operators()
├── iterate.py           # REQUIRED (restore for bimodal)
├── examples.py          # REQUIRED attrs: example_range, test_example_range, semantic_theories, unit_tests
├── tests/
│   ├── conftest.py      # required in all four
│   ├── unit/            # class-level tests
│   └── integration/     # example-run tests (builder imports allowed here only)
├── notebooks/           # required (add to bimodal)
├── docs/                # README, API_REFERENCE, ARCHITECTURE, ITERATE, SETTINGS, USER_GUIDE
├── README.md  CITATION.md  LICENSE.md  VERSION
```

Subtheory standard (logos): `__init__.py`, `operators.py`, `examples.py`, `README.md`, `tests/`, `notebooks/` — semantics stays centralized in `logos/semantic/` (current design is correct; subtheories are operator packages).

Enforce the contract with a **conformance test** in `theory_lib/tests/` that iterates `AVAILABLE_THEORIES` and asserts: required files exist, `examples` module exposes the four required attributes, `get_theory()` returns the `{'semantics','proposition','model','operators'}` dict shape. This turns F4's drift into a permanently failing test rather than a one-time cleanup.

### R2. Boundary hardening (core ⇄ theory_lib)

1. **Move `utils/api.py` and `utils/version.py`'s theory-aware halves** up: theory discovery/version aggregation belongs in `theory_lib/meta_data.py` (which already exists for exactly this purpose) or a thin `model_checker/api.py`. `utils/` must not import `theory_lib` (fixes the layering inversion, F2).
2. **Move `builder/z3_utils.py` → `iterate/`** (its consumers are difference-constraint iteration logic) and fold generic helpers into `utils/z3_helpers.py` (F7).
3. **Extract `logos/comparison.py`'s builder-dependent machinery** into `builder/comparison.py` (a `builder/comparison.py` already exists — verify overlap during planning) or make it accept injected build objects; a theory module must not import `builder` (F2).
4. Replace path-substring sniffing in `builder/loader.py:93` / `builder/strategies.py:290` with a registry query (`name in AVAILABLE_THEORIES` after resolving the module's package root) — behavior-preserving, removes the Windows-path special case.

### R3. Semantic package normalization (per theory)

- **exclusion**: move the ~550 lines of class bodies out of `semantic/__init__.py` into new focused modules (`proposition.py`, `structure.py` or similar); shrink `__init__.py` to re-exports. Delete dead `semantic.py`.
- **imposition**: delete dead `semantic.py`; optionally rename for cross-theory consistency (`helpers.py` stays; add `proposition.py` if the class lives in `core.py`).
- **bimodal**: the critical one. Split the 3,194-line `semantic.py` INTO the existing `semantic/` package (`core.py`, `model.py`, `proposition.py`, keeping `witness_constraints.py`/`witness_registry.py`), delete `semantic.py`, and delete the `spec_from_file_location` double-load hack in `semantic/__init__.py`. This removes the dual-class-identity hazard (F3).
- **logos**: split flat `semantic.py` (1,283 lines) into the same package shape.
- Project-wide: `grep` confirms no external consumer imports `theory_lib.{t}.semantic` as a *file* vs *package* distinctly (Python resolves identically), so this is import-compatible; the repo's "No Backwards Compatibility" principle (CLAUDE.md) means the dead wrappers should be deleted, not preserved.

### R4. Spot fixes to fold into the same refactor

- Fix bimodal `get_test_examples` bug: add `test_example_range = unit_tests` (or better, make the conformance test in R1 catch it) — `examples.py:1357` vs `theory_lib/__init__.py:135`.
- Remove duplicate `example_range` assignment in `logos/examples.py:142/191`.
- Delete `imposition/examples_refactored/` (orphaned, zero references) and `imposition/reports/`.
- Restore/write `bimodal/iterate.py` (git history has it — the stale `.pyc` shows it existed; check `git log -- '*bimodal/iterate.py'`).
- Delete one of `theory_lib/docs/usage_guide.md` / `USAGE_GUIDE.md` after merging content.
- Unify `get_theory` signatures: `get_theory(config=None)` everywhere; logos gains `get_theory(config=None, subtheories=None)` so `config` is positionally uniform.
- Resolve the relevance subtheory decision (F6): recommend moving `RelevanceOperator` from constitutive into relevance (matching `SUBTHEORY_DESCRIPTIONS`) or deleting the empty package and documenting relevance as part of constitutive.
- Clean `code/` root cruft (`boneyard/`, `output.md`, `test_update.py`, `run_update.py`, `dist/`) and tighten package-data so `TODO.md`/`history/` don't ship in the wheel (F8). `boneyard/` should be deleted outright (git history preserves it).
- Remove spatial: delete `logos/subtheories/spatial/`, edit `theory_lib/__init__.py:16,63-64`, check `subtheories/README.md` nav links (F5).

### R5. Migration strategy (phased, each phase independently green)

1. **Phase 0 — Conformance baseline**: write the theory-contract test (R1) marked `xfail` per known gap; run full suite (`PYTHONPATH=code/src pytest code/tests/ code/src/model_checker/`) and record baseline in `specs/baselines/`.
2. **Phase 1 — Deletions (zero-risk)**: spatial removal, dead `semantic.py` wrappers (exclusion, imposition), `examples_refactored/`, doc duplicates, `boneyard/`, root cruft. Smallest diffs, immediate wins.
3. **Phase 2 — Contract fixes**: bimodal `test_example_range`, logos duplicate assignment, `get_theory` signature unification, restore `bimodal/iterate.py`. Flip corresponding `xfail`s.
4. **Phase 3 — Semantic package normalization**: one theory per commit (imposition → exclusion → logos → bimodal, easiest to hardest; bimodal last because the 3,194-line split plus shadow-hack removal is the riskiest and benefits from the pattern being proven three times).
5. **Phase 4 — Boundary hardening**: `utils` layering fix, `z3_utils` relocation, `comparison.py` extraction, loader path-sniff replacement. Each is a small, testable move.
6. **Phase 5 — Docs/packaging**: per-theory docs parity (notebooks for bimodal), package-data tightening, README updates.

Ordering rationale: deletions before moves (shrinks the surface every later phase touches); per-theory normalization before boundary work (boundary code like `loader.py` gets simpler once theory layouts are uniform); TDD per CLAUDE.md — the conformance test is the RED that each phase turns GREEN.

---

## Evidence / Examples (index)

- Shadow hack: `code/src/model_checker/theory_lib/bimodal/semantic/__init__.py:9-24` (spec_from_file_location re-execution of sibling `semantic.py`)
- Dead wrappers: `exclusion/semantic.py:14` (`from .semantic import ...` — never reachable), `imposition/semantic.py:9`
- 600-line `__init__` with class bodies: `exclusion/semantic/__init__.py` (comment at ~line 15: "import the remaining large classes directly from the original semantic.py")
- Missing iterate: `ls theory_lib/*/iterate.py` → exclusion, imposition, logos only; `bimodal/__pycache__/iterate.cpython-312.pyc` exists
- get_test_examples bug: `theory_lib/__init__.py:135` (`module.test_example_range`) vs `bimodal/examples.py:1357` (only `unit_tests`)
- Spatial: `logos/subtheories/spatial/` = README.md only; registry `logos/subtheories/__init__.py:19-25` excludes it; mentions only at `theory_lib/__init__.py:16,63-64`
- Relevance empty shell: `logos/subtheories/relevance/operators.py:8` + `get_operators()` returning `{}`
- utils→theory_lib inversion: `utils/api.py:52,57`, `utils/version.py:37,57`
- theory→builder inversion: `logos/comparison.py:64`
- Path sniffing: `builder/loader.py:93`, `builder/strategies.py:290`
- Template coupling: `builder/project.py:54`
- Packaging: `code/pyproject.toml` (`package-dir {"" = "src"}`, package-data `"*" = ["*.md", "*.ipynb"]`)
- Size hotspots: `bimodal/semantic.py` 3,194; `bimodal/operators.py` 1,624; `logos/semantic.py` 1,283; `logos/comparison.py` 1,110; `builder/runner.py` 1,070

## Confidence Level

**High** for: spatial removal scope (F5), the semantic.py/semantic/ shadowing analysis (F3), the module-set matrix (F4), coupling inventory (F2), and the bimodal `get_test_examples` AttributeError path (F4) — all verified directly against source.

**Medium** for: the recommendation to keep `theory_lib` inside `model_checker` (judgment call; the evidence of dotted-name/template coupling is solid but a plugin-split advocate could counter with entry-points); the claim that no markdown outside the spatial dir references spatial (grep-based, one nav README should be re-checked); overlap between `logos/comparison.py` and the existing `builder/comparison.py` (not read side-by-side — planner should verify).

**Caveats**: I did not run the test suite (branch `task-117-restore-model-checker` has uncommitted changes to `models/structure.py`; current suite health unknown to me). Phase 0 baseline capture is therefore load-bearing in the migration strategy.
