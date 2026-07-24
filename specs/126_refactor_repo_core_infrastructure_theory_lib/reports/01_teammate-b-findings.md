# Teammate B Findings: Alternative Approaches and Prior Art

**Task**: 126 - Refactor repo into core infrastructure + theory_lib, remove spatial subtheory
**Angle**: Alternative organizational schemes, external plugin-architecture prior art, and in-repo precedent
**Date**: 2026-07-24
**Mode**: hard (claims verified against actual files; paths cited throughout)

## Key Findings

### 1. The repo already has a written theory-structure standard — the refactor should enforce it, not invent one

`code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` documents two sanctioned
patterns:

- **Simple Pattern**: `semantic.py`, `operators.py`, `examples.py`, `__init__.py` (used by
  bimodal, imposition, exclusion in spirit)
- **Modular Pattern**: shared `semantic.py` + `operators.py` registry + `subtheories/{name}/`
  each with `operators.py`, `examples.py`, `tests/`, `notebooks/` (used by logos)

The actual tree has drifted from both patterns (see Finding 4). The highest-leverage,
lowest-risk framing of task 126 is "reconcile the tree with THEORY_ARCHITECTURE.md (updating
that doc where reality is better), and enforce it uniformly" — rather than designing a novel
layout. `code/docs/core/ARCHITECTURE.md` additionally documents the intended principles
(composition, Protocol interfaces, dependency injection) that any new shared abstractions
should follow.

### 2. Rich in-repo precedent exists for exactly this kind of surgery

- **Theory removal playbook** — `specs/archive/028_archive_unused_theories/summaries/implementation-summary-20260303.md`
  is a complete, phase-by-phase record of removing theories (exclusion/imposition at the time):
  move to `code/boneyard/`, prune `AVAILABLE_THEORIES`, delete notebook templates, purge
  `builder/loader.py` mappings, update fixtures/tests/docs. This is a directly reusable
  checklist for the spatial removal and for any consolidation deletions.
- **Keep/Drop/Fix inventory technique** — `specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md`
  (the bmlogic-oracle clean-break ADR) demonstrates the inventory format (Keep/Drop/Fix tables
  plus dependency-wave DAG) that made the strip-to-bimodal refactor tractable. It also
  catalogued the hard coupling points that still deserve attention: logos-specific branching in
  `builder/runner.py` and `builder/example.py`, and the unconditional logos import in
  `theory_lib/__init__.py`.
- **Strip-and-restore cycle** — tasks 100-115 stripped the repo to a bimodal-only oracle;
  tasks 118-121 (current branch `task-117-restore-model-checker`) restored the four-theory
  framework. Consequence: several "restored" components still carry stale, bimodal-era wiring
  (see Finding 5's loader evidence). Task 126 is effectively the reconciliation pass after that
  cycle.
- **Durable decision already made** — `specs/ROADMAP.md` (Durable Decisions): the framework
  ships as the `model_checker` package with four registered theories built from `code/` with
  `where = ["src"]`, and `oracle/` stays a standalone top-level tree excluded from the wheel.
  Any alternative that repackages theories separately or relocates `oracle/` contradicts a
  recorded decision and would need explicit user sign-off.

### 3. The spatial subtheory is documentation-only; removal is trivial and clean-break is safe

Verified contents of `code/src/model_checker/theory_lib/logos/subtheories/spatial/`: a single
`README.md` whose own header says "**Implementation Status**: Planned" — no `__init__.py`, no
`operators.py`, no `examples.py`, no tests. It is **not** listed in `AVAILABLE_SUBTHEORIES`
(`logos/subtheories/__init__.py:19-25` lists only extensional, modal, constitutive,
counterfactual, relevance). Grep confirms the only other mentions are docstring text in
`theory_lib/__init__.py` (lines 15-16, 63-64) and the README itself. There is nothing to
deprecate in stages: delete the directory, fix the two docstrings, done. Git history (plus
`specs/archive/005_logos_spatial_readme`, the task that authored the README) preserves the
theoretical content; no boneyard copy is needed since there is no code.

### 4. Theory-discovery today is a triple-redundant, partially stale registry — external prior art says: keep it explicit, but single-source it

Current mechanisms (all verified):

1. `AVAILABLE_THEORIES` hardcoded list — `theory_lib/__init__.py:61-67`, with lazy loading via
   module `__getattr__` (lines 364-393). Consumers: `meta_data.py`, `jupyter/environment.py`,
   `utils/version.py`, `utils/api.py`.
2. `discover_theories()` filesystem scan (dirs containing `examples.py` + `operators.py`),
   `theory_lib/__init__.py:167-194` — dev-only, advisory.
3. **Stale duplicates** in `builder/loader.py:185-201`: `prop_to_theory` and `theory_patterns`
   dicts contain only `bimodal` — exclusion/imposition entries were removed by the theory
   archival work (see the removal summary cited in Finding 2) and never restored when the
   theories were (restoration effort). This is live drift caused by registry duplication.

External prior art (see Appendix for sources):

| System | Mechanism | Fit for ModelChecker |
|---|---|---|
| Django `INSTALLED_APPS` + `AppConfig` | Explicit list, per-app config object | **Best analog.** Theories are first-party, co-developed, few in number; explicitness is a feature |
| sympy | Plain monorepo subpackages, explicit imports, no plugin machinery | Matches theory_lib's reality; validates "no plugin framework needed" |
| pytest/pluggy | `pytest11` entry points, hook specs | Right only when third parties ship plugins as separate distributions — not the case here |
| Sphinx extensions | `extensions` config list + `setup(app)` convention | Hybrid; its lesson is a uniform per-extension entry contract (cf. `get_theory()`) |
| stevedore (OpenStack) | Entry-point manager library | Overkill; adds packaging indirection with zero current benefit |
| Namespace packages (PEP 420) | Auto-discovery by namespace | Fragile (silent partial installs), wrong tradeoff for 4 first-party theories |

The literature's split is "explicitly specified vs auto-discovered"; for statically-imported,
first-party code, explicit registration is the recommended side (Django's position). The defect
here is not the explicit list — it is that there are *three* places encoding theory identity,
and two of them disagree. Recommendation: one registry (a small `TheoryMetadata`/registry
module in theory_lib), with `builder/loader.py`'s dicts derived from it or deleted, and
`discover_theories()` retained only as a dev lint ("unregistered theory present?").
Entry-point-based discovery (`[project.entry-points."model_checker.theories"]`) is a reasonable
*future* extension if third-party theory packages ever become a goal, and the single-registry
consolidation is precisely what makes adding it later cheap; do not adopt it now.

### 5. Uniformity defects inventory (what "standardized module set" must fix)

All verified against the tree:

- **Back-compat shims violating project policy**: `exclusion/semantic.py` is explicitly a
  "backward compatibility" re-export over `exclusion/semantic/` (its docstring says so);
  imposition has the same `semantic.py` + `semantic/` pair. CLAUDE.md mandates "No Backwards
  Compatibility / no compatibility layers" — these shims should be deleted and imports updated.
- **Mixed monolith/package**: `bimodal/semantic.py` is a large monolith while
  `bimodal/semantic/` simultaneously holds `witness_constraints.py` / `witness_registry.py` —
  neither Simple nor Modular pattern.
- **Dead parallel tree**: `imposition/examples_refactored/` has zero importers outside itself
  (grep-verified) — an abandoned migration to finish or delete.
- **Asymmetric extras**: `exclusion/` carries `history/` and `TODO.md`; `imposition/` carries
  `reports/`; `logos/` carries `TODO.md`, `comparison.py`, `protocols.py`; bimodal none of
  these. Standardize which of docs/notebooks/history/reports are part of the theory contract
  (per-theory `docs/` with the fixed six-file set — API_REFERENCE, ARCHITECTURE, ITERATE,
  README, SETTINGS, USER_GUIDE — is already uniform across all four and worth keeping).
- **Doc duplication**: `theory_lib/docs/` contains both `usage_guide.md` and `USAGE_GUIDE.md`.
- **`code/` root clutter**: `boneyard/`, `dist/`, `output.md`, `test_update.py`,
  `run_update.py`, `scaling_benchmark.py` sit beside `pyproject.toml` — candidates for
  deletion/relocation under `scripts/` or `specs/`.
- **Tests**: bimodal/exclusion/logos/imposition all have `tests/{unit,integration}` (good,
  uniform); logos subtheories each have their own `tests/` + `notebooks/` (uniform); bimodal
  has an empty `tests/e2e/`.

### 6. Alternative organizational schemes considered (and why most lose)

- **(A) Improved status quo — monorepo, `theory_lib` stays at `src/model_checker/theory_lib/`, single explicit registry** — *recommended*.
  Note the task description's "move theory_lib/ into src/" is already satisfied: theory_lib
  lives inside the package. The open layout questions are naming (e.g. rename to `theories/`
  for plainness — cosmetic, high churn in imports/docs, low value) and whether `code/` should
  remain the package root (ROADMAP durable decision says yes: built from `code/` with
  `where = ["src"]`; `specs/archive/027_flatten_code_src_directory` and
  `101_restructure_pip_package` show this ground was already litigated).
- **(B) Separate distribution per theory** (`model-checker-logos`, ...) — rejected. Theories
  and core co-evolve (every core semantic-defaults change touches all four); "packages that
  change together should live together." Per-theory `VERSION`/`LICENSE.md`/`CITATION.md` files
  already provide the scholarly identity that separate packaging would otherwise buy, without
  release-engineering overhead (fresh pain: the current branch's task 121/125 work is precisely
  about repairing single-package identity).
- **(C) Entry-point discovery now** — deferred, not rejected (see Finding 4).
- **(D) Namespace-package theory tree** — rejected; silent-failure modes, no benefit at n=4.
- **(E) Flatten logos subtheories to top-level theories** — rejected. Subtheories are *operator
  packages over a shared logos semantics* (`logos/semantic.py` + per-subtheory `operators.py`,
  loaded via `LogosOperatorRegistry.load_subtheories`, `logos/__init__.py:53-59`); they are not
  self-contained theories (no `semantic.py` of their own) and cannot stand as siblings of
  bimodal/exclusion. The two-level structure is semantically motivated; keep it, and keep the
  THEORY_ARCHITECTURE.md two-pattern doc that legitimizes it.

### 7. Spatial removal pattern: clean break, not staged deprecation

Project policy (CLAUDE.md "No Backwards Compatibility", "clean breaks... single commits") plus
the theory archival precedent both point one way, and the doc-only status (Finding 3) removes
any argument for staging. Choose outright deletion over the theory boneyard precedent: boneyard
was for *working code* with restoration instructions; a planned-only README needs neither. One
commit: delete directory, edit two docstrings in `theory_lib/__init__.py`, update
`logos/subtheories/README.md` if it lists spatial. (Optional: note in the logos README that the
spatial extension is a documented future direction, citing the Logos literature rather than the
deleted file.)

## Recommended Approach

1. **Frame the refactor as standards-enforcement**: update
   `theory_lib/docs/THEORY_ARCHITECTURE.md` to the target contract first (choose: `semantic/`
   package is canonical for large theories, `semantic.py` single-file allowed for small ones —
   never both), then bring each theory into compliance. Reuse the Keep/Drop/Fix +
   dependency-wave format from the clean-break ADR
   (`specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md`).
2. **Single-source the theory registry** (Django-style explicit registration): one metadata
   registry in `theory_lib`; derive or delete `builder/loader.py`'s stale dicts; keep
   `discover_theories()` as a consistency lint only. No entry points now; consolidation keeps
   that door open.
3. **Delete the compat shims and dead trees** (`exclusion/semantic.py` shim, imposition shim,
   `examples_refactored/`, `usage_guide.md` duplicate, `code/` root strays, decide
   boneyard's fate) under the no-backwards-compat policy.
4. **Remove spatial as a one-commit clean break** per Finding 7, using the task-28-style
   reference-sweep checklist (registry, docstrings, README cross-links, notebooks, fixtures).
5. **Do not** split theories into separate distributions, adopt namespace packages, or move
   `theory_lib` out of the package; do not touch `oracle/` placement (durable decision).

## Evidence/Examples

| Claim | Evidence |
|---|---|
| Spatial is doc-only, unregistered | `logos/subtheories/spatial/` contains only README.md ("Implementation Status: Planned"); absent from `logos/subtheories/__init__.py:19-25` |
| Registry triplication + drift | `theory_lib/__init__.py:61-67` (4 theories) vs `builder/loader.py:185-201` (bimodal only) |
| Compat shim vs policy | `exclusion/semantic.py` docstring: "maintains backward compatibility by re-exporting..."; CLAUDE.md "No Backwards Compatibility" |
| Existing two-pattern standard | `theory_lib/docs/THEORY_ARCHITECTURE.md` (Simple vs Modular pattern sections) |
| Removal playbook | `specs/archive/028_archive_unused_theories/summaries/implementation-summary-20260303.md` (6-phase reference sweep) |
| Clean-break ADR technique + coupling points | `specs/archive/106_architecture_review_refactor/reports/04_architectural-decisions.md` (Keep/Drop/Fix; `builder/runner.py:82,206` logos branching) |
| Package-identity durable decision | `specs/ROADMAP.md` Durable Decisions |
| Dead tree | `imposition/examples_refactored/` — no importers found outside the directory |
| Doc duplication | `theory_lib/docs/usage_guide.md` and `theory_lib/docs/USAGE_GUIDE.md` both exist |
| Subtheories are operator packages | `logos/__init__.py:53-59` (`LogosOperatorRegistry().load_subtheories(...)`); subtheory dirs have `operators.py`/`examples.py` but no `semantic.py` |

### External prior-art sources

- [Creating and discovering plugins — Python Packaging User Guide](https://packaging.python.org/en/latest/guides/creating-and-discovering-plugins/) (naming convention vs namespace packages vs entry-point metadata)
- [Entry points specification — Python Packaging User Guide](https://packaging.python.org/specifications/entry-points/)
- [Entry Points — setuptools documentation](https://setuptools.pypa.io/en/latest/userguide/entry_point.html)
- [Plugin Systems — Sedimental (Mahmoud Hashemi)](https://sedimental.org/plugin_systems.html) (explicit-vs-discovered tradeoff; Django cited as right to require explicit listing)
- [Applications — Django documentation](https://docs.djangoproject.com/en/6.0/ref/applications/) (`INSTALLED_APPS`/`AppConfig` explicit-registry model)
- [Dynamic Code Patterns: Extending Your Applications with Plugins — stevedore](https://docs.openstack.org/stevedore/1.19.1/essays/pycon2013.html)
- [How to Build Plugin Systems in Python — OneUptime blog](https://oneuptime.com/blog/post/2026-01-30-python-plugin-systems/view)
- [Monorepo vs Multirepo tradeoffs — dev.to](https://dev.to/dayal/monorepo-vs-multirepo-managing-codebases-in-modular-architectures-f3b) ("packages that change together should live together")

## Confidence Level

- Spatial-removal findings: **high** (directory listing + registry + grep all verified)
- Registry drift and shim findings: **high** (read the code)
- In-repo precedent characterization: **high** for task-28 summary and 106 ADR (read);
  **medium** for the exact scope of tasks 100-115/118-121 (inferred from titles, archive
  listings, and branch name; individual summaries not all read)
- External prior-art recommendation (explicit registry, no entry points now): **high** —
  converging guidance from packaging docs and the n=4 first-party-theory reality
- Layout-alternative rejections (B, D, E): **medium-high** — grounded in ROADMAP durable
  decision and code structure, but final call belongs with the synthesized plan
