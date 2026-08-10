# Teammate D Findings: Horizons / Strategic Alignment — Task 126 Refactor

**Task**: 126 - refactor_repo_core_infrastructure_theory_lib
**Role**: Teammate D (HORIZONS — long-term alignment and strategic direction)
**Date**: 2026-07-24
**Sources**: `specs/ROADMAP.md`, `specs/state.json`, task 118-125 summaries, task 125 rehearsal
evidence (`specs/125_release_engineering_and_pypi_rehearsal/rehearsal/`), `README.md`,
`docs/architecture/README.md`, `code/pyproject.toml`, `flake.nix`, and direct inspection of
`code/src/model_checker/` (theory_lib, builder, solver, theory registry).

---

## Key Findings

### F1. The roadmap is nearly empty — this refactor will *become* the de facto roadmap

`specs/ROADMAP.md` contains exactly one durable decision and no Phase 1 items ("(No items yet)").
The single durable decision directly constrains task 126:

> **Package identity**: the framework ships as the `model_checker` package (four registered
> theories: `logos`, `exclusion`, `imposition`, `bimodal`) built from `code/` with
> `[tool.setuptools.packages.find] where = ["src"]`. The cross-solver differential oracle is
> kept as a standalone, unpacked top-level `oracle/` tree — outside `code/src/` and excluded
> from the wheel.

Strategic implication: any refactor design that moves the build root away from `code/`, renames
the `model_checker` package, or changes the four-theory registration model contradicts the only
durable decision on record. The refactor should work *within* that decision (reorganize inside
`code/src/model_checker/`) and, as a deliverable, should populate ROADMAP.md Phase 1 with the
refactor's own wave structure so the project finally has forward-looking priorities.

### F2. The refactor sits directly between a fully rehearsed 1.3.0 and its user-gated publish

Tasks 118-125 form a coherent restoration-and-release arc (all `completed` in `state.json`):
baseline capture + oracle relocation (118), core restoration (119), exclusion/imposition port
(120), package identity + test infra repair (121), cross-oracle differential (122), Nix flake
rewrite (123), documentation refresh (124), and release engineering + PyPI rehearsal (125).

Task 125 produced byte-exact rehearsal evidence: a built and `twine check --strict`-verified
`model_checker-1.3.0` wheel (SHA256 `f85e6512...`), a classified parity diff against the last
published `model-checker==1.2.12`, and a user-gated `PUBLISH-CHECKLIST.md`
(`specs/125_release_engineering_and_pypi_rehearsal/`). Parent task 117 ("prepare a top-quality
release to push to PyPI") is still in `planning`.

**Any refactor invalidates all of that rehearsal evidence** — wheel hashes, wheel-content
listings, and the parity diff are artifacts of the current tree. The strategic sequencing
question ("publish 1.3.0 first, or fold the refactor in?") is the single most consequential
scoping decision for this task. See Recommended Approach R1.

### F3. Two of the task's three stated premises are already (nearly) satisfied

Verified against the actual tree:

1. **"Move theory_lib/ into src/"** — `theory_lib` is *already* inside src-layout:
   `code/src/model_checker/theory_lib/`. There is nothing to move. What the description
   plausibly gestures at is either (a) flattening `code/` into the repo root, or (b) a more
   visible core-vs-theories separation. Option (a) is high-churn against freshly-completed
   work: `flake.nix:82` hardcodes `MC_SRC="$PWD/code/src"`, `.github/workflows/release.yml`
   had its `cd code` casing fixed in task 125, and CLAUDE.md/docs reference `code/` throughout.
2. **"theory_lib consisting of bimodal, exclusion, imposition, logos"** — already exactly true;
   `AVAILABLE_THEORIES` in `code/src/model_checker/theory_lib/__init__.py:61` registers exactly
   those four.
3. **"Remove the spatial subtheory"** — spatial is a **README-only stub**: the entire subtheory
   is one file, `code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md`
   ("Implementation Status: Planned"), plus two *comment* lines in `theory_lib/__init__.py`
   (lines 16, 64). Removal is a one-commit hygiene item, not a refactor phase.

Implication: the task's real substance is not the three headline items — it is the fourth
clause ("standardized set of modules for each theory/subtheory, improving organization, code
quality, and uniformity"). Planning should weight accordingly.

### F4. The genuinely strategic payload: theory-layout uniformity is a *user-facing product*, not internal hygiene

Three verified facts make theory-directory standardization strategically load-bearing:

1. **`builder/project.py` copies entire theory directories into user projects.** The
   `model-checker -l <theory>` scaffolding flow copies everything except `__pycache__` and
   `.ipynb_checkpoints` (`code/src/model_checker/builder/project.py:172`). Today,
   `model-checker -l exclusion` hands an academic user a project containing
   `history/IMPLEMENTATION_STORY.md`, `LESSONS_LEARNED.md`, and `STRATEGIES.md`;
   `-l imposition` includes `examples_refactored/` and `reports/imposition_comparison/`. The
   theory directory *is* the template product for the project's primary academic audience.
2. **The 1.3.0 wheel ships the same cruft** (verified in
   `specs/125_release_engineering_and_pypi_rehearsal/rehearsal/wheel-contents.txt`, 490 files):
   `exclusion/history/*.md`, `imposition/examples_refactored/*.py`,
   `imposition/reports/imposition_comparison/*.md`, the spatial stub README, and a
   **case-colliding duplicate pair** `theory_lib/docs/usage_guide.md` *and*
   `theory_lib/docs/USAGE_GUIDE.md` — a genuine defect on case-insensitive filesystems
   (macOS default), where one silently overwrites the other on install.
3. **Theory layouts have drifted into transitional duplication.** All three non-logos theories
   currently carry *both* a `semantic.py` module *and* a `semantic/` package
   (bimodal, exclusion, imposition — verified by direct listing); logos alone has
   `comparison.py` and `protocols.py`; bimodal alone lacks `iterate.py`; logos subtheories are
   internally nonuniform (counterfactual has `CITATION.md` + `report/`, modal has neither).
   `theory_lib/docs/THEORY_ARCHITECTURE.md` exists as the natural home for a canonical
   contract but the tree does not currently conform to any single layout.

### F5. Extensibility seams already exist — the refactor should harden them, not invent new ones

- `theory_lib/__init__.py` already has a lazy `__getattr__` registry, `discover_theories()`
  (filesystem discovery vs. `AVAILABLE_THEORIES` divergence reporting), per-theory `VERSION`
  files with `get_theory_version_registry()`, and per-theory `LICENSE.md`/`CITATION.md`
  machinery — i.e., a proto theory-plugin API.
- `logos/protocols.py` and `builder/protocols.py` (380 lines) are seed material for a typed
  theory-author protocol.
- `solver/` already abstracts the backend (`z3_adapter.py`, `cvc5_adapter.py`, `registry.py`,
  `protocols.py`) — the cross-solver oracle work (tasks 118/122) pushed the codebase toward
  backend-pluggability. A standardized theory contract should be expressed against the solver
  protocol, not raw Z3, to preserve that trajectory.

### F6. Adjacent recently-completed work constrains — and can be advanced by — the refactor

- **Docs (task 124, completed)**: `docs/architecture/` has one file per core package
  (BUILDER.md, MODELS.md, ITERATE.md, ... THEORY_LIB.md) mirroring current module names.
  Keeping top-level package names stable preserves the just-refreshed docs; renaming packages
  forfeits task 124's work. The refactor can instead fix the drift docs cannot: the
  `usage_guide.md`/`USAGE_GUIDE.md` collision, and stub/reality mismatches like spatial.
- **Test infra (task 121, completed)**: test collection was just repaired with widened
  `testpaths`; per-theory `tests/unit/` plus central `code/tests/{unit,integration,e2e}` is the
  current dual structure. The refactor should treat green collection as an invariant gate per
  wave (baselines exist under `specs/baselines/` per CLAUDE.md conventions).
- **Nix flake (task 123, completed)**: `flake.nix` depends only on `$PWD/code/src` — stable
  under any *internal* reorganization, broken by moving `code/`. Another reason to refactor
  inside `code/src/model_checker/` rather than relocating the build root.
- **Repo-root cruft** (outside the wheel but confusing to contributors): `code/boneyard/`
  (contains an old `theory_lib` copy with exclusion/imposition), `code/output.md`,
  `code/scaling_benchmark.py`, `code/test_update.py`, `code/run_update.py`,
  `imposition/notebooks` alongside per-subtheory `notebooks/` — a Wave-1 sweep candidate.

---

## Recommended Approach

### R1. Sequence around the release: publish 1.3.0 first, refactor as 1.4.0 (strongest recommendation)

Publish the rehearsed 1.3.0 (user-gated, via task 125's `PUBLISH-CHECKLIST.md`) **before**
landing the refactor, then target the refactor at 1.4.0:

- The 125 rehearsal evidence is only valid for the current tree; refactoring first forces a
  full re-rehearsal and delays a release that is already checklist-ready.
- A published 1.3.0 gives the refactor a *known-good published baseline* to parity-diff
  against — exactly the methodology task 125 established (wheel-contents diff vs. 1.2.12).
  The refactor's acceptance gate becomes: "wheel diff vs. 1.3.0 shows only intended
  removals/moves; example-suite oracle baselines unchanged."
- The project's "No Backwards Compatibility / clean breaks" principle (CLAUDE.md) means the
  refactor may change public import paths; that belongs in a version bump users can pin
  around, not silently inside the restoration release.

If the user prefers folding hygiene into 1.3.0, split R2's Wave 1 (pure deletions, no import
changes) into the pre-publish window and defer everything else — but do not fold Wave 2+.

### R2. Rescope into three waves aligned with release milestones

**Wave 1 — Hygiene (non-breaking, could ship as 1.3.x):**
- Delete: spatial stub (1 README + 2 comment lines), `exclusion/history/`,
  `imposition/examples_refactored/`, `imposition/reports/`, `code/boneyard/`, stray `code/`
  root files (`output.md`, `scaling_benchmark.py`, `test_update.py`, `run_update.py`), and
  resolve the `usage_guide.md`/`USAGE_GUIDE.md` case collision. Move anything with historical
  value into `specs/` or `docs/` (out of the wheel), never delete silently.
- Gate: wheel-contents diff shows only removals; all tests collect and pass.

**Wave 2 — Standardized theory/subtheory contract (the core of the task; 1.4.0):**
- Define ONE canonical layout in `theory_lib/docs/THEORY_ARCHITECTURE.md` and make all four
  theories conform. Concretely resolve the `semantic.py` + `semantic/` duplication in bimodal,
  exclusion, and imposition to a single form (recommend: `semantic/` package with `__init__.py`
  re-exports, since all three already have the package started).
- Canonical theory module set: `__init__.py`, `semantic/`, `operators.py`, `examples.py`,
  `iterate.py` (optional with a documented core default), `tests/`, `docs/`, `notebooks/`,
  `README.md`, `CITATION.md`, `LICENSE.md`, `VERSION`. Canonical subtheory set (logos):
  `__init__.py`, `operators.py`, `examples.py`, `tests/`, `notebooks/`, `README.md`.
- Because `builder/project.py` copies theory dirs verbatim, this wave *is* the UX improvement
  for `model-checker -l <theory>` — consider adding an explicit copy manifest or ignore list to
  `project.py` so future cruft can never leak into user projects again.
- Express the contract as typed protocols (grow `logos/protocols.py` into a shared
  `theory_lib/protocols.py`), checked by a parametrized conformance test over
  `AVAILABLE_THEORIES` — turning uniformity from a one-time cleanup into a regression-proof
  invariant.

**Wave 3 — Core reorganization (only if still needed; 2.0.0 territory, propose-don't-do):**
- Defer any build-root move (`code/` → repo root) and any public-package renames. Record the
  decision and triggers in ROADMAP.md instead. Verified blast radius: `flake.nix`,
  `release.yml`, CLAUDE.md, all docs cross-links, and the durable package-identity decision.

### R3. Creative/long-horizon options — adopt the cheap halves now

- **Theory plugin ecosystem (entry points)**: a `model_checker.theories` entry-point group
  would let third parties ship theories as separate packages. Do NOT split the four in-tree
  theories out now (academic users benefit from batteries-included `pip install model-checker`,
  and the durable decision registers all four in one package) — but Wave 2's protocol +
  conformance test is precisely the prerequisite such an ecosystem needs. Adopt the contract
  now; defer the packaging split as a ROADMAP item with an explicit trigger ("first external
  theory author appears").
- **Versioned theory API**: per-theory `VERSION` files and `get_theory_version_registry()`
  already exist; Wave 2 should declare which registry/protocol surfaces are the *stable
  theory-author API* and document them in `theory_lib/docs/CONTRIBUTING.md`, so future core
  refactors know what they must not break.
- **Solver-agnostic theory contract**: define the Wave-2 protocol against `solver/protocols.py`
  rather than raw Z3 types where feasible, preserving the cvc5/differential-oracle trajectory
  from tasks 118/122 without expanding this task's scope.

### R4. Deliver ROADMAP.md population as an explicit refactor deliverable

Phase 1 of ROADMAP.md is empty. The refactor plan should end by writing its wave structure,
the deferred Wave-3 decision, and the plugin-ecosystem trigger into ROADMAP.md — converting
this task's strategic analysis into durable project direction.

---

## Evidence / Examples

| Claim | Evidence (verified paths) |
|---|---|
| Roadmap empty except package-identity decision | `specs/ROADMAP.md` (lines 3-13) |
| 1.3.0 rehearsed, publish user-gated | `specs/125_.../rehearsal/parity-diff.md`, `specs/125_.../PUBLISH-CHECKLIST.md`; task 117 status `planning` in `specs/state.json` |
| theory_lib already in src-layout | `code/src/model_checker/theory_lib/` exists; `code/pyproject.toml` `where = ["src"]` |
| Spatial is a README-only stub | `find .../logos/subtheories/spatial -type f` → only `README.md`; comment-only refs at `theory_lib/__init__.py:16,64` |
| Dev cruft ships in wheel | `specs/125_.../rehearsal/wheel-contents.txt`: `exclusion/history/*.md`, `imposition/examples_refactored/*.py`, `imposition/reports/...`, `spatial/README.md` |
| Case-colliding doc pair in wheel | `wheel-contents.txt` lists both `theory_lib/docs/usage_guide.md` and `theory_lib/docs/USAGE_GUIDE.md`; both exist on disk |
| semantic.py + semantic/ duplication | Direct listing: bimodal, exclusion, imposition each have both `semantic.py` and `semantic/` |
| Theory dirs copied verbatim to user projects | `code/src/model_checker/builder/project.py:172` (`ignore_dirs = ['__pycache__', '.ipynb_checkpoints']`) |
| Flake depends only on `code/src` path | `flake.nix:82` (`MC_SRC="$PWD/code/src"`) |
| Proto plugin API exists | `theory_lib/__init__.py`: `AVAILABLE_THEORIES` (line 61), `discover_theories()` (line 167), `get_theory_version_registry()` (line 197), `__getattr__` lazy loading (line 364) |
| Solver abstraction seam | `code/src/model_checker/solver/` (`z3_adapter.py`, `cvc5_adapter.py`, `registry.py`, `protocols.py`) |
| Repo-root cruft | `code/boneyard/` (contains stale `theory_lib/` copy), `code/output.md`, `code/scaling_benchmark.py`, `code/test_update.py` |

## Confidence Level

**High** for: repo-structure facts, wheel-content facts, the spatial-stub finding, the
`project.py` verbatim-copy behavior, and the release-arc timeline (all verified against files
this session).

**Medium** for: the recommendation to publish 1.3.0 before refactoring (depends on the user's
release urgency and tolerance for re-rehearsal, which only the user can weigh) and the
recommendation to keep `semantic/`-package form over `semantic.py` (teammates doing depth
analysis of the semantic modules should confirm which side of the duplication is live code).

**Low** for: any estimate of third-party theory-author demand (the plugin-ecosystem trigger is
deliberately framed as a deferred ROADMAP item rather than scoped work for that reason).
