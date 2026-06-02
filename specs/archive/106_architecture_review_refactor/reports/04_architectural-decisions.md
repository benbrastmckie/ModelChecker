# Architectural Decision Record: bmlogic-oracle Clean-Break Refactor

**Task**: 106 - Architecture review of bimodal refactor plan (tasks 99-105)
**Date**: 2026-06-01
**Status**: ACCEPTED
**Research Basis**: Reports 01 (team research), 02 (team research: BimodalLogic alignment), 03 (clean-break architecture)

## Context

The ModelChecker codebase is being refactored from a multi-theory framework into a focused bimodal Z3 oracle (`bmlogic-oracle`) that implements the `OracleProvider` protocol expected by BimodalHarness. Three rounds of research identified the architecture, concrete implementation requirements, and critical soundness gaps. This ADR captures the nine key decisions that drive the refactor.

---

## Decision 1: Three-Repo Architecture

**Decision**: BimodalLogic (Lean 4) is the specification; ModelChecker (pure Python Z3) is the oracle executor; BimodalHarness (Python + Lean) is the soundness bridge. These roles are fixed and non-negotiable for the refactor.

**Rationale**:
- BimodalLogic defines the formal semantics. Any deviation in the oracle is either a bug or an undocumented approximation.
- ModelChecker's value is the Z3 implementation — fast, callable from Python, no Lean runtime required.
- BimodalHarness already owns the integration layer. Adding soundness verification there (via `fromStructuredCountermodel` in Lean) is incremental work on an existing foundation.

**Consequences**:
- ModelChecker has no Lean dependency and no code-level dependency on BimodalLogic.
- Soundness claims are owned by BimodalHarness, not ModelChecker.
- Changes to BimodalLogic semantics require manual update propagation to the Z3 encoding (tracked by `semantics_version`).

**Rejected alternatives**:
- Lean files in ModelChecker: adds Lean build complexity (~30 min for Mathlib); ModelChecker should remain pure Python.
- Separate verification repo: unnecessary fourth repo; BimodalHarness is already the integration layer.
- Code generation from Lean to Python: no mature facility for Lean-to-Python code generation.
- Lean FFI to Z3: research project, not practical for production use.

---

## Decision 2: Zero Code-Level Dependency Between ModelChecker and BimodalLogic

**Decision**: ModelChecker and BimodalLogic share NO code. They are coupled only through JSON schema contracts (formula_json in, StructuredCountermodel JSON out).

**Rationale**:
- A code-level dependency would require synchronizing Lean and Python build systems.
- JSON contracts are versioned (via `semantics_version`) and can be validated without importing either package.
- The oracle is either correct or incorrect — there is no "wrapper" that can paper over a soundness gap.

**Consequences**:
- `semantics_version` in the oracle output must pin to a specific BimodalLogic git tag or release.
- Formula encoding changes in BimodalLogic require a new oracle version.
- Cross-oracle differential testing (Task 109) is the empirical coupling mechanism.

**Rejected alternatives**:
- Python bindings for BimodalLogic types: would require maintaining Python stubs for every Lean type change.
- Shared schema package: premature; the JSON schema is currently stable and small.

---

## Decision 3: Two-Layer Package Structure (Thin OracleProvider Skin Over Preserved Z3 Core)

**Decision**: The `bmlogic_oracle` package has two layers: (1) three new files implementing the oracle interface (`provider.py`, `translation.py`, `serialization.py`) and (2) the preserved Z3 mathematical core from `theory_lib/bimodal/`. The existing directory structure is preserved — no `core/` subdirectory rename.

**Package structure**:
```
bmlogic_oracle/
├── __init__.py               # Public: Z3OracleProvider
├── provider.py               # OracleProvider implementation (new)
├── translation.py            # json_to_prefix(), temporal_depth() (new)
├── serialization.py          # CountermodelSerializer (new)
└── theory_lib/bimodal/       # Preserved Z3 core (unchanged internals)
    ├── semantic.py           # BimodalSemantics, BimodalProposition, BimodalStructure
    ├── operators.py
    ├── examples.py           # 43-example evaluation suite (PRESERVED)
    └── tests/                # Full test suite (PRESERVED)
```

**Rationale**:
- Preserving the directory structure avoids mass import renaming across ~20 files.
- The oracle skin is deliberately thin: 3 new files. The math is deep: the existing bimodal core.
- No intermediate representation between Z3 model and JSON serialization (direct dict → JSON, one transformation, not two).

**Rejected alternatives**:
- Rename to `core/` subdirectory: reduces task 101 scope but causes mass import renaming.
- Intermediate BimodalCountermodelObject: adds complexity with no benefit since BimodalHarness is the only consumer.

---

## Decision 4: Preserve Full Bimodal Test Suite and examples.py as Correctness Gate

**Decision**: `theory_lib/bimodal/tests/` and `theory_lib/bimodal/examples.py` are NOT dead code. They are the behavioral specification and must be preserved in full. The gate for task 100 is: "43 examples pass AND all unit tests in `theory_lib/bimodal/tests/unit/` pass."

**Tests to preserve**:

| Test | Content |
|------|---------|
| `test_bimodal.py` | 43 SAT/UNSAT examples — core oracle correctness gate |
| `test_frame_constraints.py` | Nullity, converse, compositionality unit tests |
| `test_foralltime.py` | `ForAllTime`/`ExistsTime` quantifier tests |
| `test_until_since.py` | Until/Since operator unit tests (alignment with `Truth.lean:122-131`) |
| `test_until_since_integration.py` | Integration tests for Until/Since in full context |
| `test_witness_constraints.py` | Witness predicate tests |
| `test_modal_witness_integration.py` | Modal integration tests |
| `test_strict_semantics.py` | Atom-outside-domain behavior (`atom_false_of_not_domain` alignment) |
| `test_api_consistency.py` | API stability regression tests |
| `test_data_extraction.py` | `extract_model_elements()` output correctness |
| `test_iterate.py` | Iterator tests |
| `test_injection.py` | Z3 injection/state isolation tests |

**Rationale**:
- These tests encode alignment with BimodalLogic semantics. Removing them loses the verification record.
- `examples.py` (43 examples) is the oracle's correctness contract. A refactor that breaks any example has introduced a regression.

**Consequences**:
- Task 104 ("dead-code cleanup") must have an explicit "do NOT remove" list.
- Task 105 must add `test_oracle_interface.py` running the same 43 examples through the new `OracleProvider.find_countermodel()` pipeline.

---

## Decision 5: Boundary Buffer via Dynamic M = max(temporal_depth(formula) + 2, 3)

**Decision**: For a formula of temporal nesting depth `d`, the oracle must use `M = max(d + 2, 3)` as the minimum time bound. The oracle reports `temporal_depth` and `boundary_safe` in every countermodel output.

**Rationale**:
The Z3 bimodal semantics uses bounded time domain `(-M, M)`. At boundary `t = M-1`, `G(phi)` is vacuously true because no future times exist. In BimodalLogic's infinite-domain semantics (with `NoMaxOrder`/`NoMinOrder`), this never happens. A Z3 countermodel exploiting boundary vacuity has no BimodalLogic analog — this is a concrete unsoundness risk.

Additionally, `capped_skolem_abundance_constraint` only guarantees shift closure for shifts within the domain. For formulas of depth `d` evaluated at `t=0`, requiring `M > d + 1` ensures the evaluation point is always at least `d` steps from both domain edges, preventing boundary vacuity for any temporal subformula.

**Practical bound**: `M = max(depth + 2, 3)` provides one step of margin beyond the minimal safe value.

**Output fields added to oracle result**:
```python
"temporal_depth": int,    # Maximum temporal nesting depth of formula
"boundary_safe": bool,    # True if M > temporal_depth + 1
"time_bound": int,        # M value used for this call
```

**Consequences**:
- Task 102 must implement `temporal_depth(formula_json) -> int` as a deliverable.
- Task 103 must use the dynamic M formula and report metadata fields.
- Task 107 is the full boundary analysis and proof task.

**Rejected alternatives**:
- Fixed M=3 for all formulas: unsound for formulas with temporal depth > 2.
- No boundary buffering: defers the soundness gap indefinitely; unacceptable.
- Full boundary proof first (block task 103): too heavyweight; the one-liner provides meaningful protection now.

---

## Decision 6: Ternary task_relation Serialization — (source, duration, target)

**Decision**: The oracle's `task_relation` output field uses ternary triples `{source, duration, target}`, not binary pairs. The extraction loop iterates all valid `(s, d, u)` combinations and evaluates `semantics.task_rel(s, d, u)` on the Z3 model.

**Ternary extraction loop** (to be implemented in Task 103):
```python
task_triples = []
N = semantics.N
M = semantics.M
for s in range(2**N):
    for d in range(-(M-1), M):
        for u in range(2**N):
            if is_true(z3_model.eval(semantics.task_rel(s, d, u))):
                task_triples.append({"source": s, "duration": d, "target": u})
```

Complexity: O(2^(2N) * (2M-1)) — 80 evaluations for N=2, M=3 (manageable).

**Rationale**:
- Both the Z3 encoding and BimodalLogic use ternary `(source, duration, target)`. Duration encodes task length in the bimodal frame.
- BimodalHarness `StructuredCountermodel` schema requires ternary triples for the soundness bridge.
- Binary pairs lose the duration information needed for `fromStructuredCountermodel` Lean parsing.

**Rejected alternatives**:
- Binary (source, target) pairs: loses duration; soundness bridge cannot reconstruct full frame.
- Separate duration field: unnecessarily complicates serialization; ternary is BimodalLogic's native representation.

---

## Decision 7: Empirical Soundness First (Tier 1 Testing), Formal Proofs Later

**Decision**: Tasks 99-105 and new tasks 107-110 target empirical soundness validation (Tier 1). Formal Lean proofs (Tier 2-3) are post-refactor work in BimodalHarness.

**Tier structure**:

| Tier | Mechanism | Timeline | Owner |
|------|-----------|----------|-------|
| 1 | Cross-oracle differential testing, frame axiom checking (Python), property-based testing with FormulaEnumerator | Alongside refactor | ModelChecker + BimodalHarness |
| 2 | Lean `fromStructuredCountermodel` parser + `validateCountermodel` theorem, CI cross-validation | 3-6 months post-refactor | BimodalHarness |
| 3 | Full Oracle Soundness theorem in Lean, specification compiler | 12+ months | BimodalHarness (research goal) |

**Rationale**:
- Tier 1 testing (Task 108 + Task 109) provides high confidence with modest effort.
- The SoundnessGateway already exists in BimodalHarness; Tier 1 uses it without modification.
- Blocking the refactor on formal proofs would delay delivery by 6-12 months for a marginal practical benefit (the Z3 oracle is already used empirically).

**Consequences**:
- Every oracle output includes `boundary_safe` flag so Tier 2 validation can prioritize boundary-unsafe results.
- `semantics_version` pins the specific BimodalLogic version the empirical tests were run against.

---

## Decision 8: Sentence.from_prefix() as Surgical Addition (Not Parser Rewrite)

**Decision**: Task 102 adds one classmethod `Sentence.from_prefix(prefix_list, operators)` to the existing `syntactic/sentence.py`. No other changes to `syntactic/` are needed.

**Classmethod signature**:
```python
@classmethod
def from_prefix(cls, prefix_list: list, operators: dict) -> 'Sentence':
    """Construct a Sentence from a prefix-list representation.
    
    prefix_list: e.g., ['\\Box', ['\\neg', ['p']]]
    operators: dict mapping operator names to Operator instances
    """
    ...
```

**Requirements**:
1. Accept a nested list in prefix form (matching `json_to_prefix()` output).
2. Construct `Sentence` objects recursively.
3. Call `update_types()` / `update_objects()` to handle defined operators via `derive_type()`.
4. Return a fully-formed `Sentence` with `.sentence_letter`, `.operator`, `.arguments` correctly populated.

**json_to_prefix() mapping** (6 BimodalLogic JSON tags → ModelChecker internal names):
```python
JSON_TO_PREFIX = {
    "atom": lambda n: [n["base"]],
    "bot":  lambda n: ["\\bot"],
    "imp":  lambda n: ["\\rightarrow", to_prefix(n["left"]), to_prefix(n["right"])],
    "box":  lambda n: ["\\Box", to_prefix(n["arg"])],
    "untl": lambda n: ["U", to_prefix(n["guard"]), to_prefix(n["reach"])],
    "snce": lambda n: ["S", to_prefix(n["guard"]), to_prefix(n["reach"])],
}
```

**Rationale**:
- The existing `update_types()` / `update_objects()` machinery already handles defined operators. Calling them on a programmatically-constructed tree costs one method call.
- A full parser rewrite would discard tested infix parsing infrastructure and risk regressions.

**Open question for Task 102**: Does `Syntax.__init__()` currently accept `Sentence` objects directly, or only infix strings? If only infix strings, a programmatic constructor overload is also a Task 102 deliverable.

---

## Decision 9: Fresh BimodalSemantics Instance Per find_countermodel() Call for Z3 Isolation

**Decision**: The oracle creates a new `BimodalSemantics` instance for every `find_countermodel()` call. The instance is not stored between calls (`self._semantics = None` between calls).

**Rationale**:
- `BimodalSemantics.__init__()` calls `_reset_global_state()`, providing clean Z3 state.
- The `isolated_z3_context()` utility in `utils/context.py` wraps each call for additional isolation.
- Reusing a `BimodalSemantics` instance between calls risks Z3 state accumulation (leaked constraints, stale solver state from `push()`/`pop()` mismatches).

**Consequences**:
- Per-call overhead: Z3 sort and function re-creation. Acceptable: Z3 functions are lightweight compared to solving.
- Task 103 must implement the isolation pattern as specified.
- Task 108 (soundness regression tests) must verify no state leakage via 100+ sequential calls.

**Rejected alternatives**:
- Reuse `BimodalSemantics` with manual reset: `_reset_global_state()` is designed for CLI use; its behavior in oracle context is untested.
- Global Z3 context: non-isolatable; any constraint leak persists for the process lifetime.

---

## Pipeline Diagram

The complete oracle pipeline from formula JSON to countermodel output:

```
formula_json (BimodalLogic JSON schema)
    │
    ▼
json_to_prefix(formula_json)            # translation.py — maps 6 tags to prefix list
    │
    ▼
Sentence.from_prefix(prefix, operators) # syntactic/sentence.py — programmatic Sentence
    │
    ▼
Syntax(operators, sentences=[sentence]) # syntactic/ — formula representation layer
    │
    ▼
BimodalSemantics(N=2, M=max(depth+2,3)) # theory_lib/bimodal/semantic.py — Z3 constraints
    │
    ▼
ModelConstraints(settings, syntax, semantics, BimodalProposition)  # models/constraints.py
    │
    ▼
BimodalStructure(model_constraints, max_time)  # theory_lib/bimodal/semantic.py
    │                                           # Z3 solving happens in __init__
    ├── satisfiable == False → return None
    ├── timeout == True → return None
    │
    ▼
extract_model_elements(z3_model)        # world_histories, task_rel triples, etc.
    │
    ▼
serialize_countermodel(structure, formula_json, depth, M)  # serialization.py
    │
    ▼
{
    "trueAtoms": [...],
    "falseAtoms": [...],
    "formula": formula_json,
    "world_histories": [...],
    "task_relation": [{"source": s, "duration": d, "target": u}, ...],
    "truth_valuation": {...},
    "evaluation_world": 0,
    "evaluation_time": 0,
    "world_count": int,
    "time_bound": int,           # M used
    "temporal_depth": int,       # depth of formula
    "boundary_safe": bool,       # M > temporal_depth + 1
    "semantics_version": "...",  # BimodalLogic version
}
```

---

## Keep/Drop/Fix Inventory

### Keep (required by oracle pipeline)

| Component | Location | Reason |
|-----------|----------|--------|
| `BimodalSemantics` | `theory_lib/bimodal/semantic.py:49` | All Z3 constraint builders |
| `BimodalProposition` | `theory_lib/bimodal/semantic.py:1913` | `find_extension()` for truth profiles |
| `BimodalStructure` | `theory_lib/bimodal/semantic.py:2222` | `extract_model_elements()`, model extraction |
| `ModelConstraints` | `models/constraints.py` | Syntax→semantics→Z3 assembly |
| `syntactic/` | `syntactic/` | Operator collection, Sentence, Syntax |
| `solver/` | `solver/` | Z3 adapter, `create_solver()`, isolation utilities |
| `models/semantic.py` | `models/semantic.py` | `SemanticDefaults` base class |
| `models/proposition.py` | `models/proposition.py` | `PropositionDefaults` base class |
| `models/structure.py` | `models/structure.py` | `ModelDefaults` base class |
| `utils/` | `utils/` | `ForAll`, `Exists`, `bitvec_to_worldstate`, helpers |
| `operators.py` | `theory_lib/bimodal/operators.py` | All operator implementations |
| `examples.py` | `theory_lib/bimodal/examples.py` | 43-example evaluation suite |
| `tests/` | `theory_lib/bimodal/tests/` | Full test suite (correctness gate) |

### Drop (multi-theory framework artifacts)

| Component | Location | Reason |
|-----------|----------|--------|
| `logos/` | `theory_lib/logos/` | Multi-theory; no bimodal use |
| `imposition/` | `theory_lib/imposition/` | Multi-theory subtheory |
| `exclusion/` | `theory_lib/exclusion/` | Multi-theory subtheory |
| `jupyter/` | `jupyter/` | Notebook templates |
| `output/notebook/` | `output/notebook/` | Notebook output formatter |
| `iterate/` | `iterate/` | Model iteration (oracle needs one countermodel) |
| `code/tests/` | `code/tests/` | Logos-specific top-level tests |
| `builder/comparison.py` | `builder/comparison.py` | Multi-theory comparison |
| `builder/` scaffolding | `builder/` | Project scaffolding (multi-theory) |
| `networkx` dep | `pyproject.toml` | No longer needed |
| `matplotlib` dep | `pyproject.toml` | No longer needed |
| `cvc5` dep | `pyproject.toml` | No longer needed |
| `jupyter` dep | `pyproject.toml` | No longer needed |

### Fix (broken wiring — hard coupling points)

| Component | Location | Issue |
|-----------|----------|-------|
| logos import | `theory_lib/__init__.py:52` | Unconditional `from model_checker.theory_lib import logos` crashes on deletion |
| logos semantic | `builder/example.py:34` | `from ..theory_lib.logos import semantic` — logos-specific init |
| logos branching | `builder/runner.py:82,206` | `if 'Logos' in semantics_class.__name__` — logos-specific branching |

---

## Dependency Graph

Full dependency graph for tasks 100-110 (bimodal refactor + new tasks from task 106 research):

### Adjacency List

```
100 (strip non-bimodal) → 101, 102, 110
101 (restructure pip)   → 103
102 (formula JSON)      → 103, 107
103 (OracleProvider)    → 104, 108, 109
104 (dead-code cleanup) → 105
107 (boundary analysis) → (none; standalone)
108 (soundness tests)   → (none; standalone)
109 (cross-oracle)      → (none; standalone)
110 (frame validation)  → (none; standalone)
```

### Wave Structure (Parallel Execution Waves)

| Wave | Tasks | Blocked by |
|------|-------|------------|
| 1 | 100 | — (none) |
| 2 | 101, 102, 110 | 100 |
| 3 | 103, 107 | 101+102 (103); 102 (107) |
| 4 | 104, 108 | 103 |
| 5 | 105, 109 | 103+104 (105); 103 (109) |

### ASCII DAG

```
100
├── 101
│   └── 103
│       ├── 104
│       │   └── 105
│       ├── 108
│       └── 109
├── 102
│   ├── 103 (see above)
│   └── 107
└── 110
```

### Cycle Check

Topological order: 100 → 110 → 102 → 107 → 101 → 103 → 108 → 109 → 104 → 105

No cycles detected (DAG confirmed).
