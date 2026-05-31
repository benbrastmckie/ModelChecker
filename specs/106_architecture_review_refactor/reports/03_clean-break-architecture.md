# Research Report: Clean-Break Architecture for bmlogic-oracle

**Task**: 106 - Architecture review of bimodal refactor plan (tasks 99-105)
**Date**: 2026-05-30
**Mode**: Single-agent deep research
**Session**: sess_1780192594_f5ac21
**Artifact**: 03 — clean-break architecture

## Summary

This report synthesizes the findings from previous team research (reports 01 and 02) and the oracle integration plan (BimodalLogic task 226) into actionable architectural recommendations for the clean-break refactor. The core thesis: the right architecture is a **two-layer Python package** — a thin `OracleProvider` skin over a self-contained Z3 core — with all useful testing and evaluation infrastructure preserved in-place (not stripped). The "clean-break" means no backwards compatibility *with the multi-theory framework*, not removing the rich bimodal-specific machinery.

The boundary problem identified by round 2 research is the single most important unresolved question. Any soundness claim requires explicit boundary buffer constraints or a temporal-depth argument. This work should be scheduled as task 107 (a new task) before the oracle claim is published.

## 1. The Inspiration: BimodalLogic Task 226 Oracle Integration Plan

The BimodalLogic task 226 plan provides a model of the clean-room philosophy: "the same math, stripped of everything else." The key architectural insight from that plan:

- **Zero code-level dependency** between ModelChecker and BimodalLogic. Coupling is through JSON schema contracts only.
- **BimodalHarness owns the soundness bridge** — it imports BimodalLogic (Lean) and translates oracle output into Lean types for verification.
- **The oracle is the executive branch**: it runs the Z3 math and returns a structured result. It does not own the verification claim.

The plan explicitly rejects wrappers, bridges, and shims at the Python-to-Python boundary. The oracle is either correct (finds countermodels aligned with BimodalLogic semantics) or it is not — there is no "wrapper" that can paper over a soundness gap.

**Implication for tasks 99-105**: The refactored package must be a clean Python implementation of the math, not a thin wrapper over the current multi-theory framework. Every abstraction retained must earn its place by serving the Z3 solving pipeline or the testing infrastructure.

## 2. What "Clean-Break" Means Concretely

After reading the full codebase, the distinction between "what to keep" and "what to drop" is clear:

### Keep: The Z3 Mathematical Core

These components implement the bimodal math and must be preserved with zero alteration:

| Component | Location | Why Keep |
|-----------|----------|----------|
| `BimodalSemantics` | `theory_lib/bimodal/semantic.py:49` | All Z3 constraint builders live here — the entire math |
| `BimodalProposition` | `theory_lib/bimodal/semantic.py:1913` | `find_extension()` computes truth profiles; needed for countermodel extraction |
| `BimodalStructure` | `theory_lib/bimodal/semantic.py:2222` | Model extraction: `extract_model_elements()`, world histories, time-shift relations |
| `ModelConstraints` | `models/constraints.py` | Links syntax→semantics→Z3; the assembly layer for the pipeline |
| `syntactic/` | `syntactic/` | Operator collection, Sentence objects, `Syntax` — the formula representation layer |
| `solver/` | `solver/` | Z3 adapter, `create_solver()`, `SolverResult`, isolation utilities |
| `models/semantic.py` | `models/semantic.py` | `SemanticDefaults` base class — bimodal extends this |
| `models/proposition.py` | `models/proposition.py` | `PropositionDefaults` base class — bimodal extends this |
| `models/structure.py` | `models/structure.py` | `ModelDefaults` base class — bimodal extends this |
| `utils/` | `utils/` | `ForAll`, `Exists`, `bitvec_to_worldstate`, `pretty_set_print` — used throughout |
| `witness_registry.py` | `theory_lib/bimodal/semantic/` | Modal operator witness predicates — Phase 4 integration |
| `witness_constraints.py` | `theory_lib/bimodal/semantic/` | Witness constraint generation — Phase 4 integration |

### Keep with Modification: The Formula Representation Layer

The `syntactic/` module must be extended (not replaced) to support programmatic construction:

- `Sentence` needs a `from_prefix()` classmethod — a surgical addition, not a replacement
- `Syntax` needs to accept `Sentence` objects directly (not just infix strings from files)
- The `atoms.py`, `operators.py`, `formulas.py` chain must remain intact — it handles `derive_type()` for defined operators

### Keep: The Bimodal Testing Infrastructure

The entire `theory_lib/bimodal/tests/` tree must be preserved. These tests are not just regression tests — they are the behavioral specification:

| Test | Content | Why It Matters |
|------|---------|----------------|
| `test_bimodal.py` | 43 SAT/UNSAT examples | Core oracle correctness gate |
| `test_frame_constraints.py` | Nullity, converse, compositionality unit tests | Verifies the TaskFrame axioms hold in isolation |
| `test_foralltime.py` | `ForAllTime`/`ExistsTime` quantifier tests | Verifies temporal quantifiers align with BimodalLogic |
| `test_until_since.py` | Until/Since operator unit tests | Direct alignment with `Truth.lean:122-131` |
| `test_until_since_integration.py` | Integration tests | Until/Since in full solving context |
| `test_witness_constraints.py` | Witness predicate tests | Modal operator soundness |
| `test_modal_witness_integration.py` | Modal integration tests | Box/Diamond in full context |
| `test_strict_semantics.py` | Atom-outside-domain behavior | Verifies `atom_false_of_not_domain` alignment |
| `test_api_consistency.py` | API stability tests | Regression against interface changes |
| `test_data_extraction.py` | Model extraction tests | `extract_model_elements()` output correctness |
| `test_iterate.py` | Iterator tests | Z3 model iteration soundness |
| `test_injection.py` | Z3 injection tests | State isolation between calls |

The `examples.py` file (the 43-example test suite with SAT/UNSAT expectations) is also critical evaluation infrastructure — it defines the correctness contract.

### Drop: Everything Multi-Theory

The following can be deleted cleanly:

- `theory_lib/logos/` — the logos theory and all its subtheories
- `theory_lib/imposition/` — imposition subtheory
- `theory_lib/exclusion/` — exclusion subtheory
- `jupyter/` — notebook templates
- `output/notebook/` — notebook output formatter
- `iterate/` — model iteration (OracleProvider needs one countermodel, not iteration)
- `code/tests/` — top-level test suite (logos-specific; bimodal tests live in `theory_lib/bimodal/tests/`)
- Multi-theory comparison code in `builder/comparison.py`
- Project scaffolding in `builder/`

### Fix: Hard Coupling Points

These are broken wiring, not features:

- `theory_lib/__init__.py:52` — unconditional logos import crashes on deletion; replace with direct bimodal-only export
- `builder/example.py:34` — `from ..theory_lib.logos import semantic`; remove logos-specific initialization
- `builder/runner.py:82,206` — `if 'Logos' in semantics_class.__name__`; remove logos-specific branching

## 3. The Pipeline Architecture

The correct programmatic pipeline, derived from reading the calling code in `ModelDefaults.__init__()` and `ModelConstraints.__init__()`:

```
formula_json
    │
    ▼
json_to_prefix(formula_json)           # New function in bmlogic_oracle/translation.py
    │
    ▼
Sentence.from_prefix(prefix, operators) # New classmethod on syntactic.Sentence
    │
    ▼
Syntax(operators, sentences=[sentence]) # Existing class, needs programmatic constructor
    │
    ▼
BimodalSemantics(settings)             # Existing class, unchanged
    │
    ▼
ModelConstraints(settings, syntax, semantics, BimodalProposition)  # Existing class
    │
    ▼
BimodalStructure(model_constraints, max_time)  # Existing class
    │
    ▼
z3_model = structure.z3_model           # Existing: solve happened in __init__
    │
    ├── structure.satisfiable → None if UNSAT
    ├── structure.timeout → None if timeout
    │
    ▼
extract_model_elements(z3_model)       # Existing: world_histories, task_rel, etc.
    │
    ▼
serialize_countermodel(structure, formula_json)  # New: maps to BimodalHarness schema
    │
    ▼
OracleProvider.find_countermodel() returns dict or None
```

### Key Pipeline Invariants

1. **One `BimodalSemantics` per `find_countermodel()` call** — `_reset_global_state()` is called in `__init__`, so constructing a fresh instance provides Z3 isolation. Do not reuse instances between calls.

2. **`BimodalStructure.__init__()` triggers Z3 solving** — the solver runs in `super().__init__()` via `ModelDefaults.__init__()`. This means construction = solve. The caller just reads the result from `structure.z3_model_status` and `structure.z3_model`.

3. **Timeout is `max_time` in settings** — the `max_time` key in the settings dict maps directly to `BimodalStructure(model_constraints, max_time)`. The oracle must convert `timeout_ms` from the protocol to seconds for settings.

4. **`find_extension()` is called during `BimodalProposition.__init__()`** — this evaluates the truth profile for output formatting. It requires a valid `z3_model`. For the oracle use case, propositions are only needed for atom extraction, not for display — but this is still triggered automatically.

### The Countermodel Serialization Boundary

The `extract_model_elements()` method returns a 4-tuple:
```python
(world_histories, main_world_history, world_arrays, time_shift_relations)
```

Where:
- `world_histories: dict[int, dict[int, str]]` — `{world_id: {time: state_label}}`
- `main_world_history: dict[int, str]` — `{time: state_label}` for world 0
- `world_arrays: dict[int, Z3Array]` — raw Z3 arrays (not needed for serialization)
- `time_shift_relations: dict[int, dict[int, int]]` — `{source: {shift: target}}`

The `task_rel` is extracted by iterating all valid `(source_state, duration, target_state)` tuples and evaluating `semantics.task_rel(s, d, u)` on the `z3_model`. The current `extract_relations()` method only extracts `time_shift_relations` — the task relation extraction for oracle output must be added.

**Critical finding**: The BimodalHarness `StructuredCountermodel` schema requires ternary `(source, duration, target)` triples, not the binary pairs that existed before the ternary refactor. The current `extract_model_elements()` does not enumerate `task_rel` triples. Task 103 must include this enumeration.

The ternary extraction loop:
```python
task_triples = []
N = semantics.N
M = semantics.M
for s in range(2**N):
    for d in range(-(M-1), M):
        for u in range(2**N):
            if is_true(z3_model.eval(semantics.task_rel(s, d, u))):
                task_triples.append((s, d, u))
```

This is O(2^(2N) * (2M-1)) — manageable for N=2,M=3 (4*5*4 = 80 evaluations) but grows for larger bounds.

## 4. The Boundary Problem: Why It Cannot Be Ignored

Round 2 research identified the boundary problem as the critical soundness gap. Reading the code confirms its reality.

The `is_valid_time()` method at `semantic.py:699` defines the time domain as the open interval `(-M, M)`:
```python
return z3.And(given_time > -self.M + offset, given_time < self.M + offset)
```

For M=3, this gives times `{-2, -1, 0, 1, 2}`. The evaluation point is fixed at `t=0` (`self.main_time = z3.IntVal(0)`). The `FutureOperator.true_at()` asserts that argument holds at all `t > eval_time` in domain D. At `t=2` (the domain boundary), `G(phi)` is vacuously true because no future times exist.

The `ForAllTime` method at `semantic.py:390`:
```python
return z3.ForAll(
    time_var,
    z3.Implies(
        self.is_valid_time(time_var),  # All times in D
        body
    )
)
```

This quantifies over ALL times in D, not just the world's interval — which is the intended BimodalLogic alignment. But the domain D is finite, so temporal operators near the boundary behave differently than in the infinite-domain Lean semantics.

**The `capped_skolem_abundance_constraint` limitation**: This constraint at `semantic.py:1275` provides shift closure for shifts within the domain. But it only guarantees that shifted-world copies exist when the shifted interval stays within the global range. For evaluation at t=0 with M=3, there exist worlds with interval [-2,2] that cannot be shifted forward by 3 (since shifted end would be 5 > M-1=2). This means shift closure is only partial near the boundary.

### Required Mitigation for Task 103 (OracleProvider)

The OracleProvider must include boundary buffering as part of its constraint generation. The approach recommended by round 2 research:

1. **Temporal depth analysis**: For a formula with temporal nesting depth `d`, require `M > d + margin` where `margin >= 1`.
2. **Practical bound**: For the oracle, use `M = max(temporal_depth(formula) + 2, 3)` as the minimum safe value.
3. **Report temporal depth**: Include `temporal_depth` in the oracle's output so downstream validators can assess boundary safety.

The `temporal_depth()` function must be implemented as part of task 102 (formula translation layer), since it requires walking the formula AST.

**This is not a blocking issue for task 103** — the oracle can function with the understanding that models near the boundary require extra validation. But the oracle must report `temporal_depth` and the `M` bound used, so BimodalHarness can flag countermodels that exploit boundary vacuity.

## 5. Architecture Recommendations

### Recommendation 1: Two-Layer Package Structure

The `bmlogic_oracle` package should have exactly two layers:

```
bmlogic_oracle/
├── __init__.py               # Public: Z3OracleProvider
├── provider.py               # OracleProvider implementation (new)
├── translation.py            # json_to_prefix(), temporal_depth() (new)
├── serialization.py          # CountermodelSerializer (new)
└── core/                     # The Z3 mathematical core (preserved from model_checker)
    ├── semantic.py           # BimodalSemantics, BimodalProposition, BimodalStructure
    ├── semantic/             # witness_registry.py, witness_constraints.py
    ├── operators.py          # All operator implementations
    ├── models/               # SemanticDefaults, PropositionDefaults, etc.
    ├── syntactic/            # Sentence, Syntax, operator collection
    ├── solver/               # Z3 adapter
    └── utils/                # ForAll, Exists, bitvec_to_worldstate
```

The `core/` directory is the preserved model_checker bimodal core. The top-level files are new: they implement the oracle interface. This separation makes the architecture legible: the oracle skin is thin (3 new files) and the math is deep (the existing core).

**Alternative**: Keep the existing directory structure without renaming to `core/` — this avoids mass-renaming imports and reduces task 101 scope. The public API is all that matters for BimodalHarness discovery (the entry point in pyproject.toml). Internal structure is a preference, not a contract.

**Recommendation**: Keep the existing structure, do not create a `core/` subdirectory. This reduces task 100 to import fixing, not mass file movement.

### Recommendation 2: Preserve examples.py as a Test Oracle

The `theory_lib/bimodal/examples.py` file is the single most valuable testing artifact in the package. Its 43 examples encode the correctness contract. Do not delete or reduce it during the refactor.

The refactor should add a `test_oracle_interface.py` that runs the same 43 examples through the new `OracleProvider.find_countermodel()` pipeline and verifies identical SAT/UNSAT results. This is distinct from `test_bimodal.py` (which tests the internal `run_test` pipeline) — the oracle test verifies the pipeline through the public interface.

### Recommendation 3: No Intermediate Representation at the Z3 Layer

The task 226 plan warns against "wrappers, bridges, shims." Concretely for this refactor: do not create an intermediate Python countermodel object between the Z3 model and the JSON serialization. The current `extract_model_elements()` returns raw Python dicts — serialize those directly to the BimodalHarness schema. One transformation layer, not two.

The pipeline should be:
```
Z3 model → extract_model_elements() → direct dict → JSON
```
Not:
```
Z3 model → extract_model_elements() → BimodalCountermodelObject → .to_json() → JSON
```

The intermediate object is a temptation when there are multiple callers with different schema requirements. But since there is exactly one consumer (BimodalHarness), the intermediate object is complexity without benefit.

### Recommendation 4: Sentence.from_prefix() is a Surgical Add

The `Sentence` class (`syntactic/sentence.py`) currently requires an infix string to be parsed. Task 102's core work is adding one classmethod:

```python
@classmethod
def from_prefix(cls, prefix_list: list, operators: dict) -> 'Sentence':
    """Construct a Sentence from a prefix-list representation.
    
    prefix_list: e.g., ['\\Box', ['\\neg', ['p']]]
    operators: dict mapping operator names to Operator instances
    """
    ...
```

This classmethod must:
1. Accept a nested list in prefix form
2. Construct `Sentence` objects recursively
3. Call `update_types()` / `update_objects()` to handle defined operators via `derive_type()`
4. Return a fully-formed `Sentence` with `.sentence_letter`, `.operator`, `.arguments` correctly populated

The existing `update_types()` / `update_objects()` machinery already handles defined operators (like `→` which expands via `DefinedOperator`). No changes to those methods are needed — they just need to be called on the programmatically-constructed tree.

The `json_to_prefix()` function maps the 6 BimodalLogic JSON tags to ModelChecker internal names:
```python
JSON_TO_PREFIX = {
    "atom": lambda n: [n["base"]],       # atom node → variable name
    "bot":  lambda n: ["\\bot"],
    "imp":  lambda n: ["\\rightarrow", to_prefix(n["left"]), to_prefix(n["right"])],
    "box":  lambda n: ["\\Box", to_prefix(n["arg"])],
    "untl": lambda n: ["U", to_prefix(n["guard"]), to_prefix(n["reach"])],
    "snce": lambda n: ["S", to_prefix(n["guard"]), to_prefix(n["reach"])],
}
```

The formula JSON uses a tree structure with `tag` fields — this mapping is mechanical once the field names in the BimodalLogic `Formula.toJson` output are confirmed.

### Recommendation 5: Z3 Context Isolation Strategy

The current `BimodalSemantics._reset_global_state()` method at `semantic.py:96` is designed for the CLI use case where one semantics instance is reused across example runs. For the oracle use case (100+ calls in sequence), a different strategy is needed.

The recommended approach: **construct a fresh `BimodalSemantics` instance per `find_countermodel()` call**. This is safe because `_reset_global_state()` is called in `__init__`, so each construction starts clean. The cost is Z3 sort/function re-creation per call, but Z3 functions are lightweight compared to solving.

The `isolated_z3_context()` utility already exists in `utils/context.py` and is used by `test_bimodal.py`. The oracle should wrap each `find_countermodel()` call in this context manager.

Additional isolation: do not hold a reference to `BimodalSemantics` between calls. The oracle's `__init__` should set `self._semantics = None` and only create it during `find_countermodel()`.

### Recommendation 6: The Testing Infrastructure Is Not Dead Code

Task 104 ("Dead-code cleanup") should explicitly **not** remove:
- `theory_lib/bimodal/tests/` — the full test suite
- `theory_lib/bimodal/examples.py` — the 43-example evaluation suite
- `theory_lib/bimodal/operators.py` — the operator implementations
- The model extraction chain (`extract_model_elements()`, `extract_states()`, etc.)
- The `print_*` methods on `BimodalStructure` — these are needed for the thin CLI

The danger in task 104 is confusing "infrastructure not on the critical path to OracleProvider" with "dead code." Output formatters are used by the thin CLI. Testing infrastructure is the correctness gate. Examples.py is both a test and a development tool.

Task 104 should have a clear scope: only remove code that was exclusively used by the multi-theory CLI (project scaffolding, multi-theory comparison, Jupyter export, progress bars for interactive prompts). Nothing bimodal-specific goes away until it can be shown to be unreachable from the oracle pipeline OR the test infrastructure.

### Recommendation 7: Add a Boundary Buffer Task (Task 107)

The existing tasks 99-105 have no task for the boundary problem. This is a gap. A new task should be created:

**Task 107: Boundary buffer constraints for oracle soundness**
- Implement `temporal_depth(formula_json) -> int` function
- Add `M_from_formula(formula_json, margin=2) -> int` — compute minimum safe M
- Add boundary buffer constraints to `BimodalSemantics` that prevent evaluation of temporal operators within `d` steps of domain boundary (where `d = temporal_depth`)
- Regression test: verify that known-valid formulas still return None, and known-invalid formulas still return countermodels
- Document the boundary claim: "for formulas of temporal depth d evaluated with M > d + 1, no boundary effects can create spurious countermodels"

This task is independent of 103 (it modifies `BimodalSemantics` inputs, not the oracle interface) and can run in parallel with task 103 or after it.

### Recommendation 8: StructuredCountermodel Format Must Include temporal_depth

The oracle's `find_countermodel()` return dict should include:

```python
{
    # Required by BimodalHarness schema:
    "trueAtoms": [...],
    "falseAtoms": [...],
    "formula": formula_json,
    
    # Structured countermodel fields:
    "world_histories": [...],        # list of {world_id, times: {t: state_label}}
    "task_relation": [...],          # list of {source, duration, target} ternary triples
    "truth_valuation": {...},        # {atom_name: {world_id: {time: bool}}}
    "evaluation_world": 0,
    "evaluation_time": 0,
    "world_count": int,
    "time_bound": int,               # M used for this countermodel
    
    # Oracle metadata (new — not in current BimodalHarness schema, but should be added):
    "temporal_depth": int,           # depth of formula
    "boundary_safe": bool,           # M > temporal_depth + 1?
    "semantics_version": "...",      # BimodalLogic version this was validated against
}
```

The `boundary_safe` flag is a self-report from the oracle. BimodalHarness can filter on it or flag it in the soundness gateway.

## 6. The G/H Equivalence Question

This is addressed correctly in task 102, but the precise verification requirement bears spelling out.

ModelChecker has `FutureOperator` (`\Past` alias `\Future`) and `PastOperator` (`\Past`) as **primitive** operators. BimodalLogic derives `G` (globally/future) from `U` and `H` (historically/past) from `S`:
- `G(φ) = ¬F(¬φ)` where `F(φ) = U(⊤, φ)` (or the equivalent using Until)
- `H(φ) = ¬P(¬φ)` where `P(φ) = S(⊤, φ)` (or the equivalent using Since)

The 6-tag JSON has no G or H tags — only `box`, `untl`, `snce`, `atom`, `bot`, `imp`. This means:
- Any formula that uses `G` or `H` in BimodalLogic must arrive at the oracle already expanded into `U`/`S` combinations
- The oracle never receives G/H directly

The G/H equivalence verification in task 102 is asking: does the oracle's `FutureOperator` compute the same Z3 constraint as the encoding `¬U(¬φ, ⊤)`? If yes, the oracle can be used directly for any formula containing `\Future` or `\Past`. If no, the oracle must only be used with formulas containing `U` and `S`.

The correct resolution: **verify the equivalence, and if it holds, register `\Future` as an alias for the `¬U(¬φ, ⊤)` encoding in the translation layer.** This allows both encoding paths to exist without confusion.

## 7. What the "Clean Break" Actually Buys

The clean break from the multi-theory ModelChecker framework buys three things:

1. **Correctness confidence**: The oracle's behavior is determined entirely by the bimodal Z3 constraints. No multi-theory dispatch, no theory registry, no lazy loading that could route to the wrong semantics.

2. **Z3 isolation feasibility**: Removing the global state that the multi-theory framework accumulated (logos-specific state in `_reset_global_state()`, etc.) makes Z3 isolation per oracle call straightforward.

3. **Dependency reduction**: Removing networkx, matplotlib, cvc5, jupyter dependencies reduces the install footprint and eliminates non-Z3 failure modes.

The clean break does NOT require:
- A rewrite of the Z3 constraints
- A new formula representation layer
- A new model extraction layer
- Any change to the tested bimodal behavior

The 43-example test suite should pass with zero changes to any bimodal-specific code. If any test fails after the refactor, the refactor introduced a regression.

## 8. Task Sequencing Implications

Given these findings, the task ordering in the current plan (100 → [101 ∥ 102] → 103 → 104 → 105) is correct. However, two adjustments are warranted:

### Adjustment 1: Make task 100's gate explicit about testing infrastructure

Current gate: "43 examples pass." Revised gate: "43 examples pass AND all unit tests in `theory_lib/bimodal/tests/unit/` pass." The unit tests for frame constraints, ForAllTime, Until/Since, and witness predicates are independent of the multi-theory framework and must continue passing throughout the refactor.

### Adjustment 2: Add temporal_depth to task 102

Task 102 should include `temporal_depth(formula_json) -> int` as a deliverable. This is a pure recursive function on the JSON AST and takes minimal effort. It enables task 103's boundary buffering logic without requiring a separate task.

### Optional Adjustment 3: Move boundary buffering into task 103

If task 107 is too heavyweight to schedule immediately, the minimum viable boundary mitigation can be folded into task 103:

```python
def find_countermodel(self, formula_json, frame_class="Base", timeout_ms=5000):
    depth = temporal_depth(formula_json)
    M = max(depth + 2, 3)  # Minimum safe M
    settings = {**DEFAULT_SETTINGS, "M": M, "max_time": timeout_ms / 1000}
    # ... rest of pipeline
```

This one-liner provides meaningful protection without the full boundary proof. The full analysis (task 107) can follow later.

## 9. Preserved Features Inventory

For completeness, this is what the refactored package preserves from the current codebase:

**Preserved (required by oracle pipeline)**:
- All of `BimodalSemantics` including all constraint builders
- All of `BimodalProposition` including `find_extension()`
- All of `BimodalStructure` including `extract_model_elements()`, `print_world_histories()`, `print_evaluation()`
- All operator implementations in `operators.py`
- All of `syntactic/` (formula parsing and representation)
- All of `solver/` (Z3 adapter and isolation utilities)
- The `models/` base classes (`SemanticDefaults`, `PropositionDefaults`, `ModelDefaults`, `ModelConstraints`)
- The `utils/` helpers

**Preserved (required by testing infrastructure)**:
- All of `theory_lib/bimodal/tests/`
- `theory_lib/bimodal/examples.py` (43-example evaluation suite)

**Preserved (required by thin CLI)**:
- `BimodalStructure.print_all()`, `print_world_histories()`, `print_evaluation()`
- `output/formatters/` (for structured output formatting)
- `settings/settings.py` (for CLI settings parsing)

**Dropped (multi-theory framework)**:
- `theory_lib/logos/`, `theory_lib/imposition/`, `theory_lib/exclusion/`
- `theory_lib/__init__.py` registry (replaced with direct bimodal-only export)
- `iterate/` module (not needed for single-countermodel oracle)
- `jupyter/`, `output/notebook/` (Jupyter integration)
- `builder/` project scaffolding (multi-theory project generation)
- `code/tests/` top-level test suite (logos-specific tests)
- Multi-theory comparison (`builder/comparison.py`)
- `networkx`, `matplotlib`, `cvc5`, `jupyter` dependencies

## 10. Key Open Questions for Implementation

1. **`Syntax` programmatic constructor**: Does `Syntax.__init__()` currently accept `Sentence` objects directly, or only infix strings? If only infix strings, this is a task 102 deliverable alongside `Sentence.from_prefix()`.

2. **`formula_json` field names**: The BimodalHarness `OracleProvider` doc says formula_json uses tags `atom`, `bot`, `imp`, `box`, `untl`, `snce`. What are the exact field names for each node type (e.g., `atom.base`, `imp.left`/`imp.right`, `box.arg`, `untl.guard`/`untl.reach`)? Task 102 must confirm these from the BimodalLogic `Formula.toJson` output or BimodalHarness schema documentation.

3. **`task_relation` format for BimodalHarness**: Does `StructuredCountermodel.task_relation` in BimodalHarness expect ternary `(source, duration, target)` triples or has it already been updated from binary? Confirm before task 103 serialization work.

4. **`semantics_version` source**: Where in BimodalLogic is the canonical semantics version defined? The oracle needs to pin against a specific value. Task 103 should include locating or creating this version tag.

5. **`validate_self` spot-check formulas format**: BimodalHarness `_mock.py` has `SPOT_CHECK_FORMULAS`. Are these in the `formula_json` format expected by `find_countermodel()`? Confirm before implementing `validate_self`.

## Summary of Recommendations

| Priority | Recommendation | Task |
|----------|----------------|------|
| Critical | Preserve the full bimodal test suite | Task 100 gate |
| Critical | Add temporal_depth() to translation layer | Task 102 |
| Critical | Boundary buffer (minimum viable: dynamic M) | Task 103 |
| High | Two-layer package structure (no intermediate objects) | Task 101/103 |
| High | Surgical `Sentence.from_prefix()` (not full rewrite) | Task 102 |
| High | Ternary task_relation triples in serialization | Task 103 |
| Medium | Report boundary_safe flag in oracle output | Task 103 |
| Medium | Add full oracle pipeline test (through OracleProvider) | Task 105 |
| Medium | Create task 107: boundary proof | New task |
| Low | `semantics_version` pinning | Task 103 |
