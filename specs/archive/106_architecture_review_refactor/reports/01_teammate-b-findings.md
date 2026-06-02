# Teammate B Findings: Interface Design and API Surface Analysis

**Task**: 106 - Architecture review of bimodal refactor plan
**Angle**: Alternative approaches — interface/API design between ModelChecker and BimodalHarness
**Date**: 2026-05-30

## Key Findings

### 1. Operator Mapping: Clean but Requires Careful Translation

The 6-tag JSON format maps to ModelChecker internals as follows:

| JSON Tag | JSON Structure | MC Internal Name | MC Operator | Primitive? |
|----------|---------------|------------------|-------------|------------|
| `atom` | `{"tag": "atom", "name": "p"}` | Z3 `Const("p", AtomSort)` | (no operator) | N/A |
| `bot` | `{"tag": "bot"}` | `\bot` | `BotOperator` | Yes |
| `imp` | `{"tag": "imp", "left": ..., "right": ...}` | `\rightarrow` | `ConditionalOperator` | **No** (defined as `¬A ∨ B`) |
| `box` | `{"tag": "box", "child": ...}` | `\Box` | `NecessityOperator` | Yes |
| `untl` | `{"tag": "untl", "event": ..., "guard": ...}` | `U` (Until) | `UntilOperator` | Yes |
| `snce` | `{"tag": "snce", "event": ..., "guard": ...}` | `S` (Since) | `SinceOperator` | Yes |

**Critical Edge Case**: The JSON `imp` tag maps to `ConditionalOperator`, which is a **defined operator** (`→` = `¬A ∨ B`). During `update_types()`, defined operators are expanded via `derive_type()` into primitive equivalents. The formula translation layer must decide:

- **Option A**: Build the internal `Sentence` object using the `\rightarrow` string, let the existing `derive_type` expand it. This is the natural path.
- **Option B**: Pre-expand `imp` into `bot`/`neg`/`or` primitives at the JSON level. This is unnecessary — the existing machinery already handles derivation.

**Recommendation**: Option A. Use `\rightarrow` directly. The `DefinedOperator` mechanism is well-tested and handles the expansion. The translation layer should map JSON tags to the *canonical* internal operator names, not try to bypass the derivation system.

**Additional edge cases**:
- Derived operators (`¬`, `∧`, `∨`, `◇`, `F`, `P`, `G`, `H`, `↔`, `⊤`) don't appear in the JSON format. The JSON format only uses 6 primitive/near-primitive constructors.
- The JSON format uses different argument key names: `"left"/"right"` for `imp`, `"child"` for `box`, `"event"/"guard"` for `untl`/`snce`. The translation layer must map these to positional arguments.

### 2. Formula Translation: Bypass Infix Parsing Entirely

The existing `Sentence.__init__()` expects an **infix string** like `"(p \rightarrow q)"` and parses it through `prefix()` using tokenization. This is a string-to-prefix-list pipeline.

The JSON formulas are already in a structured tree representation. **Building an infix string just to re-parse it is wasteful and fragile** (introduces quoting/escaping issues). Instead, the translation should:

1. Recursively convert JSON tree → prefix list (e.g., `{"tag": "imp", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "q"}}` → `["\rightarrow", ["p"], ["q"]]`)
2. Construct `Sentence` objects directly from the prefix list, bypassing the infix parser

This requires either:
- A new `Sentence.from_prefix()` classmethod that accepts pre-built prefix lists, or
- Building the `Sentence` by setting `prefix_sentence` and `complexity` directly and calling `update_types()` / `update_objects()` / `update_proposition()` manually

The second approach is more invasive but avoids adding new constructors to existing code.

**Recommendation**: Create a `json_to_prefix(formula_json)` function that produces the internal prefix-list format, then a thin `Sentence.from_prefix(prefix_list)` classmethod that skips the infix parser. This keeps the translation cleanly separated from the existing parsing infrastructure.

### 3. Countermodel Extraction: Gap Between Internal and Required Formats

The `extract_model_elements()` method returns a 4-tuple:
```python
(world_histories, main_world_history, world_arrays, time_shift_relations)
```

Where:
- `world_histories`: `{world_id: {time: bitvec_state_string}}`
- `main_world_history`: `{time: bitvec_state_string}`
- `world_arrays`: `{world_id: z3_array_expr}`
- `time_shift_relations`: `{source_id: {shift: target_id}}`

The `SimpleCountermodel` format requires:
```python
{
    "trueAtoms": [{"base": "p"}, ...],
    "falseAtoms": [{"base": "q"}, ...],
    "formula": <original_formula_json>
}
```

**Gap Analysis**:
- `trueAtoms`/`falseAtoms` are not directly available from `extract_model_elements()`. These require evaluating each atom at the evaluation point (main_world, time=0) and checking truth/falsity. The `BimodalProposition.extension` attribute contains `{world_id: (true_times, false_times)}` per proposition — but this is computed *after* model solving and requires the full `BimodalStructure` pipeline to be run.
- The `StructuredCountermodel` format maps more naturally: `world_histories` → `world_histories`, `time_shift_relations` → `task_relation`, atom truth at various world/time points → `truth_valuation`.

**Missing piece**: The current pipeline evaluates formulas and their subformulas to get extensions. For `trueAtoms`/`falseAtoms`, we need to evaluate just the atomic propositions at the evaluation point. This requires:
1. Running the full `ModelConstraints` → `BimodalStructure` → `solve` pipeline
2. After solving, iterating over atoms and checking `is_true(z3_model.eval(semantics.true_at(atom_sentence, eval_point)))` for each atom

This is already essentially what `print_evaluation()` does, just formatted differently.

### 4. Frame Class Support: Only "Base" Currently Implemented

Searching the codebase for "Dense", "Discrete", or "frame_class" yielded zero hits in the semantic implementation. The bimodal theory implements a single frame class with:
- Integer time domain `(-M, M)`
- Convex world intervals
- Unit-duration task relations (lawful constraint)
- Skolem abundance (shift-closure)

This corresponds to the "Base" frame class. There is no infrastructure for "Dense" (real-valued time) or "Discrete" (additional discreteness axioms).

**Recommendation**: Declare `supported_frame_classes = frozenset({"Base"})` initially. The protocol docstring confirms "Only 'Base' is implementable today." This is not a gap — it's alignment.

### 5. Package Name: Must Be `bmlogic-oracle`

The BimodalHarness `pyproject.toml` already declares the optional dependency:
```toml
oracle = ["bmlogic-oracle>=0.1.0"]
```

The package name is **not a choice** — it must be `bmlogic-oracle` to match. The entry point must be:
```toml
[project.entry-points.'bimodal_harness.oracle_providers']
z3_base = "bmlogic_oracle.provider:Z3OracleProvider"
```

The import path would be `bmlogic_oracle` (underscores for Python module, hyphens for pip package name).

### 6. The Existing Pipeline is Heavy for Programmatic Use

The current model-checking pipeline goes through:
1. `ParseFileFlags` → parse example file
2. `BuildModule` → load theory, create syntax
3. `ModelConstraints` → build Z3 constraints
4. `BimodalStructure` → solve and extract model

This pipeline is designed for CLI usage with example files. For the OracleProvider's `find_countermodel()`, we need a much lighter path:
1. Accept JSON formula
2. Convert to internal representation
3. Set up Z3 constraints (reusing `BimodalSemantics`, `ModelConstraints`, `BimodalStructure`)
4. Solve with timeout
5. Extract and serialize countermodel

The key question is how much of `BuildModule` / `BuildExample` to reuse vs. bypass. The settings pipeline, example file parsing, and output formatting are all unnecessary for programmatic use.

**Recommendation**: Create a lightweight `CountermodelFinder` class that:
- Accepts a JSON formula and parameters (N, M, timeout)
- Directly instantiates `BimodalSemantics(N, M)` → `Syntax(operators)` → `Sentence.from_prefix(...)` → `ModelConstraints(...)` → `BimodalStructure(...)` → solve
- Skips all file I/O, settings parsing, and output formatting

### 7. The MockOracleProvider is a Complete Reference Implementation

The `_mock.py` file in BimodalHarness provides a comprehensive reference with:
- All 5 required properties (simple class attributes, not `@property` decorators)
- Both required methods
- 10 known-invalid spot-check formulas with countermodels
- The exact JSON tag structures with helper functions

The mock shows that properties can be plain class attributes (not `@property`). The `isinstance(obj, OracleProvider)` check uses `runtime_checkable` Protocol, which checks for method/property existence, not decoration style.

## Recommended Approach

### Task 102 (Formula JSON Translation) — Revisions Needed

The current description says "bidirectional conversion" and "round-trip fidelity." The reverse direction (sentence → JSON) is unnecessary for the OracleProvider interface (which only *receives* JSON formulas). Countermodel output includes the original `formula_json` passed in — it doesn't reconstruct JSON from internal representation.

**Revised scope**: One-directional `json_to_prefix()` function + `Sentence.from_prefix()` classmethod. Drop the reverse direction unless explicitly needed later.

### Task 103 (OracleProvider) — Merge Countermodel Serialization In

The countermodel serialization is tightly coupled to the OracleProvider implementation. The `find_countermodel()` method must:
1. Run the Z3 solving pipeline
2. Extract model elements
3. Evaluate atoms at eval point
4. Build the countermodel dict

These are not separable tasks. Merging makes sense.

### Task 104 (Programmatic API) — Reconsider Scope

The description talks about "clean public Python API surface" and "simplify CLI/output/builder." But for the OracleProvider use case, the package's public API *is* the OracleProvider class and the entry point. There's no need for a general-purpose Python API beyond that.

The CLI can be removed or vestigially retained for debugging. The builder/output/settings simplification is relevant but secondary to the OracleProvider implementation.

### Task 99 (Audit) and 100 (Strip) — Merge Recommended

Task 99 produces a report. Task 100 implements what the report says. These are tightly coupled. The audit can be done as the first phase of the stripping work rather than as a separate research task. The import chain analysis is done *during* removal, not as a separate study.

## Evidence/Examples

### Example: `find_countermodel` Implementation Sketch

```python
def find_countermodel(self, formula_json, frame_class="Base", timeout_ms=5000):
    if frame_class not in self.supported_frame_classes:
        return None
    
    prefix_list = json_to_prefix(formula_json)
    sentence = Sentence.from_prefix(prefix_list)
    
    # Set up semantics with default N, M
    semantics = BimodalSemantics(N=self._N, M=self._M)
    syntax = Syntax(self._operators, [sentence])
    constraints = ModelConstraints(semantics, syntax)
    structure = BimodalStructure(constraints)
    
    # Solve with timeout
    result = structure.solve(timeout_ms=timeout_ms)
    if result is None:  # UNSAT or timeout
        return None
    
    # Extract countermodel
    atoms = syntax.get_atoms()
    true_atoms = [a for a in atoms if is_true(result.eval(semantics.true_at(a, eval_point)))]
    false_atoms = [a for a in atoms if is_true(result.eval(semantics.false_at(a, eval_point)))]
    
    return {
        "trueAtoms": [{"base": a.name} for a in true_atoms],
        "falseAtoms": [{"base": a.name} for a in false_atoms],
        "formula": formula_json,
    }
```

### Example: `json_to_prefix` Mapping

```python
def json_to_prefix(formula_json):
    tag = formula_json["tag"]
    if tag == "atom":
        return [formula_json["name"]]
    elif tag == "bot":
        return ["\\bot"]
    elif tag == "imp":
        left = json_to_prefix(formula_json["left"])
        right = json_to_prefix(formula_json["right"])
        return ["\\rightarrow", left, right]
    elif tag == "box":
        child = json_to_prefix(formula_json["child"])
        return ["\\Box", child]
    elif tag == "untl":
        event = json_to_prefix(formula_json["event"])
        guard = json_to_prefix(formula_json["guard"])
        return ["U", event, guard]
    elif tag == "snce":
        event = json_to_prefix(formula_json["event"])
        guard = json_to_prefix(formula_json["guard"])
        return ["S", event, guard]
```

### Example: Entry Point Configuration

```toml
# In bmlogic-oracle's pyproject.toml
[project]
name = "bmlogic-oracle"
version = "0.1.0"
dependencies = ["z3-solver>=4.8.0"]

[project.entry-points.'bimodal_harness.oracle_providers']
z3_base = "bmlogic_oracle.provider:Z3OracleProvider"
```

## Confidence Level

- **Operator mapping**: **High** — Directly verified JSON tags against operator class names and `bimodal_operators` collection.
- **Formula translation approach**: **High** — The `Sentence.from_prefix()` approach is clean and avoids parser fragility.
- **Countermodel serialization gap**: **High** — The `trueAtoms`/`falseAtoms` extraction is not currently exposed but the Z3 evaluation machinery is there.
- **Frame class support**: **High** — Only "Base" exists; protocol confirms this is expected.
- **Package naming**: **High** — Directly verified in BimodalHarness `pyproject.toml`.
- **Task restructuring recommendations**: **Medium** — Merging tasks 99/100 and revising 102 scope are judgment calls that depend on team preference for granularity vs. efficiency.
