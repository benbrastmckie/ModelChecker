# Teammate A Findings: Task Decomposition and Ordering Review

**Task**: 106 — Architecture review of bimodal refactor plan (tasks 99-105)
**Angle**: Primary — task decomposition optimality
**Date**: 2026-05-30

## Key Findings

### 1. Task 99 (Audit) Should Be Merged Into Task 100 (Strip)

Task 99 is a pure research task producing a report. But the audit it proposes — file-by-file keep/modify/remove classifications — is exactly the work task 100 needs to do anyway before deleting anything. Having a separate research-only audit task creates a handoff overhead where the implementer of task 100 must re-read and re-verify the audit findings against the live codebase.

**Recommendation**: Merge task 99 into task 100 as its research phase. The research report becomes the implementation plan for task 100. The operator alignment analysis (mapping 6-tag JSON to internal operators) should move to task 102, where it directly informs the translation layer implementation.

**Confidence**: High

### 2. Task 103 Is Too Large and Conflates Two Concerns

Task 103 combines OracleProvider protocol implementation with countermodel serialization. These are architecturally distinct:

- **Countermodel serialization** transforms the output of `BimodalStructure.extract_model_elements()` — which returns `(world_histories, main_world_history, world_arrays, time_shift_relations)` tuples — into the `SimpleCountermodel.toJson` and `StructuredCountermodel` JSON formats. This is a data transformation task that can be tested independently.

- **OracleProvider implementation** orchestrates the full pipeline: receive formula JSON → translate to Sentence → create Syntax/ModelConstraints/BimodalSemantics/BimodalStructure → solve → extract model → serialize to JSON. This wraps existing machinery with the protocol interface.

**Recommendation**: Split task 103 into:
- 103a: Countermodel serialization (depends on 100 only — it works with existing `extract_model_elements()`)
- 103b: OracleProvider protocol implementation (depends on 101, 102, 103a)

**Confidence**: High

### 3. Task 104 (Programmatic API Cleanup) Has a Problematic Dependency

Task 104 depends only on task 100 and is described as being about simplifying builder/output/CLI. But these modules are needed by the OracleProvider pipeline (task 103). If task 104 runs before or in parallel with task 103, the refactored internals might not match what task 103 expects.

**Evidence**: The model checking pipeline flows through:
```
BuildModule → runner.run_examples() → ModelConstraints → ModelDefaults.solve()
```
The `builder/runner.py` imports from `output/progress.py`, `syntactic`, and `builder/serialize.py`. If task 104 simplifies these, task 103's implementation may target interfaces that no longer exist.

**Recommendation**: Task 104 should depend on task 103 (not just task 100). The OracleProvider should be built first against the existing internal API, then task 104 can simplify the internals while maintaining the OracleProvider as the primary public interface. The dependency chain becomes: 100 → {101, 102, 103a} → 103b → 104 → 105.

**Confidence**: High

### 4. The Dependency Between 101 (Pip Package) and 103 (OracleProvider) Is Correct but Could Be Loosened

Task 101 restructures pyproject.toml and adds entry points. Task 103 implements the OracleProvider class. The entry point in pyproject.toml points to the class that task 103 creates. So there's a circular dependency in practice — you can't fully test the entry point until the class exists.

However, task 101 can stub the entry point initially (pointing to a placeholder class) and finalize it when task 103 is done.

**Recommendation**: Allow tasks 101 and 102 to proceed in parallel after task 100, with task 103 finalizing the entry point registration. The pyproject.toml restructuring (package name, dependencies, package-dir) is independent of the OracleProvider class.

**Confidence**: Medium

### 5. The Formula Translation Layer (Task 102) Has Clear Scope but Missing Edge Cases

The 6-tag JSON format maps cleanly to ModelChecker primitives:
- `atom` → sentence letter (AtomSort/AtomVal)
- `bot` → `⊥` (BotOperator)
- `imp` → `→` (ConditionalOperator, which is a DefinedOperator in bimodal, defined via ¬ and ∨)
- `box` → `□` (NecessityOperator)
- `untl` → `U` (UntilOperator)
- `snce` → `S` (SinceOperator)

**Critical observation**: In the current ModelChecker, `→` (ConditionalOperator) is a `DefinedOperator` — it's defined as `¬(A ∧ ¬B)`, not a primitive. But in the BimodalHarness JSON, `imp` IS a primitive constructor. The translation layer must construct the internal representation correctly — mapping `imp` either to the DefinedOperator (if keeping the existing system) or making `→` primitive in the refactored bimodal-only version.

Similarly, `bot` in the JSON corresponds to `BotOperator` (primitive in bimodal), but the Sentence class constructs from infix strings, not from operator objects directly. Task 102 needs to build Sentence objects programmatically, bypassing the infix parser entirely. The current Sentence constructor (`__init__`) takes an `infix_sentence` string and parses it — there's no constructor from AST nodes.

**Recommendation**: Task 102's scope should explicitly include creating a programmatic Sentence constructor (or factory function) that builds Sentence trees from JSON without going through infix string parsing. This is a meaningful code change, not just a translation function.

**Confidence**: High

### 6. Integration Testing (Task 105) Is Correctly Scoped

Task 105 depends on tasks 103 and 104, which makes sense as the terminal testing task. Its scope — protocol compliance, countermodel correctness, BimodalHarness compatibility — is appropriate.

**One addition**: Task 105 should also include regression testing against the existing 43-example bimodal test suite to verify that the refactored package produces identical results. This is mentioned in task 100 but should be a continuous gate at each task, not just checked once.

**Confidence**: High

## Recommended Approach

### Revised Task Structure

1. **Task 100** (merged 99+100): Strip non-bimodal code with embedded audit
   - Research phase: file-by-file audit → removal plan
   - Implementation: execute removals, verify 43-test suite still passes

2. **Task 101**: Restructure as pip package (parallel with 102, 103a after 100)
   - Update pyproject.toml, package identity, dependencies
   - Stub entry point for later finalization

3. **Task 102**: Formula JSON translation layer (parallel with 101, 103a after 100)
   - Create programmatic Sentence factory from JSON AST
   - Map 6-tag JSON to internal operator/sentence structure
   - Include operator alignment analysis (moved from old task 99)

4. **Task 103a** (new): Countermodel serialization (after 100)
   - Transform extract_model_elements() output to SimpleCountermodel/StructuredCountermodel JSON
   - Independently testable

5. **Task 103b** (renamed from 103): OracleProvider implementation (after 101, 102, 103a)
   - Protocol class with find_countermodel, validate_self
   - Full pipeline integration
   - Finalize entry point in pyproject.toml

6. **Task 104**: Programmatic API cleanup (after 103b)
   - Simplify builder/output/CLI
   - OracleProvider is now the primary public interface

7. **Task 105**: Integration testing (after 104)
   - Protocol compliance, regression, BimodalHarness compatibility

### Revised Dependency Graph

```
100 (strip+audit)
 ├── 101 (pip package)     ──┐
 ├── 102 (JSON translation) ─┼── 103b (OracleProvider) → 104 (cleanup) → 105 (testing)
 └── 103a (serialization)  ──┘
```

## Evidence/Examples

- `theory_lib/__init__.py` (line 52) has `from model_checker.theory_lib import logos` as a hard import — this will break immediately on logos removal, confirming task 100 needs careful import tracing
- `ConditionalOperator` in operators.py is a `DefinedOperator` (line ~200), meaning `imp` JSON tag doesn't map to a primitive — translation is non-trivial
- `Sentence.__init__` (sentence.py line 49) only accepts infix strings — no AST constructor exists
- `extract_model_elements` (semantic.py line 1587) returns 4-tuples, not JSON — serialization is a real task

## Confidence Level

**Overall**: High — based on detailed code reading of all relevant modules, the OracleProvider protocol, and the existing model checking pipeline. The main risk areas are the formula translation (lack of AST constructor) and the dependency ordering between cleanup and OracleProvider implementation.
