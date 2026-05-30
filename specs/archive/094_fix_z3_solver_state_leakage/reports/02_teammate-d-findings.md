# Teammate D Findings: Strategic Horizons for Z3 Solver State Leakage Fix

- **Task**: 94 - fix_z3_solver_state_leakage
- **Teammate**: D (Horizons)
- **Focus**: Long-term alignment, architectural opportunities, hybrid approach analysis

---

## Key Findings

1. **The codebase already has extensive isolation infrastructure, but it all relies on an ineffective reset mechanism.** There are at least 5 call sites that attempt to reset Z3 state before each example (`ModelRunner._initialize_z3_context`, `ModelDefaults.__init__`, `BuildExample._initialize_z3_context`, `SemanticDefaults._reset_global_state`, `BimodalStructure.__init__`), yet none achieve true isolation because `reset_z3_context()` calls `importlib.reload(z3)` which does not reset the underlying C library.

2. **The Z3 maintainers explicitly recommend creating a fresh `Solver()` per query from Python, and explicitly warn against `Z3_reset_memory()` from managed interfaces.** See the Z3 GitHub discussion (https://github.com/Z3Prover/z3/discussions/4992): "Resetting memory from managed interfaces, e.g., Python, Java, C#, OCaml, is not practical because of interactions with GC and global objects." For Python: simply create a fresh `Solver()` per problem.

3. **The fix scope is large but concentrated.** There are approximately 295 Z3 API call sites across the codebase that do not pass an explicit `ctx=` parameter. However, the actual object construction that propagates the global context is concentrated in just two files: `code/src/model_checker/theory_lib/logos/semantic.py` (21 calls) and `code/src/model_checker/theory_lib/bimodal/semantic.py` (20 calls). These files contain `z3.Function(...)`, `z3.BitVec(...)`, and `z3.BitVecSort(...)` calls that build the primitive relations and evaluation framework for the entire theory.

4. **The existing `Z3SolverAdapter` already creates a fresh `z3.Solver()` on each instantiation** (line 25 in `z3_adapter.py`). The real state leakage is in the Z3 global context cache for named declarations (functions like `verify`, `falsify`, `possible`, `task_rel`, `world_function`, `is_world`). When two examples define a Z3 function called `verify` with the same signature, Z3 silently reuses the same declaration. The solver cache then carries learned knowledge about that function across examples.

5. **Explicit `z3.Context()` per example is verified to work correctly.** Local experiments confirm that `z3.Function('verify', sort1, sort2)` in separate `z3.Context()` instances returns independent function declarations with no shared state.

6. **There is no `ROADMAP.md` in the specs directory**, so alignment analysis is relative to the existing task history and codebase trajectory.

---

## Theory Landscape Survey

### Two top-level theories

The project has exactly two implemented theories with distinct semantic files:

| Theory | Semantics Class | Model Structure Class | Location |
|--------|----------------|----------------------|----------|
| Logos | `LogosSemantics(SemanticDefaults)` | `LogosModelStructure(ModelDefaults)` | `theory_lib/logos/semantic.py` |
| Bimodal | `BimodalSemantics(SemanticDefaults)` | `BimodalStructure(ModelDefaults)` | `theory_lib/bimodal/semantic.py` |

### Logos subtheories

Logos is further divided into 7 subtheories: `extensional`, `modal`, `constitutive`, `counterfactual`, `relevance`, `spatial`, `first_order`. These are **not** independent theories -- they share `LogosSemantics` as a common base and contribute only operators/examples. They do **not** independently construct Z3 primitives.

### How theories use Z3 globally

Both theories follow the same pattern in their `__init__`:
1. Call `super().__init__(settings)` which calls `SemanticDefaults.__init__`
2. Call `define_sorts()` or directly create `z3.BitVecSort(N)` -- **no ctx= parameter**
3. Call `define_primitives()` or directly create `z3.Function(name, ...)` -- **no ctx= parameter**
4. Build `frame_constraints` as a list of Z3 expressions -- **no ctx= parameter**

The Z3 expressions at steps 2-4 are all bound to the global implicit context. This is the root cause: when a second example runs, a new `LogosSemantics` or `BimodalSemantics` instance is created, but `z3.Function("verify", ...)` returns the same C-level function declaration object as before, now carrying internal solver state.

### Inheritance chain

```
SemanticDefaults  (models/semantic.py)
  |-- _reset_global_state()  # base, resets _cached_values only
  |-- LogosSemantics          # creates verify, falsify, possible, main_world
  |-- BimodalSemantics        # creates task_rel, world_function, is_world, truth_condition
```

Both call `super().__init__()` first, meaning `SemanticDefaults._reset_global_state()` is always invoked -- but it only clears `_cached_values`, not Z3 function declarations.

### Z3 call site distribution (no ctx= parameter)

| Module | Count | Key constructs |
|--------|-------|----------------|
| `theory_lib/logos/semantic.py` | 21 | `z3.Function`, `z3.BitVecSort`, `z3.BitVec`, `z3.Bool` |
| `theory_lib/bimodal/semantic.py` | 20 | Same plus `z3.IntSort`, `z3.ArraySort`, `z3.Function` |
| `iterate/` package | 48 | Constraint manipulation |
| `utils/` package | 28 | Helper functions |
| `solver/` package | 22 | Adapter internals |

The `iterate/`, `utils/`, and `solver/` calls operate on existing Z3 expressions (passed in), not constructing new named declarations from scratch. The semantic files are the true origin point.

---

## Architectural Opportunities

### Opportunity 1: ExampleContext abstraction

The codebase already has the concept of per-example isolation scattered across 5 call sites. These could be consolidated into a single `ExampleContext` object that:

- Holds a `z3.Context()` instance
- Serves as the factory for all Z3 expression construction within one example
- Has a clear lifecycle: created before semantics construction, destroyed after model extraction
- Is passed down through `SemanticDefaults.__init__` via `settings` or a dedicated parameter

This would make the isolation boundary explicit and architectural rather than implicit and procedural. The `Z3SolverAdapter` would accept `ctx=example_context.ctx` instead of using the default.

### Opportunity 2: Context-aware SemanticDefaults

`SemanticDefaults.__init__` is the natural place to receive a `z3.Context`. Adding an optional `ctx=None` parameter that defaults to `z3.main_ctx()` would:

- Provide full backward compatibility
- Allow per-example isolation via `ctx=z3.Context()`
- Propagate the context to all child constructions in `LogosSemantics` and `BimodalSemantics`

This is a single-point change with high leverage. All 41 Z3 construction calls in the two theory semantic files would need updating, but the logic would remain identical.

### Opportunity 3: Solver-layer context injection

The existing `Z3SolverAdapter` creates a `z3.Solver()` with the implicit context. Extending `create_solver(settings)` to accept an optional `ctx` argument would allow the solver to share the same context as the semantic objects. This ensures model evaluation (`model.evaluate(expr)`) works correctly, since Z3 requires the model and expression to share a context.

### Opportunity 4: Enabling parallel example processing

If each example gets its own `z3.Context()`, examples can safely run in separate Python threads (Z3's documentation explicitly states cross-context thread safety). This is currently not possible with the shared global context. This is a significant future capability for performance.

The current `ModelRunner.run_examples()` already has a `try_single_N_static` path using `ProcessPoolExecutor` that serializes theories -- suggesting the codebase has already explored parallelism. With explicit contexts, a thread-pool approach becomes viable without the serialization overhead.

### Opportunity 5: Cleanup of dead isolation code

The current `reset_z3_context()` / `reset_solver_context()` infrastructure in `utils/context.py`, the `Z3ContextManager` class, and the 5 scattered call sites could all be removed once explicit context-per-example is established. This would reduce code complexity significantly.

---

## Hybrid Approach Analysis

The research report (01_z3-state-leakage.md) identified four options: process isolation (A), explicit contexts (B), `Z3_reset_memory()` (C), and increased timeouts (D).

### Option A (subprocess/multiprocessing) analysis

**Strengths**: Guaranteed complete isolation regardless of Z3 internals. No Z3 API threading constraints. Each example is a clean OS process.

**Weaknesses for this codebase**:
- The `try_single_N_static()` function already explored this path -- it requires serializing the entire semantic theory (class objects, Z3 function declarations, etc.) across process boundaries. The codebase already has a `serialize.py` module for this.
- UX impact: The `UnifiedProgress` / `Spinner` objects use terminal control codes and `time.monotonic()`. These would need IPC or cannot be trivially passed to subprocesses.
- `_run_generator_iteration()` relies on yielding model structures incrementally -- this becomes complex with process isolation.
- Interactive mode (`prompt_for_iterations`) would be impossible inside subprocesses.

**Verdict**: Process isolation is valuable as a testing/CI mode but is not suitable as the primary fix for the normal interactive execution path.

### Option B (explicit contexts) analysis

**Strengths for this codebase**:
- Z3's intended mechanism for isolation
- Thread-safe across contexts
- No serialization overhead
- Compatible with the existing `Spinner` / `UnifiedProgress` UX
- Compatible with the generator iteration interface
- Enables future parallel processing

**Weaknesses**:
- Requires threading `ctx` through constructors. Count: approximately 41 changes in `logos/semantic.py` and `bimodal/semantic.py`, plus 48 in the `iterate/` package that operate on existing expressions (these may not need changes if expressions already carry context).
- `z3.BitVec`, `z3.Function`, `z3.BitVecSort` all have `ctx=` parameters already -- no API extension needed.
- Model evaluation: `z3_model.evaluate(expr)` requires model and expression to be in the same context. This is automatically satisfied if both the solver and semantic expressions share `ctx`.

**Verdict**: Correct and maintainable. The effort is contained and mechanical.

### Hybrid: Option B primary + Option A for CI/testing

A hybrid approach is strategically sound:

1. **Normal execution**: Explicit `z3.Context()` per example (Option B). Clean, fast, no UX changes.

2. **Test suite / CI mode**: An optional `--isolated` or `--subprocess` flag that runs each example in a separate subprocess via `multiprocessing`. This provides belt-and-suspenders isolation for test suites where nondeterminism is particularly harmful.

3. **Configuration knob**: A `solver_isolation` setting in `DEFAULT_GENERAL_SETTINGS` with values `"context"` (default, Option B) and `"subprocess"` (Option A). The `ModelRunner.run_examples()` loop could dispatch accordingly.

This gives:
- Correctness as the default
- Maximal isolation for CI
- A clear migration path (start with context isolation, add subprocess mode later if needed)

### Why Option C (`Z3_reset_memory()`) should not be used

Confirmed by Z3 maintainers (GitHub discussion #4992): calling `Z3_reset_memory()` from Python causes segmentation faults due to interactions with Python's GC and global objects. The existing codebase does not use it, and it should be permanently ruled out.

---

## Strategic Recommendations

### Recommendation 1: Explicit Z3 context per example (Option B) as the primary fix

Implement `z3.Context()` per example, threaded through `SemanticDefaults.__init__`. This is the architecturally correct approach, aligns with Z3 maintainer guidance, and enables future parallel processing.

**Minimal viable scope**: Add `ctx: Optional[z3.Context] = None` to `SemanticDefaults.__init__`. Propagate to `LogosSemantics` and `BimodalSemantics`. Update the ~41 Z3 construction calls in those two files. Update `Z3SolverAdapter` to accept `ctx=`. Update `create_solver()` to forward context.

**Boundary condition**: Z3 requires that a model and its expressions share a context. The `z3_model.evaluate(expr)` calls in `LogosModelStructure.__init__` and `BimodalStructure.__init__` are safe only if `self.z3_model` was produced by a solver sharing the same context as `self.semantics`.

### Recommendation 2: Centralize context creation in BuildExample

`BuildExample.__init__` is the per-example entry point. Creating the `z3.Context()` there and passing it into `semantics_class(settings, ctx=ctx)` is cleaner than creating it inside the solver or the semantic object. This makes the context lifecycle explicit: created when the example starts, used throughout, garbage-collected when the example object is released.

### Recommendation 3: Remove the dead reset infrastructure after the fix

Once Option B is implemented, `reset_z3_context()`, `reset_solver_context()`, `Z3ContextManager`, `z3.reset_params()`, and the scattered `gc.collect()` calls added to approximate isolation should all be removed. These are compensatory measures for the missing real fix, and leaving them creates confusion about the actual isolation mechanism.

### Recommendation 4: Do not implement Option A as the primary fix

Process isolation adds complexity to the UX layer (progress bars, interactive iteration), complicates the generator interface, and adds serialization overhead. It is only appropriate as a secondary mode for CI or benchmarking.

### Recommendation 5: Add a context verification test

Add a test that runs `BM_CM_3` and `BM_CM_1` in isolation and in combination (as described in report 01) and asserts deterministic results. This test is currently impossible to pass; passing it after the fix provides regression coverage.

---

## Confidence Level

**High** for the architectural diagnosis. The Z3 maintainer guidance is explicit and the codebase structure is clearly analyzed. The ~41 call site count in the two semantic files is precise (21 in logos/semantic.py, 20 in bimodal/semantic.py, confirmed by grep). The recommendation to use explicit `z3.Context()` per example aligns with both the Z3 API design and the maintainer-documented best practice.

**Medium** for the hybrid approach details. The exact interface for `create_solver(ctx=...)` and how context threading interacts with the `iterate/` package (48 call sites) requires implementation-level exploration to determine whether those sites need updating or whether they receive context implicitly through passed Z3 expressions.

**Medium** for the parallel processing future capability. The thread-safety claim for cross-context operations is documented by Z3, but the practical benefit for this codebase depends on profiling and workload characteristics not yet measured.

---

## References

- `code/src/model_checker/utils/context.py` - dead reset infrastructure
- `code/src/model_checker/models/structure.py` - solver creation and reset call
- `code/src/model_checker/builder/example.py` - per-example entry point
- `code/src/model_checker/builder/runner.py` - `run_examples()` loop and reset calls
- `code/src/model_checker/models/semantic.py` - `SemanticDefaults` base class
- `code/src/model_checker/theory_lib/logos/semantic.py` - `LogosSemantics` (21 Z3 calls)
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - `BimodalSemantics` (20 Z3 calls)
- `code/src/model_checker/solver/z3_adapter.py` - `Z3SolverAdapter`
- `code/src/model_checker/solver/registry.py` - `create_solver()`
- Z3 GitHub discussion: https://github.com/Z3Prover/z3/discussions/4992 (reset() vs new Solver)
- Z3 GitHub issue: https://github.com/Z3Prover/z3/issues/7525 (nondeterministic behavior despite seed)
