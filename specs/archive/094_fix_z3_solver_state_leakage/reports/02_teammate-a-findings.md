# Teammate A Findings: Option A (Process-Level Isolation) Design

- **Task**: 94 - fix_z3_solver_state_leakage
- **Focus**: Option A - process-level isolation via multiprocessing
- **Report**: 02_teammate-a-findings.md

---

## Key Findings

1. **Z3 objects cannot be pickled**: `z3.Solver`, `z3.ModelRef`, `z3.ExprRef`, and `z3.BitVecNumRef` all fail with `ValueError: ctypes objects containing pointers cannot be pickled`. This is fundamental to the Option A design: Z3 objects can never cross the process boundary.

2. **`Z3_reset_memory()` causes segfaults**: Testing confirmed that `z3.Z3_reset_memory()` called after any Z3 use (even with all references deleted and GC collected) causes a segmentation fault. Option C is not just fragile - it is actively dangerous in Python 3.12 / Z3 4.16.0. This validates that Option A (process isolation) and Option B (explicit contexts) are the only safe paths forward.

3. **The project already has working subprocess infrastructure**: `builder/comparison.py` uses `ProcessPoolExecutor` with serialized theory configs, and `builder/runner.py` has `try_single_N_static()` - a module-level function that reconstructs theories from serialized data and uses a `MockBuildModule` pattern. Option A can leverage this exact infrastructure.

4. **Subprocess overhead is ~0.12-0.15s per example** (fork-based): Using `multiprocessing` with fork start method (Unix default), per-example subprocess overhead is approximately 120-150ms since the child process inherits the parent's already-loaded Python environment. For examples that currently take 5+ seconds due to Z3 state, this is negligible.

5. **`serialize_semantic_theory` / `deserialize_semantic_theory` already handles all theory serialization**: These functions in `builder/serialize.py` convert theory dicts with Python class objects into plain dicts of module/class names and back. All inputs to the subprocess worker can be pickled.

---

## Iterator/Processing Pattern Analysis

### The Main Loop

`ModelRunner.run_examples()` (runner.py:733) is the entry point:

```
run_examples()
  for example_name, example_case in build_module.example_range.items():
    for theory_name, semantic_theory in build_module.semantic_theories.items():
      process_example(example_name, example_copy, theory_name, semantic_theory)
```

`process_example()` (runner.py:273) branches on `iterate_count`:
- `iterate_count == 1`: calls `_process_single_model()` -> `BuildExample()` -> `_capture_and_save_output()`
- `iterate_count > 1`: calls `_process_with_iterations()` which uses `ModelIterator` for MODEL 2, 3, ...

### The Data Flow for a Single Example

```
Input (all picklable):
  example_case = [premises: List[str], conclusions: List[str], settings: dict]
  theory_name = str
  semantic_theory = {semantics: class, proposition: class, model: class, operators: OperatorCollection}

Processing (requires Z3, NOT picklable):
  BuildExample.__init__() -> ModelDefaults.__init__() -> solve() -> z3.Solver.check()
  -> z3_model: z3.ModelRef (C pointer, lives in subprocess's Z3 C library)

Output needed by parent (all picklable):
  output_text: str  (captured stdout of print_to())
  model_found: bool (z3_model_status)
  runtime: float    (z3_model_runtime)
  timeout: bool
  check_result: bool (model_found == settings['expectation'])
```

### The Iteration Pattern

For `iterate > 1`, `_process_with_iterations()` calls theory-specific `iterate_example_generator()` functions. These functions internally use `ModelIterator` which:
1. Takes the initial `BuildExample` (has `z3_model`)
2. Creates additional solvers with "difference constraints" excluding previous models
3. Yields new `model_structure` objects with their own `z3_model`

Since each iteration result also requires `z3_model.eval()` for display, the ENTIRE iteration sequence must happen inside the subprocess. The subprocess must return `output_text` covering ALL models in the iteration.

### What `build_module` Is Used For Inside the Worker

`BuildExample.__init__()` uses `build_module` for:
- `build_module.semantic_theories` - to check `len() > 1` for `is_comparison`
- `build_module.general_settings` - merged settings
- `build_module.raw_general_settings` - for `SettingsManager`
- `build_module.module_flags` - CLI flags

`_capture_and_save_output()` uses `build_module.output_manager` - this is NOT needed in the subprocess (the parent handles output saving using the returned `output_text` string).

---

## Option A Design Proposal

### Process Boundary Location

The process boundary should sit at `ModelRunner.process_example()`. The parent process:
1. Serializes inputs (already picklable)
2. Spawns subprocess
3. Receives `{output_text, model_found, runtime, timeout, check_result}`
4. Prints/saves `output_text`

The subprocess:
1. Deserializes theory from `theory_config`
2. Constructs `MinimalMockModule` (a simple struct, no `OutputManager`)
3. Creates `BuildExample` using `MinimalMockModule`
4. Handles iterations (all Z3 model printing happens here)
5. Returns the result dict

### Minimal API Surface

```python
# In builder/runner.py (module-level, picklable)
def run_example_isolated(
    theory_config: Dict[str, Any],   # serialize_semantic_theory() output
    example_case: List[Any],          # [premises, conclusions, settings]
    example_name: str,
    theory_name: str,
    iterate_count: int,
    module_flags_dict: Dict[str, Any]  # vars(module_flags), plain dict
) -> Dict[str, Any]:
    """
    Returns:
        {
            'output_text': str,      # captured stdout from print_to()
            'model_found': bool,
            'runtime': float,
            'timeout': bool,
            'check_result': bool
        }
    """
    from model_checker.builder.serialize import deserialize_semantic_theory
    from model_checker.builder.example import BuildExample
    import io, sys
    
    semantic_theory = deserialize_semantic_theory(theory_config)
    
    class MinimalMockModule:
        def __init__(self):
            self.semantic_theories = {theory_name: semantic_theory}
            self.general_settings = example_case[2]
            self.raw_general_settings = example_case[2]
            self.module_flags = type('flags', (), module_flags_dict)()
            self.module = type('mod', (), {'__name__': 'mock'})()
        def _capture_and_save_output(self, example, ex_name, th_name, model_num=None):
            example.print_model(ex_name, th_name)
    
    mock = MinimalMockModule()
    captured = io.StringIO()
    sys.stdout = captured
    try:
        example = BuildExample(mock, semantic_theory, example_case, theory_name)
        if iterate_count > 1:
            # Handle iterations - all inside subprocess
            ...
        else:
            example.print_model(example_name, theory_name)
    finally:
        sys.stdout = sys.__stdout__
    
    return {
        'output_text': captured.getvalue(),
        'model_found': example.model_structure.z3_model_status,
        'runtime': example.model_structure.z3_model_runtime,
        'timeout': example.model_structure.timeout,
        'check_result': example.check_result()
    }
```

### Integration Point in `process_example()`

The modified `process_example()` would replace the direct `BuildExample` call:

```python
def process_example(self, example_name, example_case, theory_name, semantic_theory):
    from concurrent.futures import ProcessPoolExecutor
    from .serialize import serialize_semantic_theory
    
    theory_config = serialize_semantic_theory(theory_name, semantic_theory)
    iterate_count = self._get_iterate_count(example_case)
    flags_dict = vars(self.build_module.module_flags)
    
    with ProcessPoolExecutor(max_workers=1) as executor:
        future = executor.submit(
            run_example_isolated,
            theory_config, example_case, example_name, theory_name,
            iterate_count, flags_dict
        )
        result = future.result(timeout=example_case[2].get('max_time', 5) + 5)
    
    # Print the captured output in parent process
    print(result['output_text'], end='')
    
    # Route to output_manager if saving
    if self.build_module.output_manager.should_save():
        self.build_module.output_manager.save_example(
            example_name, {'model_found': result['model_found']}, result['output_text']
        )
```

### Handling the Progress Bar

The current progress bar (spinner, `UnifiedProgress`) is output by the parent process before/after the solve. With subprocess isolation, the parent can still:
1. Start the spinner before submitting the subprocess future
2. Stop the spinner when `future.result()` returns
3. Print the `output_text` from the result

This requires no changes to the progress bar logic.

---

## Risks and Concerns

### Risk 1: Iteration Complexity (HIGH)

The iteration pattern (`_process_with_iterations`, `_run_generator_iteration`) is tightly coupled to the parent runner's output loop. Generator-based iteration yields individual model structures incrementally - each yield needs `z3_model` to print. All of this must happen inside the subprocess.

The subprocess must run the ENTIRE `_process_with_iterations` equivalent internally. This means duplicating or refactoring approximately 250 lines of `runner.py` iteration logic into the static worker function.

**Mitigation**: The subprocess can call `ModelRunner._process_with_iterations()` directly if we initialize a `MinimalMockModule` with the runner. Or we can use `example.find_next_model()` in a loop.

### Risk 2: Interactive Mode Breakage (MEDIUM)

The `--sequential` / `prompt_manager` path queries the user between models. If iterations happen inside the subprocess, there is no way to prompt the user mid-execution. Interactive mode would need to either:
- Disable subprocess isolation (fall back to in-process)
- Change to ask "how many models?" before the subprocess runs

The current `_handle_iteration_mode()` already has this pattern: it prompts for `user_iterations` count before starting the actual iteration loop. The subprocess can take `iterate_count` as an input, which can include the user's response.

### Risk 3: fork() + Z3 Safety (LOW)

On Linux, `multiprocessing` defaults to `fork`. The Z3 C library is already initialized in the parent at fork time. In theory, forked Z3 state could cause issues - but in practice, after forking, the subprocess creates a completely fresh `z3.Solver()`, and the inherited state is never used. The comparison mode already uses `ProcessPoolExecutor` (which uses fork by default on Linux) without issues.

### Risk 4: Timeout Architecture Change (LOW)

Currently, Z3 solver timeout is set via `solver.set_timeout()` inside the subprocess. The subprocess outer timeout (passed to `future.result(timeout=...)`) provides a safety net. This is actually cleaner than the current architecture.

### Risk 5: Output Capture Differences (LOW)

Some theory printing code uses `sys.__stdout__` (the original stdout) rather than `sys.stdout`. After redirecting `sys.stdout` in the subprocess, calls to `sys.__stdout__` would escape capture. A check of `bimodal/semantic.py` shows `print(..., file=sys.__stdout__)` is used only as a fallback default argument (`output=sys.__stdout__`). Since `print_to()` is called with an explicit `output` parameter, this is not an issue.

### Risk 6: ANSI Color Code Handling (NEGLIGIBLE)

Currently, `_capture_and_save_output()` in `module.py` captures stdout, strips ANSI codes for markdown saving, then prints the raw (colored) version to terminal. With subprocess isolation, the subprocess output_text will contain ANSI codes. The parent just needs to print it as-is (terminal) and strip codes for saving. This is the same logic, just applied to a string instead of a live capture.

---

## Concrete Implementation Scope

Estimated changes required for Option A:

1. **New module-level function** `run_example_isolated()` in `runner.py` (~50 lines): The subprocess worker. Handles single and iterated examples. Captures stdout. Returns plain dict.

2. **Modify `ModelRunner.process_example()`** (~30 lines changed): Replace direct `BuildExample` call with `ProcessPoolExecutor.submit(run_example_isolated, ...)`. Add result routing.

3. **Modify `ModelRunner.run_examples()`** (~5 lines): Remove the manual `z3._main_ctx = None` reset (now handled by process isolation). Remove the `reset_z3_context()` calls (no longer needed).

4. **`MinimalMockModule` class** in the worker (~20 lines): Minimal struct to satisfy `BuildExample.__init__()` without needing `OutputManager`, `SequentialSaveManager`, etc.

5. **Iteration handling in subprocess** (~30 lines): Run `_process_with_iterations` equivalent or a simpler loop using `find_next_model()`.

Total: ~135 lines of new/changed code. The key existing infrastructure (`serialize_semantic_theory`, `try_single_N_static` pattern) is already in place.

---

## Confidence Level

**HIGH** for the core design:
- Z3 C objects cannot pickle (confirmed empirically)
- `ProcessPoolExecutor` with serialized theory configs already works (used in `comparison.py`)
- The `try_single_N_static` pattern in `runner.py` proves the MockBuildModule approach is viable
- subprocess overhead (~0.15s) is acceptable relative to typical Z3 solve times
- All subprocess inputs are picklable (confirmed empirically)

**MEDIUM** for iteration complexity:
- The iteration path (`_process_with_iterations`, generator interface) is more complex
- The subprocess must replicate or reuse ~250 lines of iteration logic
- Testing would be needed to confirm all edge cases (generator vs list iteration, deferred progress bar completion pattern)

**HIGH** that Option A would fully solve the problem:
- Each example runs in its own process with a completely fresh C library instance
- No amount of Z3 internal state can leak between processes
- This is the only approach that provides categorical isolation guarantees
