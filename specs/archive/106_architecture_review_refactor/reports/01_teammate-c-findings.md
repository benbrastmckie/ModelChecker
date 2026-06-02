# Teammate C (Critic): Gaps and Blind Spots in Bimodal Refactor Plan

## Key Findings

### 1. CRITICAL: Hard Logos Import Will Break Immediately (Confidence: HIGH)

`theory_lib/__init__.py` line 52 has `from model_checker.theory_lib import logos` — a **non-lazy, unconditional import**. This means the moment the logos directory is deleted (Task 100), importing `theory_lib` will crash the entire package. This is not a lazy load via `__getattr__`; it's a top-level import.

Additionally, `builder/example.py` line 34 has `from ..theory_lib.logos import semantic` — another hard logos dependency in core builder infrastructure. Although it appears unused after import (no `semantic.` attribute accesses found via AST analysis), it will still crash on import.

**Impact on plan**: Task 100 (strip non-bimodal code) cannot simply delete logos/. It must first fix these hard imports. Tasks 99 and 100 need to be merged or Task 99 must produce an exhaustive import-chain map that Task 100 follows exactly.

### 2. CRITICAL: Builder Module Has Logos-Specific Branching (Confidence: HIGH)

`builder/runner.py` lines 82 and 206 contain:
```python
if 'Logos' in semantics_class.__name__:
    semantics = semantics_class(combined_settings=settings)
else:
    semantics = semantics_class(settings)
```

This means Logos and Bimodal have **different initialization signatures**. Logos uses `combined_settings=` kwarg while Bimodal uses positional. After removing logos, these branches need cleanup — but this cleanup is not explicitly called out in any task. Task 100 or 104 must address this.

### 3. MISSING: Test Migration Task (Confidence: HIGH)

The bimodal theory tests live inside the source tree at `code/src/model_checker/theory_lib/bimodal/tests/` (12 test files), NOT in `code/tests/`. The top-level `code/tests/` directory contains logos-specific tests (`test_cli_subtheory.py`, `unit/theory_lib/logos/`). There's no bimodal-specific test file in `code/tests/`.

The existing pytest config (`pyproject.toml` line 66) points `testpaths = ["src/model_checker/theory_lib"]`, which currently discovers tests for ALL theories. After stripping logos:
- Logos test files will break on import (missing logos module)
- No task explicitly handles cleaning up or migrating the top-level test suite
- The OracleProvider needs its own test suite (Task 105 covers this but depends on 103+104, creating a long critical path)

**Recommendation**: Test cleanup should be part of Task 100 (strip), not deferred to Task 105.

### 4. SIGNIFICANT: The iterate/ Module Is Likely Unnecessary (Confidence: MEDIUM)

The OracleProvider protocol needs `find_countermodel()` which returns ONE countermodel or None. The iterate/ module (15+ source files, 20+ test files) is designed to find MULTIPLE distinct models with isomorphism detection via NetworkX.

For the OracleProvider use case:
- One countermodel is sufficient
- No iteration needed
- NetworkX dependency can be dropped
- All isomorphism detection code is wasted

However, the `BimodalModelIterator` is re-exported from `theory_lib/bimodal/__init__.py`. If someone wants to use the package standalone (not just via OracleProvider), iteration could still be useful.

**Recommendation**: Task 104 should explicitly scope whether iterate/ stays or goes. If it stays, it should be optional. If it goes, the NetworkX dependency can be dropped from pyproject.toml.

### 5. SIGNIFICANT: pyproject.toml Needs Major Overhaul, Not Just Entry Points (Confidence: HIGH)

Task 101 says "Update pyproject.toml with appropriate package identity." But the current pyproject.toml has significant concerns:

- **Package name**: `model-checker` → needs to become something like `bmlogic-oracle`
- **Description**: "hyperintensional theorem prover" → completely wrong for bimodal-only
- **Dependencies**: `networkx>=2.0` is listed as core dependency but only used by iterate/ (which may not be needed)
- **Optional deps**: jupyter, cvc5, matplotlib — all should be removed or restructured
- **Entry point**: `model-checker = "model_checker.__main__:run"` → script name changes
- **Classifiers/keywords**: All need updating
- **Python version**: `>=3.8` is quite old; the protocol uses `dict[str, Any]` syntax (3.9+) and `frozenset[str]` (3.9+)
- **testpaths**: Currently points to theory_lib which will break
- **Package directory**: `src/model_checker/` → does the package name change or just the pip name?

This is a significantly larger scope than Task 101 currently describes.

### 6. SIGNIFICANT: Formula Translation Is Harder Than It Looks (Confidence: MEDIUM)

Task 102 says to build `json_to_sentence()` but Sentence objects are created from **infix string notation** (e.g., `"(A \\boxright B)"`). The JSON format uses a tree structure with tags. This means:

- Option A: Convert JSON → infix string → Sentence (simple but fragile, round-trip lossy)
- Option B: Build Sentence objects directly from JSON tree (bypasses infix parser, cleaner but requires understanding Sentence internals deeply)
- Option C: Skip Sentence entirely, build Z3 constraints directly from JSON (most efficient for OracleProvider but divorces from the existing pipeline)

The task doesn't specify which approach, and each has very different implications for how much existing code can be reused vs. needs to be rewritten. This architectural decision should be made in Task 99 (audit) or Task 106, not discovered during implementation.

The JSON tags map to operators:
- `atom` → propositional variable (p, q, r...)
- `bot` → `\\bot` (⊥)
- `imp` → `\\rightarrow` (→)
- `box` → `\\Box` (□)
- `untl` → `U` (Until)
- `snce` → `S` (Since)

Note: the BimodalHarness uses ONLY 6 primitive constructors. But the existing operator set has 15 operators (including defined operators). The "round-trip fidelity" mentioned in Task 102 may not even be meaningful — JSON→internal is always possible but internal→JSON requires decomposing defined operators back to primitives.

### 7. MISSING: Solver Pipeline Path for OracleProvider (Confidence: HIGH)

The current model checking pipeline goes:
```
CLI → ParseFileFlags → BuildModule → _load_module() → SettingsManager → BuildExample → ModelConstraints → ModelStructure → Z3 solve → print output
```

The OracleProvider needs:
```
formula_json → ??? → Z3 solve → extract countermodel → return dict
```

Task 103 says "wrapping the existing Z3 model-checking pipeline" but the existing pipeline starts from **files on disk** (module_flags.file_path). There's no existing code path that takes a formula directly and returns a result programmatically without going through the CLI/file loader.

The closest thing is `utils/testing.py:run_test()` which takes `(example_case, semantic_class, proposition_class, ...)` and returns a boolean. But:
- It doesn't return the model, just True/False
- It doesn't handle timeouts via Z3 parameters (uses settings['max_time'] but for comparison only)
- It doesn't extract countermodel data

Task 103 or Task 104 needs to explicitly build a **new pipeline path** that goes: formula → syntax → semantics → constraints → solve → extract model → serialize JSON. This is more than "wrapping" existing code.

### 8. MISSING: Version Pinning and Compatibility Matrix (Confidence: MEDIUM)

The BimodalHarness OracleProvider has a `semantics_version` property that must match BimodalLogic's semantics. Neither Task 101 nor Task 103 addresses:
- Which BimodalLogic semantics version to target
- How to maintain compatibility across BimodalLogic updates
- Whether to declare BimodalHarness as a dependency or peer-dependency
- How the soundness gateway's 3-phase check (self-check → cross-validation → compatibility matrix) will be satisfied

### 9. MISSING: Z3 Context Isolation for OracleProvider (Confidence: MEDIUM)

The codebase has elaborate Z3 context management (`utils/context.py:isolated_z3_context`, `solver/lifecycle.py:invalidate_all_caches`). The OracleProvider will be called repeatedly with different formulas. Each call needs clean Z3 state.

The existing code resets state in `BimodalSemantics._reset_global_state()`, but this was designed for CLI batch execution, not high-throughput API calls. Tasks 103-104 need to address:
- Z3 context cleanup between find_countermodel() calls
- Memory management for repeated solver instantiation
- Thread safety if the OracleProvider is used concurrently

### 10. Task 99 (Audit) May Be Redundant with Task 106 (Confidence: MEDIUM)

Task 99 proposes to produce a "file-by-file refactor map" and "operator alignment" report. Task 106 does much of the same analysis at a higher level. If Task 106 produces revised task descriptions, Task 99's audit scope significantly overlaps.

Consider merging 99 into 106 (this task), or reducing 99 to a pure mechanical checklist that 106's research produces.

## Recommended Approach

1. **Merge Task 99 into Task 106**: The audit work belongs here in the architecture review, not as a separate task
2. **Split Task 100**: Separate "fix hard imports and coupling" from "delete unused code"
3. **Add test cleanup to Task 100**: Don't defer test migration to Task 105
4. **Force an architectural decision on formula translation** before Task 102 begins (JSON→infix vs JSON→Sentence-direct vs JSON→Z3-direct)
5. **Build a new pipeline path in Task 103/104**: Explicitly design the programmatic solve path rather than assuming the CLI path can be "wrapped"
6. **Scope iterate/ in Task 104**: Decide keep-as-optional vs. remove

## Evidence/Examples

- Hard logos import: `theory_lib/__init__.py:52`, `builder/example.py:34`
- Logos branching: `builder/runner.py:82,206`
- Builder complexity: 18 source files, 30+ test files — this is not a simple cleanup
- Output complexity: 20+ source files including progress bars, prompts, formatters — most unused by OracleProvider
- Bimodal tests: 12 test files inside `theory_lib/bimodal/tests/`, 0 in `code/tests/`

## Confidence Level

- Hard import issues: **HIGH** — verified via grep, will crash immediately
- Builder coupling: **HIGH** — verified in source code
- Test migration gap: **HIGH** — verified no bimodal tests in top-level test dir
- iterate/ unnecessary: **MEDIUM** — depends on whether standalone use is a goal
- Formula translation complexity: **MEDIUM** — depends on chosen approach
- Pipeline path missing: **HIGH** — no existing programmatic entry point exists
