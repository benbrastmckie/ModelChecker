# Critic Findings: Z3 Solver State Leakage Between Examples

- **Task**: 94 - fix_z3_solver_state_leakage
- **Role**: Teammate C (Critic)
- **Type**: z3

---

## Key Findings

The prior research (report 01) correctly identifies that `reset_z3_context()` fails to reset Z3's C library state. However, the analysis is incomplete in three important ways:

1. The actual mechanism of the failure is more subtle than reported
2. Option A (multiprocessing) has a hard serialization blocker the report underestimates
3. Option B (explicit contexts) requires pervasive changes across 50+ files and has a partial-fix risk

Additionally, there are Python-level global states contributing to the problem that the research missed entirely, and there is a simpler targeted fix (set `z3.z3._main_ctx = None`) that is neither Option A nor B.

---

## Assumption Challenges

### Challenge 1: The Diagnosis Is Partially Wrong

The report states that `reset_z3_context()` silently fails because `hasattr(z3, '_main_ctx')` returns False (the attribute is at `z3.z3._main_ctx`, not `z3._main_ctx`). This is confirmed correct.

However, the report then claims the code falls through to the `elif hasattr(z3, 'main_ctx')` branch and "also silently does nothing." This is incorrect. The `elif` branch **does execute** and sets `z3.main_ctx = None`. This overwrites the `main_ctx` function itself with `None`, corrupting the z3 module temporarily. The subsequent `importlib.reload(z3)` then **restores the function** — but crucially, it does NOT reset `z3.z3._main_ctx`, which holds the actual Context object. So on the next call to `z3.main_ctx()`, the old context is returned.

Empirical verification:
```python
import z3, z3.z3 as z3core
ctx_before = z3.main_ctx()  # initializes z3.z3._main_ctx
z3.main_ctx = None           # corrupts function (wrong target)
import importlib; importlib.reload(z3)  # restores function, NOT _main_ctx
ctx_after = z3.main_ctx()   # returns OLD context (same C-level object)
assert ctx_before is ctx_after  # True - no reset occurred
```

The **actual fix** for the global-context approach is a single line: `z3.z3._main_ctx = None`. This genuinely creates a fresh context on the next `z3.main_ctx()` call (confirmed with different Python and C-level object identities). This targeted fix is much simpler than either Option A or Option B and is not mentioned in report 01.

### Challenge 2: `_initialize_z3_context()` in `example.py` Is Also Silently Broken

`code/src/model_checker/builder/example.py:118` contains:
```python
try:
    z3.main_ctx().solver.reset()
except Exception:
    pass
```

`z3.Context` objects do not have a `solver` attribute (confirmed: `hasattr(z3.main_ctx(), 'solver') == False`). The `AttributeError` is silently swallowed. This is a dead code path that does nothing but create a false impression of isolation. Report 01 notes this call exists but does not identify that it always fails silently.

### Challenge 3: The Evidence Table May Not Establish Causation

The report's evidence table (BM_CM_3 UNSAT alone, SAT after EX_CM_1) is compelling but there is an alternative explanation: **timeout sensitivity**. BM_CM_3 uses `max_time: 2` seconds. The formula `Diamond A |= future A` with `N=2, M=2` involves a ternary `TaskRel` function, two unary world/time functions, quantified constraints over `M` time points, and witness predicates. This is a UFBV (Uninterpreted Functions + BitVectors) problem with quantifiers, which sits in a fragment that Z3's MBQI solver handles non-deterministically.

Z3 GitHub issue #7525 documents that Z3 exhibits nondeterministic behavior even with identical seeds on formulas outside fully decidable fragments. MBQI with bitvectors is known to have variable performance that depends on internal state ordering, not just learned lemmas.

**The timeout hypothesis**: If BM_CM_3 needs, say, 3-8 seconds cold, it would always timeout at the 2-second limit in isolation. After EX_CM_1 runs first, if MBQI caches function interpretations or variable orderings that happen to align with BM_CM_3's structure, it finds the model faster. This looks like "state leakage" but could also be timeout sensitivity.

The report does not test whether BM_CM_3 succeeds with a 30-second timeout in isolation. This is an important validation the research skips.

---

## Hidden Risks Identified

### Risk 1: Option A (Multiprocessing) Has a Hard Serialization Blocker

Z3 `ModelRef` objects cannot be pickled:
```
ValueError: ctypes objects containing pointers cannot be pickled
```

Confirmed empirically: neither `z3.ModelRef` nor `z3.BitVecRef` expressions can be serialized with Python's `pickle`. The report acknowledges "Z3 model objects can't be pickled" as a downside, but understates the severity. The current codebase has **extensive** post-solve `z3_model.eval()` calls:
- `code/src/model_checker/iterate/models.py` (lines 93-587): extracts world/state/truth-value data
- `code/src/model_checker/theory_lib/logos/semantic.py` (lines 514-1517): evaluates many expressions
- `code/src/model_checker/iterate/graph.py` (lines 105-253): graph construction
- `code/src/model_checker/models/structure.py` (lines 900-913): verify/falsify extraction

All of these use `z3_model.eval(expr, model_completion=True)` where `expr` is a Z3 formula. Both the model and the formula are non-picklable.

For Option A to work, either: (a) all result extraction must happen in the subprocess before returning, requiring serialization of the final Python results (dicts, lists, primitives — not Z3 objects), or (b) the architecture must be redesigned around fork-based process pools (Unix-only, fragile).

This is a substantial redesign, not a "higher overhead per example" tradeoff as described in the report.

### Risk 2: Option B Has a Pervasive Threading Requirement

Option B requires every Z3 expression to carry an explicit `ctx=` parameter. The codebase has:
- ~50 source files (non-test) that use Z3
- ~73 Z3 sort/function/expression calls in `bimodal/semantic.py` alone
- The abstraction layer in `solver/expressions.py` does NOT pass `ctx=` to any call

The risk is **partial threading**: if even one expression is created without `ctx=`, it silently uses the global context. When that expression is later passed to a solver with an explicit context, Z3 raises `Z3Exception: Context mismatch`. This is a latent correctness risk that is hard to audit completely.

The WitnessRegistry in `bimodal/semantic/witness_registry.py:85-90` creates `z3.Function()` calls without `ctx=`. The constraint generator and all semantic methods in `bimodal/semantic.py` similarly create expressions without `ctx=`. Threading the context through the `z3_shim` abstraction layer and `solver/expressions.py` is the right place to make the change, but it would require updating all function signatures.

### Risk 3: `Z3_reset_memory()` Is Confirmed Dangerous

Empirically confirmed: calling `z3.Z3_reset_memory()` after any Z3 objects have been created (even after `del` on the Python side, due to garbage collection timing) causes a segmentation fault:
```
Segmentation fault (core dumped)
```

The Z3 maintainers have confirmed this is expected behavior: resetting memory from managed interfaces is unsafe because Python's garbage collector may still hold references to Z3 objects when `Z3_reset_memory()` invalidates the underlying C memory. Option C in report 01 correctly notes this as "may cause segfaults" but understates that the segfault is essentially guaranteed in any real usage scenario.

### Risk 4: AtomSort Cache Is a Second Source of Leakage

`code/src/model_checker/syntactic/atoms.py:19` has:
```python
_atom_sort = None
```

This module-level cache is NOT reset between examples by the current `reset_solver_context()`. The `reset_atom_sort()` function exists and IS called from `reset_solver_context()` (confirmed, line 100-101). However, the `AtomSort` sort object itself is a Z3 `SortRef` that belongs to the global context. If the context is reset (once fixed), the cached `_atom_sort` would be from the OLD context — creating a context mismatch when the first expression is built using `AtomVal()`.

The reset_atom_sort call in reset_solver_context is correct IF context reset is also working. Currently neither works.

---

## Missing Research Gaps

### Gap 1: The Simpler Fix Is Not Analyzed

The research jumps to Option A or Option B without considering whether the current architecture (global context) could work if reset correctly. Setting `z3.z3._main_ctx = None` before each example IS a valid reset that creates a genuinely fresh C-level context. This is simpler than either option and does not require architectural changes. The research does not test or evaluate this.

The reason this approach is not sufficient is that Z3's CDCL(T) solver retains learned clauses at the C library level WITHIN a context. However, a new context (`z3.Context()`) gets a fresh C-level context object with no inherited state. Confirmed empirically: different `ctx.ref()` values after reset.

### Gap 2: No Analysis of MBQI's Phase Saving Across Examples

Z3's MBQI engine uses phase saving (remembering previous satisfying assignments to guide future search). The Z3 source and GitHub issue #1909 confirm that phase selection is context-scoped. A fresh context should reset phase-saving state. The research does not establish whether the observed speed-up is from MBQI phase saving (context-level, fixable by context reset) vs. learned clause reuse at a deeper C level (requires process isolation).

### Gap 3: Test Infrastructure Lacks Isolation

The bimodal test files (`tests/integration/`, `tests/e2e/`) have no Z3 isolation fixtures in conftest.py. Tests run sequentially under pytest share the same global Z3 context. This means:
- Test ordering affects test outcomes
- A flaky test that passes in isolation may fail in a full suite run
- The reported nondeterminism in examples may also manifest in test results

No conftest-level `autouse` fixture calling `reset_solver_context()` (once fixed) exists. This is a testing infrastructure gap.

### Gap 4: The `z3.reset_params()` Call in `runner.py` Has Unknown Effect

`code/src/model_checker/builder/runner.py:327` calls `z3.reset_params()` after `reset_z3_context()`. The `reset_params()` function resets global solver parameters (like `verbose` level, timeout defaults) but does NOT reset context-level state (learned lemmas, caches). The interaction between `reset_params()` and context state is not analyzed in the report. This call may actually make things worse by resetting the timeout parameter that was set earlier.

---

## Evidence Validation

### Validation 1: Timeout Hypothesis Not Tested

The report does not document testing BM_CM_3 with a longer timeout (e.g., 30 seconds) in isolation. Until this is tested, the observed behavior could be explained by:
- State leakage causing structural reuse (report's hypothesis)
- Timeout sensitivity: 2s is insufficient cold, but sufficient with warmup state
- A combination of both

The distinction matters for solution choice: if timeout sensitivity is the primary cause, simply increasing `max_time` to 30s for the problematic examples (Option D in the report) would fix the user-visible symptom without requiring architectural changes.

### Validation 2: The Diagnosis Conflates Two Bugs

The report identifies the Z3 state leakage problem but does not distinguish:
- **Bug A**: `reset_solver_context()` uses the wrong attribute (`z3._main_ctx` vs `z3.z3._main_ctx`), so context is never reset
- **Bug B**: Even if context were reset, `importlib.reload(z3)` would not reset it either (it restores the function but not the stored context reference)

These are independent bugs that compound. The `z3.z3._main_ctx = None` fix addresses both simultaneously.

### Validation 3: Module Reload Danger

`importlib.reload(z3)` in `reset_solver_context()` (line 92) is dangerous beyond just ineffectiveness. It re-runs z3's module-level initialization code, which may register duplicate lifecycle hooks (the `register_cache_hook` calls in `z3_shim.py` and `atoms.py` run at import time). After a reload, hooks could be registered twice. The `lifecycle.py:27-29` does check for duplicates (`if hook not in _cache_hooks`), which prevents double-registration, but this is fragile.

---

## Confidence Level

**High confidence** on:
- The exact mechanism of `reset_solver_context()` failure (empirically confirmed in isolation)
- `Z3_reset_memory()` causes segfaults (empirically confirmed)
- Z3 model objects cannot be pickled (empirically confirmed)
- `_initialize_z3_context()` in `example.py` always silently fails (code analysis)
- `z3.z3._main_ctx = None` creates a genuinely fresh context (empirically confirmed)

**Medium confidence** on:
- Timeout sensitivity as an alternative/contributing explanation for BM_CM_3 behavior (hypothesis not tested)
- MBQI phase saving as the primary mechanism (plausible but not directly proven)
- Option B pervasiveness estimate (50 files based on grep, actual threading scope may vary)

**Low confidence** on:
- Whether the C-level context reset (`z3.z3._main_ctx = None`) actually resolves the timing disparity, vs. just being a cleaner architecture (requires running the full bimodal test suite to confirm)
