---
next_project_number: 35
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 34. Display predicate extensions in first-order countermodels
- **Effort**: TBD
- **Status**: [RESEARCHED]
- **Research**: [research-001.md](034_display_predicate_extensions_in_countermodels/reports/research-001.md)
- **Language**: python
- **Dependencies**: None

**Description**: When the model checker finds a countermodel for a first-order example, the output currently shows the truth values and verifier/falsifier sets for the premise and conclusion formulas (e.g., `|\exists v_x. F[v_x]| = < {a, a.b, b}, {} >`), but does not show what the predicates themselves denote in the model. For the countermodel to be interpretable, users need to see the **extension** of each predicate — i.e., what proposition each predicate maps each domain element to.

**Problem details**:
- In `LogosModelStructure.print_all` (`code/src/model_checker/theory_lib/logos/semantic.py:1478`), the output for countermodels calls `print_states`, `print_evaluation`, `print_input_sentences`, and `print_model`, but no code extracts and displays predicate extensions.
- Predicates are registered in `LogosSemantics` via `register_predicate(name, arity)` (`semantic.py:746`), which creates Z3 uninterpreted functions stored in `_predicate_verifiers` and `_predicate_falsifiers` dictionaries.
- Domain elements are all 2^N bit vectors (enumerated in quantifier operators like `ForAllOperator.true_at` at `first-order/operators.py:319` with `range(2**N)`).
- For a unary predicate F and domain element d, the verifier states are all states s where `semantics._predicate_verifiers["F"](d, s)` is True in the Z3 model, and similarly for falsifiers.

**Required output** (new section to appear between "State Space" and "INTERPRETED PREMISE"):
```
PREDICATE EXTENSIONS:

F (arity 1):
  F(□)   = < {}, {} >
  F(a)   = < {a, a.b}, {} >
  F(b)   = < {}, {a.b} >
  F(a.b) = < {}, {} >
```

**Design considerations**:
1. Only show predicates that were actually used in the formulas (registered in semantics), not all possible predicates.
2. Use the same state formatting as the rest of the output (`bitvec_to_substates(bit, N)` for state names, `pretty_set_print` for set display).
3. Respect the `print_impossible` setting — only show possible states in verifier/falsifier sets unless `print_impossible` is True.
4. Handle higher-arity predicates: for binary predicate R, enumerate all (d1, d2) pairs.
5. The method should be added to `LogosModelStructure` and called from `print_all` only when a countermodel is found and the first-order subtheory is loaded (i.e., `_predicate_verifiers` is non-empty in the semantics).
6. TDD: write tests first in `code/src/model_checker/theory_lib/logos/tests/` or nearby that verify the new predicate extension section appears in countermodel output for first-order examples.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` — add `print_predicate_extensions` method to `LogosModelStructure` and call it from `print_all`.

---

### 33. Fix premature progress bar display between examples
- **Effort**: TBD
- **Status**: [RESEARCHED]
- **Research**: [research-002.md](033_fix_premature_progress_bar_display/reports/research-002.md)
- **Plan**: [implementation-001.md](033_fix_premature_progress_bar_display/plans/implementation-001.md)
- **Language**: python
- **Dependencies**: None

**Description**: When running examples with `iterate > 1`, the iteration progress bar appears between examples — specifically BEFORE the "EXAMPLE NAME: there is a countermodel." header of the second example. This is confusing because the progress bar visually belongs to the current example, not the gap between examples.

**Problem details**:
- Observed in `output/test.md`: after FO_TH_1's closing `========================================`, the line `Finding non-isomorphic models: [████████████████████] 1/2 0.1s` appears before FO_CM_1's opening `========================================` and header.
- Root cause: In `_process_with_iterations` (`code/src/model_checker/builder/runner.py:388`), the `UnifiedProgress` tracker starts model-1 search (with animated progress bar) BEFORE the example header is printed:
  1. `print()` — blank line
  2. `progress.start_model_search(1)` — **progress bar starts animating here**
  3. `example = BuildExample(...)` — Z3 runs to find model 1
  4. `progress.complete_model_search(found=True)` — **progress bar shows completed state "1/2 0.1s"**
  5. `print()` — blank line after progress
  6. `_handle_iteration_mode` → `_capture_and_save_output` → **example header printed here**
- The progress bar for model 1 (the initial countermodel search) completes and displays its final state BEFORE the example header is printed.

**Required fix**: The progress bar for model 1's initial solve should not appear before the example header. Options (in order of preference):
1. **Remove model 1 progress bar entirely**: The initial Z3 solve already reports "Z3 Run Time: X.XXXX seconds" in the example output. Replace the model-1 `UnifiedProgress` tracking with a simple `Spinner` (as used in `run_model_check` at `runner.py:165`). Only the iteration progress (models 2+) needs the full progress bar since those searches are time-bounded by `max_time` and may take much longer.
2. **Move model 1 progress to appear after the header**: Print a simplified example header before the progress bar starts. However this requires knowing premises/conclusions before Z3 runs, which may be complex.
3. **Clear the progress bar before printing the header**: After model 1 is found, clear the terminal line entirely (via `\r` or display clear) before printing the example output.

**Key invariant to preserve**: The iteration progress bar (for models 2+) must still appear and function correctly. Only the model-1 pre-header progress bar needs to be fixed.

**Files to modify**:
- `code/src/model_checker/builder/runner.py` — modify `_process_with_iterations` (lines 388-450) to remove/replace the model-1 progress bar.
- Possibly `code/src/model_checker/output/progress/core.py` — adjust `UnifiedProgress` if needed to support deferred model-1 tracking.

**Verification**: After the fix, running the first-order examples should show output in this order for each example: `[header] → [state space] → [premises/conclusions] → [blank] → [iteration progress bar for models 2+] → [iteration report]`. No progress bar content should appear before any example header.

---

### 32. Consolidate first-order subtheory to standard structure
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Research**: [research-001.md](032_consolidate_first_order_subtheory_structure/reports/research-001.md)
- **Plan**: [implementation-001.md](032_consolidate_first_order_subtheory_structure/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](032_consolidate_first_order_subtheory_structure/summaries/implementation-summary-20260303.md)
- **Language**: python
- **Dependencies**: None

**Description**: Refactor first-order subtheory (`code/src/model_checker/theory_lib/logos/subtheories/first-order/`) to contain only the standard files (`__init__.py`, `examples.py`, `operators.py`, `README.md`) matching other subtheories. Review contents of `constraints.py` and `denotation.py` to identify correct integration points. Ensure the logos theory structure remains systematic and extensible for future subtheories.

---

### 28. Archive unused theory libraries
- **Effort**: 1-2 hours
- **Status**: [COMPLETED]
- **Plan**: [implementation-001.md](028_archive_unused_theories/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](028_archive_unused_theories/summaries/implementation-summary-20260303.md)
- **Language**: python
- **Dependencies**: None

**Description**: Archive `theory_lib/exclusion/` and `theory_lib/imposition/` directories to `code/boneyard/`. Update any references to these theories in the codebase. Ensure the boneyard directory structure preserves the original organization. Run tests to confirm no regression from removing these theories from active code paths.

---

### 29. Clean up specs directories
- **Effort**: 1 hour
- **Status**: [COMPLETED]
- **Research**: [research-001.md](029_cleanup_specs_directories/reports/research-001.md)
- **Plan**: [implementation-002.md](029_cleanup_specs_directories/plans/implementation-002.md)
- **Summary**: [implementation-summary-20260303.md](029_cleanup_specs_directories/summaries/implementation-summary-20260303.md)
- **Language**: general
- **Dependencies**: None

**Description**: Remove all `specs/` directories throughout the repository except for `ModelChecker/specs/`. Identify any specs content that should be preserved and migrate it appropriately before deletion. Document what was removed for reference.

---

### 30. Consolidate documentation directories
- **Effort**: 4-6 hours
- **Status**: [COMPLETED]
- **Research**: [research-001.md](030_consolidate_documentation/reports/research-001.md)
- **Plan**: [implementation-001.md](030_consolidate_documentation/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](030_consolidate_documentation/summaries/implementation-summary-20260303.md)
- **Language**: general
- **Dependencies**: Task #27

**Description**: Reduce documentation to two directories: `ModelChecker/docs/` for general project information (less technical overviews, user guides) and `code/docs/` for technical documentation (API references, architecture, development standards). Review existing documentation across all docs directories, eliminate redundancy, preserve valuable content, and improve organization. Update all documentation cross-references.

---

### 31. Clean scripts and artifacts
- **Effort**: 2-3 hours
- **Status**: [COMPLETED]
- **Research**: [research-001.md](031_clean_scripts_and_artifacts/reports/research-001.md)
- **Plan**: [implementation-001.md](031_clean_scripts_and_artifacts/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](031_clean_scripts_and_artifacts/summaries/implementation-summary-20260303.md)
- **Language**: general
- **Dependencies**: Task #27

**Description**: Review scripts and artifacts throughout `code/` subdirectories. Remove unnecessary scripts and artifacts. Improve organization and documentation of those that are needed. Ensure any cleanup scripts, maintenance utilities, or development tools are properly documented and organized.
