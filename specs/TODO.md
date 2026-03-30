---
next_project_number: 57
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 56. Fix comparison.py warnings: add 'M' to DEFAULT_EXAMPLE_SETTINGS and gitignore output.json
- **Effort**: 0.25 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Added M to DEFAULT_EXAMPLE_SETTINGS to suppress 8 unknown setting warnings, and added output.json to gitignore.
- **Language**: python
- **Plan**: [01_implementation-plan.md](056_fix_comparison_warnings_default_settings/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](056_fix_comparison_warnings_default_settings/summaries/01_execution-summary.md)

**Description**: Fix comparison.py warnings: add 'M' to DEFAULT_EXAMPLE_SETTINGS in LogosSemantics (semantic.py) to suppress 8 "Unknown example setting 'M'" warnings from constitutive examples CL_TH_16-19, and add output.json to .gitignore since it is a generated benchmark file.

### 55. Create comparison.py script for systematic z3 vs cvc5 solver benchmarking with JSON output
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Created comparison.py script that benchmarks z3 vs cvc5 on all 138 logos theory examples with structured JSON output, solver switching, and disagreement tracking.
- **Language**: python
- **Research**: [01_comparison-script-research.md](055_create_comparison_script_z3_cvc5_benchmarking/reports/01_comparison-script-research.md)
- **Plan**: [01_implementation-plan.md](055_create_comparison_script_z3_cvc5_benchmarking/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](055_create_comparison_script_z3_cvc5_benchmarking/summaries/01_execution-summary.md)

**Description**: Create a comparison.py script that imports examples from theory_lib/logos/examples.py and systematically runs each example against both z3 and cvc5 solvers, recording results and timing data to output.json for analysis.

### 54. Fix MOD_COMP_1/2/3 solver comparison test failures caused by lambda error
- **Effort**: 0.25 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Added 'first_order' to modal subtheory dependencies in test_solver_comparison.py to fix the MOD_COMP test failures caused by missing lambda operator support.
- **Language**: python
- **Research**: [01_lambda-error-research.md](054_fix_mod_comp_solver_comparison_test_failures/reports/01_lambda-error-research.md)
- **Plan**: [01_implementation-plan.md](054_fix_mod_comp_solver_comparison_test_failures/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](054_fix_mod_comp_solver_comparison_test_failures/summaries/01_execution-summary.md)

**Description**: Fix MOD_COMP_1/2/3 solver comparison test failures caused by '\\lambda' error. All 6 tests (z3 and cvc5 backends) fail with the same error, suggesting a LaTeX rendering or operator definition issue in the modal_comparison subtheory examples. Investigate the '\\lambda' KeyError/lookup failure in the operator or semantics pipeline, fix the root cause, and verify that test_solver_comparison.py passes 100% (all tests green). Key files: code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py, and the modal_comparison subtheory examples (MOD_COMP_1, MOD_COMP_2, MOD_COMP_3).

---

### 53. Refine progress bar timing architecture for consistent fill and display
- **Effort**: 3 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Fixed progress bar timing mismatch by storing _frozen_elapsed in freeze_at_current() and using it in complete(). Added 4 new tests (1 unit, 3 integration), class constants, type hints, and state machine documentation.
- **Language**: python
- **Research**: [01_timing-architecture-review.md](053_refine_progress_bar_timing_architecture/reports/01_timing-architecture-review.md)
- **Plan**: [01_implementation-plan.md](053_refine_progress_bar_timing_architecture/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](053_refine_progress_bar_timing_architecture/summaries/01_execution-summary.md)

**Description**: Refine and harden progress bar system for non-isomorphic model iteration. Current issues: (1) Fill fraction vs displayed time inconsistency -- freeze_at_current() captures fill at model-found time but complete() displays elapsed including post-search processing (difference calculation ~500ms between freeze and yield in iterate/core.py lines 377-399), creating bars that show 0% fill but 0.6s text. (2) Fill fraction should either be recalculated at complete() time to match displayed elapsed, or the displayed elapsed should use the frozen timestamp. (3) The overall progress bar timing architecture needs consolidation -- there are two code paths for stopping bars (_stop_progress_animation in runner.py and stop_animation_only in core.py) that were just unified but the underlying timing model is fragile. (4) Progress bar display ordering (bar->output->bar) was recently fixed by reordering complete_model_search calls but should have integration tests. Key files: output/progress/animated.py (TimeBasedProgress.freeze_at_current/complete), output/progress/core.py (UnifiedProgress coordination), iterate/core.py (calls stop_animation_only at line 375, difference calc at 378-383, yield at 400), builder/runner.py (_process_with_iterations, _run_generator_iteration).

---

### 52. Redesign progress bar for non-isomorphic model iteration
- **Effort**: 3.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Redesigned progress bar system with time-proportional fill semantics and correct bar->output->bar ordering. Added freeze_at_current() method, stop_animation_only() for deferred completion, and modified iterator/runner for proper output sequencing.
- **Language**: python
- **Research**: [01_progress-bar-redesign.md](052_redesign_progress_bar_model_iteration/reports/01_progress-bar-redesign.md)
- **Plan**: [01_implementation-plan.md](052_redesign_progress_bar_model_iteration/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](052_redesign_progress_bar_model_iteration/summaries/01_execution-summary.md)

**Description**: Redesign progress bar for non-isomorphic model iteration: (1) Progress bar should show actual search progress per-model, filling proportionally to elapsed time and completing at the actual fill level when found (not snapping to 100%), (2) Each model's output should appear immediately after its progress bar completes (bar -> model output -> bar -> model output), not stacked bars followed by stacked outputs, (3) For model 1: bar animates during search -> freezes at actual fill -> model header + output prints -> then model 2 bar starts, (4) The bar fill semantics should be time-based against timeout which is fine, but the completion should freeze at the actual elapsed fraction rather than filling to 100%. Key files: output/progress/animated.py (TimeBasedProgress.complete fills to 100%), output/progress/core.py (UnifiedProgress coordination), iterate/core.py (calls complete_model_search at line 374 inside iterator before yield), builder/runner.py (_run_generator_iteration doesn't manage per-model progress for models 2+). The core architectural issue is that iterate/core.py manages progress bars internally and calls complete_model_search before yielding, but runner.py manages the display ordering -- these need to be reconciled so progress completes -> model displays -> next progress starts, in sequence.

---

### 51. Fix cvc5 CLI integration issues
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Fixed cvc5 CLI integration by adding z3/cvc5/subtheory to standard_args, updating runtime label to backend-neutral 'Solver Run Time', and documenting solver backend selection in Settings README.
- **Language**: z3
- **Research**:
  - [01_teammate-a-findings.md](051_fix_cvc5_cli_integration_issues/reports/01_teammate-a-findings.md)
  - [01_teammate-b-findings.md](051_fix_cvc5_cli_integration_issues/reports/01_teammate-b-findings.md)
  - [01_team-research.md](051_fix_cvc5_cli_integration_issues/reports/01_team-research.md)
- **Plan**: [01_implementation-plan.md](051_fix_cvc5_cli_integration_issues/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](051_fix_cvc5_cli_integration_issues/summaries/01_execution-summary.md)

**Description**: Fix cvc5 CLI integration issues: add z3/cvc5 to standard_args in settings.py to suppress spurious "Flag 'cvc5' doesn't correspond to any known setting" warning, replace hardcoded "Z3 Run Time" label in structure.py with backend-aware label, and audit other hardcoded Z3 references in user-facing output.

---

### 50. Create standalone solver comparison script using dev_cli.py
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: python

**Description**: Create standalone solver comparison script that runs each logos example through dev_cli.py twice (once with z3, once with cvc5), displaying concrete model/countermodel output with timing data for side-by-side comparison.

---

### 49. Expand examples.py with first_order subtheory examples and create solver comparison test suite
- **Effort**: 3.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Integrated 12 first_order examples into unified logos examples module and created parametrized solver comparison test suite covering 138 examples against z3 and cvc5 backends with timing collection and graceful degradation.
- **Language**: z3
- **Research**:
  - [01_teammate-a-findings.md](049_solver_comparison_first_order_examples/reports/01_teammate-a-findings.md)
  - [01_teammate-b-findings.md](049_solver_comparison_first_order_examples/reports/01_teammate-b-findings.md)
  - [01_team-research.md](049_solver_comparison_first_order_examples/reports/01_team-research.md)
- **Plan**: [01_implementation-plan.md](049_solver_comparison_first_order_examples/plans/01_implementation-plan.md)
- **Summary**: [01_solver-comparison-summary.md](049_solver_comparison_first_order_examples/summaries/01_solver-comparison-summary.md)

**Description**: Expand /home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/logos/examples.py to include examples from the first_order/ subtheory, then create a test file that imports examples from all subtheories and runs them first with z3 and then with cvc5, collecting results and timing data for systematic comparison between cvc5 and z3.

---

### 48. Fix failing test_update_types_atomic in syntactic package
- **Effort**: 0.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Fixed test_update_types_atomic by replacing MagicMock with real Z3 Const object. The test was failing because z3.is_const() returns False for MagicMock objects.
- **Language**: python
- **Research**: [01_research-report.md](048_fix_test_update_types_atomic_syntactic/reports/01_research-report.md)
- **Plan**: [01_implementation-plan.md](048_fix_test_update_types_atomic_syntactic/plans/01_implementation-plan.md)

**Description**: Fix failing test_update_types_atomic in syntactic package: test uses MagicMock for sentence letter but store_types() requires Z3 Const.

---

### 47. Implement multi-solver abstraction layer for z3, cvc5, and future constraint solvers
- **Effort**: 10 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Implemented multi-solver abstraction layer enabling Z3 and cvc5 backends with CLI flags, Protocol-based interfaces, and 34 new tests.
- **Language**: z3
- **Research**:
  - [01_team-research.md](047_multi_solver_abstraction_layer/reports/01_team-research.md)
  - [03_plan-review.md](047_multi_solver_abstraction_layer/reports/03_plan-review.md)
- **Plan**: [03_multi-solver-revised.md](047_multi_solver_abstraction_layer/plans/03_multi-solver-revised.md)
- **Summary**: [03_implementation-summary.md](047_multi_solver_abstraction_layer/summaries/03_implementation-summary.md)

**Description**: Review the 2026 state of the art in constraint solving and design/implement a multi-solver abstraction layer enabling the ModelChecker to use z3, cvc5, or other constraint solvers interchangeably. Perform a clean-break refactor to achieve a maximally maintainable and flexible architecture that accommodates multiple solvers going forward.

---

### 46. Fix z3.And() return type narrowing for custom Exists() calls in first-order operators
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Added cast(BoolRef, ...) to all 51 z3.And/z3.Or/z3.Not call sites across 13 files, eliminating all Probe-related Pyright errors. Zero runtime impact. All z3_helpers tests pass.
- **Language**: z3
- **Research**: [01_team-research.md](046_fix_z3_and_return_type_narrowing/reports/01_team-research.md)
- **Plan**: [04_cast-z3-returns.md](046_fix_z3_and_return_type_narrowing/plans/04_cast-z3-returns.md)

**Description**: Fix z3.And() return type narrowing for custom Exists() calls in first-order operators. z3.And() returns Union[Unknown, Probe, BoolRef] per z3 stubs, but custom Exists(bvs, formula: BoolRef) requires BoolRef. Affects lines 384 and 572 in code/src/model_checker/theory_lib/logos/subtheories/first-order/operators.py. Code is correct at runtime but fails static type checking. Research needed: survey all z3.And/z3.Or usage patterns across the codebase to find the most mathematically correct and uniform approach — whether via type narrowing, signature widening, or a wrapper utility — rather than ad-hoc casts.

---

### 45. Rename `first-order` subtheory directory to `first_order` for valid Python packaging
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Verified directory rename from first-order to first_order. All 53 subtheory tests pass, all 9 proposition tests pass, all 99 parsing tests pass, all 33 unit tests pass. No remaining 'first-order' string references in code.
- **Plan**: [01_rename-first-order.md](045_rename_first_order_directory/plans/01_rename-first-order.md)
- **Language**: python

**Description**: Rename `code/src/model_checker/theory_lib/logos/subtheories/first-order/` to `first_order` (underscore). The hyphenated name is not a valid Python identifier, breaking Pyright LSP features (go-to-definition, autocompletion, type checking). Need to: (1) rename directory to `first_order`, (2) update all `importlib.import_module()` calls referencing `first-order`, (3) update subtheory registry strings in `__init__.py` files, (4) update `load_subtheories()`/`load_subtheory()` calls across examples and tests, (5) update any documentation or comments referencing the old path, (6) verify all tests still pass after rename.

---

### 44. Remove vestigial ISemantics Protocol and use concrete SemanticDefaults type in Operator base class
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Removed 3 vestigial ISemantics/Semantics Protocol definitions, updated Operator base class to use SemanticDefaults, and added LogosSemantics class annotations to 22 Logos operator classes. All 334 tests pass.
- **Research**: [01_isemantics-refactor.md](044_remove_vestigial_isemantics_protocol/reports/01_isemantics-refactor.md)
- **Plan**: [02_isemantics-refactor-revised.md](044_remove_vestigial_isemantics_protocol/plans/02_isemantics-refactor-revised.md)
- **Summary**: [02_isemantics-refactor-summary.md](044_remove_vestigial_isemantics_protocol/summaries/02_isemantics-refactor-summary.md)
- **Language**: python

**Description**: Remove vestigial ISemantics Protocol and use concrete SemanticDefaults type in Operator base class. The codebase has 3 unused/underspecified ISemantics/Semantics Protocol definitions (syntactic/types.py, models/types.py, theory_lib/types.py) that cause pyright errors across all operator files. Replace with SemanticDefaults in Operator.__init__ and narrow to LogosSemantics in Logos-specific operators. Delete unused Protocol definitions.

---

### 43. Fix 3 pre-existing test failures
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Fixed 3 pre-existing test failures: updated test_exists_duality.py to check for extract_lambda_term, added parser to valid_errors in test_semantic_coverage.py, and changed FO_CM_4 example to use closed formula. All 86 tests pass.
- **Research**: [01_test-failures-research.md](043_fix_preexisting_test_failures/reports/01_test-failures-research.md)
- **Plan**: [01_test-failures-fix.md](043_fix_preexisting_test_failures/plans/01_test-failures-fix.md)
- **Language**: python

**Description**: Fix 3 pre-existing test failures: (1) FO_CM_4 - open formula with free variable v_x needs quantifier wrapping or test update, (2) test_exists_uses_validation - ExistsOperator.true_at no longer contains validate_lambda_argument in source, (3) test_semantic_method_calls_dont_crash - 'parser error' not in valid_errors whitelist for compatible/maximal/is_world method calls.

---

### 42. Uniform eval_point threading across all logos subtheory operators
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-29
- **Summary**: Added with_world helper to preserve variable bindings across modal world shifts. Fixed NecessityOperator and CounterfactualOperator, removed vestigial PossibilityOperator code, added 3 compositionality tests.
- **Research**: [01_team-research.md](042_uniform_eval_point_threading/reports/01_team-research.md)
- **Plan**: [01_eval-point-threading.md](042_uniform_eval_point_threading/plans/01_eval-point-threading.md)
- **Summary**: [01_eval-point-threading-summary.md](042_uniform_eval_point_threading/summaries/01_eval-point-threading-summary.md)
- **Language**: python

**Description**: The `eval_point` dictionary carries both `"world"` (current world state) and `"assignment"` (first-order variable bindings). Several operators construct new eval_point dicts from scratch when shifting the world, dropping the assignment key. This breaks compositionality: a formula like `Box(forall x. phi(x))` would lose variable bindings when the necessity operator shifts to a new world.

---

### 41. Final conciseness pass: throat-clearing, roadmap, narrative flow
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-25
- **Summary**: Removed ~102 words of throat-clearing (roadmap paragraph, transition sentence, minor hedges) and added ~80 words of motivated section transitions for Sections 3, 6, and 7. Net ~22 word reduction with improved narrative flow.
- **Research**: [01_team-research.md](041_final_conciseness_pass/reports/01_team-research.md)
- **Plan**: [01_conciseness-plan.md](041_final_conciseness_pass/plans/01_conciseness-plan.md)
- **Summary**: [01_conciseness-summary.md](041_final_conciseness_pass/summaries/01_conciseness-summary.md)
- **Language**: latex
- **Dependencies**: Task #40

**Description**: Final polish pass on `latex/paper.tex` for publication readiness. Three focus areas:

1. **Global throat-clearing removal** (topic 7): Search-and-delete filler phrases throughout the paper: "it is worth noting that", "it should be observed that", "it bears mentioning that", "in the remainder of this section", "as one might expect", "it is perhaps unsurprising that". State claims directly without preamble. (~230 words savings with zero content loss.)

2. **Trim paper roadmap** (topic 16): The section-by-section preview in the introduction (Sec 1.3, "Paper Roadmap" paragraph, lines ~285-293) is verbose. Cut to 2-3 sentences or remove entirely -- JAR reviewers find sections from the table of contents.

3. **Narrative flow improvements** (topic 17): Add brief design-rationale paragraphs at key transition points: (a) at the start of Section 3 (Modularity) explaining why modularity matters for this framework; (b) at the start of the Logos case study (Sec 6) explaining what the case study is meant to demonstrate beyond what precedes it. Ensure each section opening motivates what follows rather than just stating what it covers.

---

### 40. Trim code listings, over-explanation, and aspirational content
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-24
- **Summary**: Reduced paper from 29 to 27 pages by trimming ~1,310 words: aspirational TheoryLib content (~500 words), code listings (~340 words), and over-explanations for JAR audience (~470 words).
- **Research**: [01_trim-overexplanation.md](040_trim_code_and_overexplanation/reports/01_trim-overexplanation.md)
- **Plan**: [01_trim-overexplanation-plan.md](040_trim_code_and_overexplanation/plans/01_trim-overexplanation-plan.md)
- **Summary**: [01_trim-overexplanation-summary.md](040_trim_code_and_overexplanation/summaries/01_trim-overexplanation-summary.md)
- **Language**: latex
- **Dependencies**: Task #39

**Description**: Targeted verbosity reduction in `latex/paper.tex` across three categories:

1. **Trim code listings** (topic 5): Show only semantically interesting methods in code listings. Use ellipsis (`...`) for boilerplate (`__init__`, `__repr__`, etc.). Where multiple operator classes follow the same pattern, show one representative example and note "analogous definitions for other operators." Cut repeated structural patterns. (~900-1100 words savings.)

2. **Cut over-explanation for JAR audience** (topic 6): Remove elementary explanations that JAR readers don't need: basic Boolean/lattice definitions stated at textbook level, Python OOP concepts ("Python's class system allows us to define..."), and introductory Z3 descriptions. Replace with concise one-sentence reminders or citations. (~450 words savings.)

3. **Condense TheoryLib vision and future work** (topics 8, 9): Section 5 (TheoryLib) includes community model, contribution pathways, incentives, quality standards, and BibTeX citation format that read like a project README rather than a journal paper. Keep the core architectural vision and the comparative research platform concept; cut aspirational community-building content. Similarly, cut generic future work items ("extend to other logics", "improve performance", "add a GUI") and keep only technically specific future directions.

---

### 39. Eliminate structural redundancy across sections
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-24
- **Summary**: Removed redundant "first implementation" claims, consolidated tables, added back-references for bitvector/bilateral semantics, trimmed Section 6, restructured Section 9.1. Estimated savings: ~2.5-3.5 pages.
- **Research**: [01_redundancy-research.md](039_eliminate_structural_redundancy/reports/01_redundancy-research.md)
- **Plan**: [01_redundancy-plan.md](039_eliminate_structural_redundancy/plans/01_redundancy-plan.md)
- **Language**: latex
- **Dependencies**: Task #37, Task #38

**Description**: Major structural revision of `latex/paper.tex` to eliminate redundant re-explanations. This task should be done AFTER tasks 37-38 (which add new content) so that all content is in place before consolidation.

1. **De-duplicate core concept explanations** (topic 1): Each of these concepts is explained from scratch in multiple sections. Establish one definitive treatment and replace others with back-references:
   - Bitvector representation (explained 3x: Sec 4.2 state space, Sec 2.2 constraints, Sec 6 case study)
   - Bilateral semantics (explained 5x: abstract, intro, Sec 2, Sec 6, conclusion)
   - Arity/exponential growth (discussed 4x: Sec 2.5, Sec 4.2, Sec 2.5.4, Sec 6 performance)
   - "First implementation" novelty claim (asserted 5x -- limit to abstract + contributions list)

2. **Consolidate overlapping comparison tables** (topic 2): Table 2 ("Comparative Predictions Across Theories", line ~604) and Table 7 ("Comparative Inference Results", line ~1112) share overlapping dimensions and data. Either merge into one comprehensive table, or clearly differentiate: one for theoretical predictions, one for empirical tool-level results with no shared rows.

3. **Restructure Discussion to stop restating contributions** (topic 3): Contributions are listed in intro (Sec 1.3), re-discussed in Discussion (Sec 9.1), and summarized again in Conclusion (Sec 9.4). The Discussion section should analyze implications and tradeoffs, not re-enumerate achievements. Rewrite Sec 9.1 to focus on what the results mean rather than what was done.

4. **Trim Logos case study re-explanations** (topic 4): Sec 6 re-derives bitvector encoding, bilateral evaluation, and counterfactual semantics rather than referencing Sections 2-4. Rewrite to assume the reader has read preceding sections; focus on the concrete example, results, and what the case study specifically demonstrates.

Estimated savings: ~2-3 pages.

---

### 38. Strengthen proofs, add limitations, qualify novelty claims
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-24
- **Summary**: Added encoding correctness section with soundness/extraction theorems, expanded limitations with threats-to-validity format, added modal logic solvers and hyperintensional logic to related work, qualified 5 novelty claims.
- **Research**: [01_proofs-limitations-research.md](038_strengthen_proofs_and_limitations/reports/01_proofs-limitations-research.md)
- **Plan**: [01_proofs-limitations-plan.md](038_strengthen_proofs_and_limitations/plans/01_proofs-limitations-plan.md)
- **Language**: latex
- **Dependencies**: Task #37

**Description**: Improve technical rigor in `latex/paper.tex` across three areas:

1. **Expand proof sketches for Z3 encoding correctness** (topic 15): The correctness claim for the Z3 encoding (that constraints faithfully represent the formal semantics) is central to the paper's validity. Currently only a brief justification is provided. Expand with: (a) a clear statement of the correctness theorem, (b) a detailed proof sketch explaining the proof strategy and key lemma, (c) either a full proof in an appendix or a reference to a mechanized verification. For JAR, this is the bridge between formal semantics and implementation -- a brief sketch is insufficient.

2. **Add Limitations section** (topic 18): Add a dedicated subsection (likely at the end of Discussion, Sec 9) covering: incompleteness of the BitVector encoding for infinite models, soundness guarantees beyond testing, scalability ceiling (what problem sizes become intractable and why), restrictions on the class of models considered, and threats to validity of the empirical results. Currently no limitations are discussed explicitly.

3. **Qualify or substantiate novelty claims** (topic 13): The paper claims "first systematic computational implementation of bilateral truthmaker semantics" in multiple places. Either: (a) soften to "first dedicated implementation" with appropriate caveats, or (b) add a more thorough survey in Related Work (Sec 8) demonstrating that no prior tool handles this specific combination of features (bilateral evaluation + hyperintensional operators + counterfactual conditionals + SMT backend). Check tools like MLSOLVER, Tableaux Workbench, and Isabelle/HOL encodings of non-normal modal logics.

---

### 37. Add formal definitions, complexity analysis, and experimental setup
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-24
- **Summary**: Added experimental setup paragraph, hyperintensionality definition, complexity analysis section, and two bibliography entries to latex/paper.tex. Document compiles successfully.
- **Research**: [01_formal-definitions-research.md](037_add_formal_definitions_and_complexity/reports/01_formal-definitions-research.md)
- **Plan**: [01_formal-content-plan.md](037_add_formal_definitions_and_complexity/plans/01_formal-content-plan.md)
- **Language**: latex
- **Dependencies**: Task #36

**Description**: Add missing technical content to `latex/paper.tex` that JAR reviewers will expect:

1. **Formal definition of "hyperintensional"** (topic 12): The term "hyperintensional" is used throughout as a key property but never formally defined. Add a definition (either as a numbered Definition environment or a Remark) stating the criterion: an operator O is hyperintensional iff there exist formulas A, B that are logically equivalent (true in all the same worlds) but O(A) and O(B) differ in truth value. State precisely which operators in the framework are hyperintensional and provide an example or proof.

2. **Complexity analysis of the model checking algorithm** (topic 14): The paper never provides formal complexity bounds. Add a subsection (likely in Sec 2.5 or Sec 4) analyzing: (a) the complexity class of the decision problem for the relevant logic fragments, (b) the complexity of the Z3 encoding (how constraint count and quantifier depth grow with N and K), (c) citation of known complexity results for modal/hyperintensional logics. At minimum, state whether the problem is PSPACE, EXPTIME, or undecidable for the relevant fragments.

3. **Experimental setup for benchmark reproducibility** (topic 10): Tables 4, 6, and 7 present timing data with no information about the experimental setup. Add an "Experimental Setup" paragraph at the start of Section 7 (Results) specifying: hardware (CPU, RAM, OS), Z3 version, Python version, number of trials and whether results are averaged/median, whether times are wall-clock or CPU time, timeout configuration, and standard deviation or confidence intervals. This is the single most likely reason for desk rejection at JAR.

---

### 36. Fill placeholders and fix metadata
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: latex
- **Dependencies**: None

**Description**: Fix all placeholder and incomplete content in `latex/paper.tex`:

1. **Author information** (line 216): Replace `\author*[1]{\fnm{Author} \sur{Name}}` and `\email{author@example.com}` with real author name and email.

2. **Affiliation** (line 218): Replace `\orgdiv{Department}, \orgname{University}, \orgaddress{\city{City}, \state{State}, \country{Country}}` with real institutional affiliation.

3. **Code availability** (line 1332): Replace `[repository URL]` and `[license]` with the actual GitHub/PyPI URL and license name (MIT).

4. **Author contributions** (line 1336): Replace `[Author contributions to be added]` with appropriate contribution statement.

5. **Verify URLs**: Confirm that `https://github.com/benbrastmckie/ModelChecker` (if referenced) and `https://pypi.org/project/model-checker/` are live and accessible. Consider adding a Zenodo DOI for the specific version used in benchmarks.

6. **MSC Classification** (line 245): Uncomment and verify the MSC codes (`03B45, 68T15, 68Q60`) are appropriate for the paper's content, or update them.

---

### 35. Fix first-order semantics and predicate extension display
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: python
- **Dependencies**: None

**Description**: Upon running the first-order theory in the model-checker, the output shows the model-checker is running but does not find or produce a reasonable looking model. Each n-place predicate should get mapped to a set of verifiers and falsifiers (functions from n states to a state) where the positive extension of a predicate in a world is the set of state n-tuples which get mapped to a state that is part of that world by SOME verifier for the predicate. Review the semantics in `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ` and `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ` to verify the first-order semantics in the model-checker is correct. Then evaluate and redesign the elements needed to extract predicate extensions at each world and display these when printing a model.

---

### 34. Display predicate extensions in first-order countermodels
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Research**: [research-001.md](034_display_predicate_extensions_in_countermodels/reports/research-001.md), [research-002.md](034_display_predicate_extensions_in_countermodels/reports/research-002.md), [research-003.md](034_display_predicate_extensions_in_countermodels/reports/research-003.md), [research-004.md](034_display_predicate_extensions_in_countermodels/reports/research-004.md)
- **Plan**: [implementation-001.md](034_display_predicate_extensions_in_countermodels/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](034_display_predicate_extensions_in_countermodels/summaries/implementation-summary-20260303.md)
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
- **Status**: [COMPLETED]
- **Research**: [research-002.md](033_fix_premature_progress_bar_display/reports/research-002.md)
- **Plan**: [implementation-002.md](033_fix_premature_progress_bar_display/plans/implementation-002.md)
- **Summary**: [implementation-summary-20260303.md](033_fix_premature_progress_bar_display/summaries/implementation-summary-20260303.md)
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
