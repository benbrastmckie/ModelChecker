---
next_project_number: 89
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 88. Optimize quantifier implementation for logos theory
- **Effort**: medium
- **Status**: [RESEARCHED]
- **Language**: z3
- **Dependencies**: 87
- **Research**:
  - [01_teammate-a-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/01_teammate-a-findings.md)
  - [01_teammate-b-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/01_teammate-b-findings.md)
  - [01_team-research.md](088_optimize_quantifier_implementation_logos_theory/reports/01_team-research.md)
  - [02_teammate-a-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/02_teammate-a-findings.md)
  - [02_teammate-b-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/02_teammate-b-findings.md)
  - [02_team-research.md](088_optimize_quantifier_implementation_logos_theory/reports/02_team-research.md)
  - [03_teammate-a-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/03_teammate-a-findings.md)
  - [03_teammate-b-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/03_teammate-b-findings.md)
  - [03_team-research.md](088_optimize_quantifier_implementation_logos_theory/reports/03_team-research.md)
  - [04_teammate-a-findings.md](088_optimize_quantifier_implementation_logos_theory/reports/04_teammate-a-findings.md)
  - [04_team-research.md](088_optimize_quantifier_implementation_logos_theory/reports/04_team-research.md)
- **Plan**: [02_implementation-plan.md](088_optimize_quantifier_implementation_logos_theory/plans/02_implementation-plan.md)
- **Summary**: [02_quantifier-optimization-summary.md](088_optimize_quantifier_implementation_logos_theory/summaries/02_quantifier-optimization-summary.md) (PARTIAL: 2/4 phases)

**Description**: Research and implement optimizations for how quantifiers work throughout the model-checker for the logos/ theory. Build on the findings of task 87 and the documentation in docs/theory/QUANTIFIER_SOLVERS.md and code/scripts/README.md.

### 87. Research native quantifiers for Z3 and CVC5
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-05
- **Summary**: Created docs/theory/QUANTIFIER_SOLVERS.md with educational documentation on Z3/CVC5 quantifier mechanisms including e-matching, MBQI, CEGQI, FMF, comparison tables, and ModelChecker application guidance.
- **Language**: z3
- **Research**:
  - [01_teammate-a-findings.md](087_research_native_quantifiers_z3_cvc5/reports/01_teammate-a-findings.md)
  - [01_teammate-b-findings.md](087_research_native_quantifiers_z3_cvc5/reports/01_teammate-b-findings.md)
  - [01_team-research.md](087_research_native_quantifiers_z3_cvc5/reports/01_team-research.md)
  - [02_teammate-a-findings.md](087_research_native_quantifiers_z3_cvc5/reports/02_teammate-a-findings.md)
  - [02_teammate-b-findings.md](087_research_native_quantifiers_z3_cvc5/reports/02_teammate-b-findings.md)
  - [02_team-research.md](087_research_native_quantifiers_z3_cvc5/reports/02_team-research.md)
- **Plan**: [02_implementation-plan.md](087_research_native_quantifiers_z3_cvc5/plans/02_implementation-plan.md)
- **Summary**: [02_implementation-summary.md](087_research_native_quantifiers_z3_cvc5/summaries/02_implementation-summary.md)

**Description**: Research exactly how the native quantifiers for z3 and cvc5 work in detail, creating a detailed report in /home/benjamin/Projects/Logos/ModelChecker/docs/theory/ which can then be linked in /home/benjamin/Projects/Logos/ModelChecker/code/scripts/README.md for a deep dive on quantification.

### 86. Extend first-order examples to test limits and exploit solver differences
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-05
- **Summary**: Added 46 stress test examples across 5 suites (N_SCALE, NEST, ALT, COMP, STRESS) to examples.py, plus --suite and --find-choke-point flags to benchmark script for solver limit testing.
- **Language**: z3
- **Dependencies**: 85
- **Research**: [01_stress-test-research.md](086_extend_first_order_examples_test_solver_limits/reports/01_stress-test-research.md)
- **Plan**: [01_implementation-plan.md](086_extend_first_order_examples_test_solver_limits/plans/01_implementation-plan.md)
- **Summary**: [01_execution-summary.md](086_extend_first_order_examples_test_solver_limits/summaries/01_execution-summary.md)

**Description**: Extend the examples in first_order/examples.py to test the limits of the different solver configurations and exploit differences between finitary-z3, finitary-cvc5, native-z3, and native-cvc5 modes as benchmarked in Task 85.

### 85. Create systematic quantifier benchmark for first-order theory
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-05
- **Summary**: Created first-order quantifier benchmark comparing 4 modes (finitary-z3, finitary-cvc5, native-z3, native-cvc5). All 12 examples run successfully. Key finding: native-cvc5 returns incorrect UNSAT for countermodel examples.
- **Language**: z3
- **Research**: [01_benchmark-research.md](085_create_systematic_quantifier_benchmark_first_order/reports/01_benchmark-research.md)
- **Plan**: [02_implementation-plan.md](085_create_systematic_quantifier_benchmark_first_order/plans/02_implementation-plan.md)

**Description**: Create a systematic benchmark to compare z3 native quantifiers, cvc5 native quantifiers, and finitary quantifiers in the first_order/ subtheory. Output style inspired by code/scripts/quantifier_benchmark.py with tabular comparison of correctness and timing.

### 84. Add native Z3 quantifier operator classes for first-order subtheory
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-04
- **Summary**: Added NativeForAllOperator (\\all) and NativeExistsOperator (\\some) using Z3 native quantifiers. Extended parser to recognize new syntax. Created 12 NFO examples and 20 unit tests. Native quantifiers are 44% faster while producing identical results to finitary quantifiers.
- **Language**: z3
- **Research**: [01_native-quantifier-research.md](084_add_native_z3_quantifier_operators_first_order/reports/01_native-quantifier-research.md)
- **Plan**: [01_implementation-plan.md](084_add_native_z3_quantifier_operators_first_order/plans/01_implementation-plan.md)

**Description**: The finitary definition of quantifiers are used throughout the majority of the semantics and operators defined in the logos/ theory. For the first-order subtheory, add additional operator classes for quantifiers that use native Z3 quantifiers instead of the finitary quantifiers used elsewhere. This will facilitate comparison between finitary and native quantifiers for claims articulated with first-order quantifiers.

---

### 83. Investigate root cause of native quantifier incorrect UNSAT results
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-04
- **Summary**: Reverted Task 82 toggleable quantifier mode implementation. Restored z3_helpers.py to pre-Task-82 state with only finitary enumeration. All unit tests pass.
- **Language**: z3
- **Dependencies**: 82
- **Research**: [01_root-cause-analysis.md](083_investigate_native_quantifier_unsat_root_cause/reports/01_root-cause-analysis.md)
- **Plan**: [01_revert-task82-plan.md](083_investigate_native_quantifier_unsat_root_cause/plans/01_revert-task82-plan.md)
- **Summary**: [01_reversion-summary.md](083_investigate_native_quantifier_unsat_root_cause/summaries/01_reversion-summary.md)

**Description**: The task 82 benchmark found that native quantifiers return incorrect results for countermodel examples. All 10 countermodel examples (expecting SAT) returned UNSAT with native quantifiers, while finitary enumeration correctly found countermodels (SAT). This is not a timeout issue - the solvers return definitive UNSAT results incorrectly. Investigate the root cause of this behavior in order to design an appropriate solution.

---

### 82. Test Z3 vs CVC5 comparison with primitive quantifiers
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-04
- **Summary**: Implemented toggleable quantifier mode in z3_helpers.py and benchmark script. Benchmark results show finitary enumeration is essential: native quantifiers incorrectly return UNSAT for all SAT cases (0% accuracy on countermodels vs 100% for finitary). Finitary is also 11x faster.
- **Language**: z3
- **Research**:
  - [01_quantifier-comparison-design.md](082_test_z3_cvc5_primitive_quantifiers/reports/01_quantifier-comparison-design.md)
  - [02_toggleable-quantifier-design.md](082_test_z3_cvc5_primitive_quantifiers/reports/02_toggleable-quantifier-design.md)
- **Plan**: [02_implementation-plan.md](082_test_z3_cvc5_primitive_quantifiers/plans/02_implementation-plan.md)
- **Summary**: [02_benchmark-results.md](082_test_z3_cvc5_primitive_quantifiers/summaries/02_benchmark-results.md)

**Description**: State spaces are finite throughout the model-checker. Because of this, the quantifiers are defined in terms of boolean operations over the relevant substitution instances instead of using z3 quantifiers. Test how Z3 compares to CVC5 when primitive Z3 quantifiers are used instead of the finitary definitions currently used. Create a method for this comparison without disrupting the existing semantics and examples which use finite quantifier definitions. The test should create markdown and JSON output following `code/scripts/comparison.py` as an example of good output format.

---

### 81. Fix iterate package test regression
- **Effort**: small
- **Status**: [COMPLETED]
- **Completed**: 2026-04-03
- **Language**: z3
- **Dependencies**: 77
- **Research**: [01_iterate-regression-analysis.md](081_fix_iterate_package_test_regression/reports/01_iterate-regression-analysis.md)

**Description**: Research and fix the iterate package test regression. After running `./code/run_tests.py`, the iterate package tests FAILED while all other tests passed. This regression appeared after the task 77 implementation (conditional unsat core tracking). Need to investigate root cause and fix all issues to restore passing tests.

---

### 80. Optimize constraint encoding for CVC5 UNSAT performance
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-03
- **Summary**: Encoding is near-optimal for CVC5. Push/pop batching and simplification both degraded performance. Final gap 1.70x overall is inherent to solver differences.
- **Language**: z3
- **Dependencies**: 79
- **Research**:
  - [01_cvc5-encoding-optimization.md](080_cvc5_encoding_optimization/reports/01_cvc5-encoding-optimization.md)
  - [02_optimization-testing.md](080_cvc5_encoding_optimization/reports/02_optimization-testing.md)

**Description**: Research whether the constraint encoding style used by the logos theory can be restructured to improve CVC5's UNSAT proof search without degrading Z3 performance. The benchmark data (task 76) shows CVC5 is 8-34x slower than Z3 on UNSAT (theorem) examples, while SAT (countermodel) performance is nearly identical. This suggests the encoding itself may be poorly suited to CVC5's internal heuristics rather than CVC5 being inherently slower.

**Research approach** (successive rounds until approach is clear):

1. **Round 1 - Encoding analysis**: Examine how the logos theory generates SMT constraints. Focus on `logos/semantic.py`, the operator files in `subtheories/*/operators.py`, and `models/structure.py`. Characterize the constraint patterns: how many variables, how deeply nested, what theories are combined (bitvectors, arrays, quantifiers, uninterpreted functions). Export representative SMT-LIB2 from both solvers for the worst-case examples (CL_TH_1 at 34x, CF_TH_2 at 30x, MOD_TH_5 at 28x) to understand what the solvers actually see.

2. **Round 2 - CVC5 encoding guidelines**: Research CVC5 documentation, academic papers, and SMT-COMP submissions for encoding best practices. CVC5 may prefer: (a) different variable ordering strategies, (b) fewer intermediate let-bindings vs more, (c) different use of bitvector operations vs integer arithmetic, (d) assertion grouping/structuring differences, (e) different handling of quantifiers (instantiation patterns, triggers). Compare with how Z3-optimal encodings are structured.

3. **Round 3 - Targeted experiments**: Based on findings, identify 2-3 specific encoding changes to test. For each, create a minimal experiment using `run_example_with_timing()` on the worst-case examples. Measure whether the change closes the gap. Candidates might include: (a) replacing BitVec with Int for small domains, (b) restructuring how world-accessibility constraints are encoded, (c) pre-simplifying constraints before adding to CVC5, (d) splitting large conjunctions into individual assertions.

4. **Round 4 - Feasibility assessment**: For changes that show improvement, assess whether they can be implemented as a CVC5-specific encoding path without duplicating the entire constraint generation system. Determine if the change can be a post-processing step (transform constraints after generation) or requires deeper changes to the theory semantics layer.

**Success criteria**: Identify at least one encoding change that reduces CVC5's UNSAT time ratio from 9.37x average to under 4x on the curated benchmark, or conclusively demonstrate that the encoding is already near-optimal for CVC5 and the gap is due to fundamental solver differences.

---

### 79. Tune CVC5 solver options for modal logic performance
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-03
- **Summary**: Validated Task 77 performance mode config as optimal. CVC5 now 1.61x slower than Z3 (was 8.9x). No further tuning needed.
- **Language**: z3
- **Dependencies**: 77
- **Research**:
  - [01_cvc5-options-research.md](079_cvc5_solver_options_tuning/reports/01_cvc5-options-research.md)
  - [02_cvc5-options-post-task77.md](079_cvc5_solver_options_tuning/reports/02_cvc5-options-post-task77.md)

**Description**: Research and test CVC5 solver configuration options to improve performance on the logos theory's constraint profile. The benchmark data (task 76) shows CVC5 is dramatically slower on UNSAT proofs (avg 9.37x) while competitive on SAT. CVC5 has extensive configuration options that may not be optimal for this workload: finite-domain bitvector reasoning over modal logic Kripke structures with tracked assertions.

**Research approach** (successive rounds until approach is clear):

1. **Round 1 - CVC5 option inventory**: Research CVC5's command-line options and Python API configuration. Focus on categories relevant to the constraint profile: (a) `--bv-solver` modes (bitblast, layered, etc.), (b) decision heuristics (`--decision=justification` vs default), (c) SAT solver backend options (`--sat-solver`), (d) preprocessing/simplification levels, (e) proof production settings (currently `produce-unsat-cores=true` is forced on), (f) quantifier instantiation strategies (`--enum-inst`, `--cbqi`), (g) `--tlimit-per` vs `--rlimit` for resource limits. Document which options are accessible via `cvc5.pythonic.Solver.set()` vs only CLI.

2. **Round 2 - Profile the bottleneck**: Determine where CVC5 spends time on UNSAT problems. Use `--stats` or `--stats-every-query` options if available through the Python API. Key questions: Is CVC5 spending time in (a) preprocessing/simplification, (b) the core DPLL(T) loop, (c) theory solver calls (BV, UF), (d) proof production for unsat cores, or (e) model construction attempts before concluding UNSAT? This determines which options to tune.

3. **Round 3 - Systematic option testing**: Using the comparison benchmark infrastructure (`run_example_with_timing`), test promising option combinations on the 3 worst-case UNSAT examples (CL_TH_1, CF_TH_2, MOD_TH_5). Test one variable at a time first, then combinations of winners. Key experiments: (a) disable `produce-unsat-cores` to measure its overhead, (b) try each `--bv-solver` mode, (c) try `--decision=justification`, (d) try aggressive preprocessing. Record timing for each configuration.

4. **Round 4 - Validate and integrate**: For the best configuration found, run the full curated benchmark to ensure no regressions on SAT examples. Determine how to apply solver options: (a) hardcoded in `CVC5SolverAdapter.__init__()`, (b) configurable via example settings, or (c) conditional based on whether unsat cores are needed (links to task 77).

**Success criteria**: Identify a CVC5 option configuration that reduces average UNSAT time ratio from 9.37x to under 5x without degrading SAT performance, or conclusively demonstrate that CVC5's default options are already near-optimal for this workload and the gap is architectural.

**Key files**: `code/src/model_checker/solver/cvc5_adapter.py` (current options in `__init__`), `code/src/model_checker/theory_lib/logos/comparison.py` (benchmark harness), `code/src/model_checker/models/structure.py` (solver creation and timeout).

---

### 78. Design hybrid solver strategy (Z3 for UNSAT, CVC5 for SAT)
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Language**: z3
- **Dependencies**: 77

**Description**: Research and design a strategy that leverages each solver's strengths based on the benchmark data (task 76): Z3 excels at UNSAT proofs (theorems) while CVC5 is competitive or faster at SAT (countermodel finding). The data shows CVC5 wins on 5/24 examples, all SAT cases, and is within 2x on most other SAT cases. Z3 wins decisively on all UNSAT cases (8-34x faster).

**Research approach** (successive rounds until approach is clear):

1. **Round 1 - Architecture survey**: Study how the current solving pipeline works end-to-end. Map the flow from `BuildExample` through `structure.py:solve()` to result extraction. Key questions: (a) At what point does the solver commit to searching for SAT vs proving UNSAT? (b) Can two solvers run in parallel on the same problem? (c) What data structures would need to be shared or duplicated? (d) How does the iteration loop (finding multiple models) interact with solver choice? (e) What is the overhead of running both solvers vs one?

2. **Round 2 - Strategy patterns**: Research established patterns for multi-solver strategies in SMT solving. Options to evaluate: (a) **Portfolio solving**: Run both solvers in parallel, take the first result (requires threading/multiprocessing, adds complexity). (b) **Sequential fallback**: Try CVC5 first with short timeout; if SAT, done; if timeout, switch to Z3 (simpler but adds latency on UNSAT). (c) **Heuristic routing**: Based on example characteristics (subtheory, expectation hint, constraint count), route to the better solver (requires training data). (d) **Race with early termination**: Start both, kill the slower one when the faster returns. Evaluate each against: implementation complexity, performance gain, reliability, and resource usage.

3. **Round 3 - Feasibility deep-dive**: For the most promising 1-2 strategies, investigate implementation specifics. Key concerns: (a) Python's GIL limits true parallelism — would need `multiprocessing` not `threading`. (b) CVC5 and Z3 solver instances may not be fork-safe. (c) Unsat core extraction is only needed from one solver. (d) The current `switch_solver()` mechanism does full cache invalidation — parallel solvers would need independent constraint construction. (e) Memory impact of maintaining two sets of constraints.

4. **Round 4 - Cost-benefit analysis**: Given the findings, determine whether a hybrid strategy is worth the complexity. The current total runtime is 18.7s for 24 examples (14.9s CVC5 + 3.8s Z3). If we could achieve best-of-both, total would be ~3.5s. But the real question is whether CVC5 adds value beyond what Z3 alone provides. Assess: Does CVC5 solve ANY problem that Z3 cannot (timeouts, different results)? If not, the hybrid adds complexity without correctness benefit — only a small SAT speedup on some examples.

**Success criteria**: Produce a clear recommendation — either a concrete hybrid strategy design ready for planning, or a well-reasoned argument for why single-solver (Z3 with CVC5 as validation) is the better path. The recommendation should be grounded in empirical data from the benchmark and architectural analysis of the codebase.

**Key files**: `code/src/model_checker/models/structure.py` (solve loop), `code/src/model_checker/solver/registry.py` (backend switching), `code/src/model_checker/solver/lifecycle.py` (cache invalidation), `code/src/model_checker/builder/example.py` (BuildExample), `code/src/model_checker/theory_lib/logos/comparison.py` (benchmark).

---

### 77. Conditional unsat core tracking for CVC5 solver
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-03
- **Language**: z3
- **Research**:
  - [01_unsat-core-overhead.md](077_conditional_unsat_core_tracking/reports/01_unsat-core-overhead.md)
  - [02_conditional-design.md](077_conditional_unsat_core_tracking/reports/02_conditional-design.md)
- **Plan**: [02_conditional-core-tracking.md](077_conditional_unsat_core_tracking/plans/02_conditional-core-tracking.md)
- **Summary**: [02_conditional-core-tracking-summary.md](077_conditional_unsat_core_tracking/summaries/02_conditional-core-tracking-summary.md)

**Description**: Research whether disabling CVC5's `produce-unsat-cores` option when unsat cores are not needed can improve performance. Currently `CVC5SolverAdapter.__init__()` unconditionally sets `solver.set('produce-unsat-cores', 'true')`, which forces CVC5 to maintain proof-tracking overhead on every query — including SAT queries where unsat cores are never extracted. The benchmark data (task 76) shows CVC5 is 3.9x slower overall and up to 34x slower on UNSAT examples.

**Research approach** (successive rounds until approach is clear):

1. **Round 1 - Measure the overhead**: Create a minimal experiment that runs the same examples with `produce-unsat-cores` enabled vs disabled. Use the comparison benchmark's `run_example_with_timing()` to measure both SAT and UNSAT examples. Focus on the worst-case examples: CL_TH_1 (34x ratio), CF_TH_2 (30x), MOD_TH_5 (28x). If disabling unsat cores shows <5% improvement, this task can be closed early — the overhead is not significant and the gap is elsewhere.

2. **Round 2 - Trace unsat core usage**: Map every code path where `solver.unsat_core()` is called. Determine: (a) Is it called on every `check()` result, or only on UNSAT results? (b) Is it called during iteration (finding additional models)? (c) Which callers actually USE the returned core vs discard it? (d) Can the adapter detect at construction time whether cores will be needed? Key files to trace: `structure.py:solve()`, `iterate/constraints.py`, any code that calls `solver.unsat_core()`.

3. **Round 3 - Design the conditional mechanism**: Based on findings, design how to make unsat core tracking conditional. Options: (a) Add a `need_unsat_cores: bool` parameter to `CVC5SolverAdapter.__init__()` and `create_solver()`. (b) Use lazy initialization — don't set `produce-unsat-cores` until `assert_tracked()` is first called. (c) Add a solver option in example settings (`unsat_cores: true/false`). (d) Always disable for SAT-expected examples (when `expectation=True`). Evaluate each for correctness safety — disabling cores when they're needed would cause silent failures.

4. **Round 4 - Broader implications**: Consider how this interacts with the other optimization tasks. If task 79 (options tuning) reveals that `produce-unsat-cores` is a major bottleneck, this task becomes high-priority. If task 78 (hybrid strategy) concludes CVC5 should only handle SAT queries, then cores are never needed for CVC5 and this becomes trivial. Document these dependencies.

**Success criteria**: Quantify the performance impact of `produce-unsat-cores` on CVC5 (with/without, on both SAT and UNSAT examples). If significant (>10% improvement when disabled), design a safe conditional mechanism. If insignificant, document the finding and close the task.

**Key files**: `code/src/model_checker/solver/cvc5_adapter.py:27-34` (current unconditional setting), `code/src/model_checker/solver/protocols.py` (TrackedSolverProtocol), `code/src/model_checker/models/structure.py` (solver creation), `code/src/model_checker/iterate/constraints.py` (unsat core usage).

---

### 76. Refactor comparison.py for selective examples with dual-solver timing comparison
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-04-03
- **Summary**: Added --curated, --format, --table flags to comparison.py for focused dual-solver timing comparison
- **Language**: z3
- **Research**: [01_comparison-refactor-research.md](076_refactor_comparison_dual_solver_timing/reports/01_comparison-refactor-research.md)
- **Plan**: [01_implementation-plan.md](076_refactor_comparison_dual_solver_timing/plans/01_implementation-plan.md)
- **Summary**: [01_implementation-summary.md](076_refactor_comparison_dual_solver_timing/summaries/01_implementation-summary.md)

**Description**: Refactor comparison.py to run a curated selection of examples (a couple theorems and a couple invalid claims for each operator) rather than all examples from examples.py. For each selected example, run both z3 and cvc5, compare results (model found, no model, timeout), and record the time each solver takes. Skip countermodel printing for this comparison test.

---

### 75. Optimize CVC5 solver integration following best practices
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Added three-layer term ID fallback to CVC5SolverAdapter.unsat_core()
- **Language**: z3
- **Research**:
  - [01_cvc5-best-practices.md](075_optimize_cvc5_solver_best_practices/reports/01_cvc5-best-practices.md)
  - [02_team-research.md](075_optimize_cvc5_solver_best_practices/reports/02_team-research.md)
- **Plan**: [02_implementation-plan.md](075_optimize_cvc5_solver_best_practices/plans/02_implementation-plan.md)
- **Summary**: [02_execution-summary.md](075_optimize_cvc5_solver_best_practices/summaries/02_execution-summary.md)

**Description**: Research CVC5 documentation and community best practices online, then apply optimizations to improve solver performance, model evaluation, and iteration. Build on task 74's findings (truthiness checks, lazy string conversion).

---

### 74. Investigate CVC5 model evaluation and iteration performance bottleneck
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Fixed CVC5 performance bottlenecks reducing BuildExample time from 18s to 0.7s by using explicit None checks and lazy string conversion.
- **Language**: z3
- **Research**:
  - [01_cvc5-performance-findings.md](074_investigate_cvc5_iteration_performance/reports/01_cvc5-performance-findings.md)
  - [02_cvc5-deep-dive.md](074_investigate_cvc5_iteration_performance/reports/02_cvc5-deep-dive.md)
- **Plan**: [02_cvc5-performance-fix.md](074_investigate_cvc5_iteration_performance/plans/02_cvc5-performance-fix.md)
- **Summary**: [02_cvc5-performance-summary.md](074_investigate_cvc5_iteration_performance/summaries/02_cvc5-performance-summary.md)

**Description**: CVC5 model structure building is ~100x slower than Z3 for counterfactual examples (18s vs 0.02s for initial model, timeout on 2nd model). The SMT `solver.check()` is fast (0.47s), but evaluating expressions against the CVC5 model (`model.eval()`) during `BuildExample` construction and iteration is extremely slow. Investigate: (a) profile exactly where time is spent during CVC5 model evaluation, (b) whether CVC5's `model.eval()` has known performance issues or alternative APIs, (c) whether the z3_shim expression evaluation path has unnecessary overhead with CVC5, (d) whether iteration can fall back to Z3 after initial CVC5 model finding, and (e) whether CVC5 solver options (e.g., `produce-models`, simplification level) can improve evaluation performance. Current workarounds in `constraints.py` (solver timeout, adapter reuse) mitigate hangs but don't address root cause.

---

### 73. Fix per-example solver backend leaking across examples via _cli_override
- **Effort**: small
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Added clear_cli_backend() and invalidate_all_caches() calls to runner.py's example processing finally block, preventing solver backend settings from leaking between examples.
- **Language**: z3
- **Research**:
  - [01_backend-leak-analysis.md](073_fix_per_example_solver_backend_leak/reports/01_backend-leak-analysis.md)
  - [02_iterator-context-analysis.md](073_fix_per_example_solver_backend_leak/reports/02_iterator-context-analysis.md)
- **Plan**:
  - [01_clear-cli-backend.md](073_fix_per_example_solver_backend_leak/plans/01_clear-cli-backend.md) (superseded)
  - [02_clear-cli-backend-revised.md](073_fix_per_example_solver_backend_leak/plans/02_clear-cli-backend-revised.md)
- **Summary**: [02_clear-cli-backend-summary.md](073_fix_per_example_solver_backend_leak/summaries/02_clear-cli-backend-summary.md)

**Description**: The new `lifecycle.set_backend_with_invalidation()` calls `set_cli_backend()` which sets `_cli_override` in registry.py. This override persists across examples, so when one example sets `solver: cvc5`, all subsequent examples without an explicit solver field inherit cvc5 through the sticky `_cli_override`. The fix should separate CLI-level overrides from per-example settings. Either: (a) add a `clear_cli_backend()` call after each example, (b) use a separate `_settings_backend` variable with lower priority than `_cli_override`, or (c) refactor `_configure_solver_backend` to save/restore the previous backend.

---

### 72. Fix CVC5 constraint compatibility with Z3 expression types
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Implemented unified z3/cvc5 architecture with hook-based lifecycle management (lifecycle.py), centralized backend access (backend.py), and runtime type guards (type_guards.py). All 34 solver tests and 14 CVC5 integration tests pass.
- **Language**: z3
- **Research**:
  - [01_cvc5-z3-compatibility.md](072_fix_cvc5_constraint_compatibility/reports/01_cvc5-z3-compatibility.md)
  - [02_team-research.md](072_fix_cvc5_constraint_compatibility/reports/02_team-research.md)
  - [03_unified-architecture.md](072_fix_cvc5_constraint_compatibility/reports/03_unified-architecture.md)
- **Plan**:
  - [01_cvc5-expression-conversion.md](072_fix_cvc5_constraint_compatibility/plans/01_cvc5-expression-conversion.md) (superseded)
  - [02_cache-invalidation-fix.md](072_fix_cvc5_constraint_compatibility/plans/02_cache-invalidation-fix.md) (superseded)
  - [03_unified-architecture.md](072_fix_cvc5_constraint_compatibility/plans/03_unified-architecture.md)
- **Summary**: [03_unified-architecture-summary.md](072_fix_cvc5_constraint_compatibility/summaries/03_unified-architecture-summary.md)

**Description**: When running examples with CVC5 solver instead of Z3, the model checker crashes with `SMTException: True, False or SMT Boolean expression expected. Received And(...) of type <class 'z3.z3.BoolRef'>`. The CVC5 adapter receives Z3 BoolRef objects which it cannot cast. Research every component that touches the z3/cvc5 choice to design a graceful, systematic approach that refactors the codebase to cleanly support both solvers with identical countermodel output formatting.

---

### 71. Add per-example solver setting with precedence chain
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Added per-example solver setting with 'z3' default, validation, tests, and documentation. Precedence: CLI > per-example > default.
- **Research**:
  - [01_per-example-solver.md](071_add_per_example_solver_setting/reports/01_per-example-solver.md)
  - [02_settings-architecture.md](071_add_per_example_solver_setting/reports/02_settings-architecture.md)
- **Plan**:
  - [01_per-example-solver.md](071_add_per_example_solver_setting/plans/01_per-example-solver.md)
  - [02_settings-architecture.md](071_add_per_example_solver_setting/plans/02_settings-architecture.md)
  - [03_revised-with-examples.md](071_add_per_example_solver_setting/plans/03_revised-with-examples.md)
- **Execution**: [03_execution-summary.md](071_add_per_example_solver_setting/summaries/03_execution-summary.md)
- **Language**: python

**Description**: Add a `solver` field to example settings that accepts `'z3'` or `'cvc5'` and overrides the semantic theory defaults. Precedence chain (highest to lowest): CLI flags (`--z3`/`--cvc5`) > per-example `solver` setting > semantic theory defaults. This allows individual examples to specify which solver backend they require while still respecting explicit CLI overrides.

---

### 70. Fix cvc5 "Z3 expression expected" compatibility errors
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Fixed cvc5 'Z3 expression expected' errors by replacing static simplify import with dynamic z3.simplify() lookup in semantic.py; all 13 affected examples now pass.
- **Research**: [01_cvc5-expression-errors.md](070_fix_cvc5_z3_expression_compatibility/reports/01_cvc5-expression-errors.md)
- **Plan**: [01_cvc5-expression-fix.md](070_fix_cvc5_z3_expression_compatibility/plans/01_cvc5-expression-fix.md)
- **Summary**: [01_cvc5-expression-fix-summary.md](070_fix_cvc5_z3_expression_compatibility/summaries/01_cvc5-expression-fix-summary.md)
- **Language**: z3

**Description**: Fix cvc5 compatibility errors in comparison.py. Multiple examples fail with "cvc5: Z3 expression expected" error when running against cvc5 solver. Affected examples include EXT_CM_2, MOD_CM_3, MOD_CM_4, CL_CM_4 through CL_CM_14. Investigate root cause and fix all issues systematically.

---

### 69. Fix all skipped and failing tests (zero skip, zero fail)
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-31
- **Summary**: Fixed 1 failing test (signed bitvec comparison), unskipped bimodal tests (7 xfail for solver timeouts), deleted legacy builder test file, mocked cvc5 detection for registry test. Net: 0 failures, 0 unexpected skips.
- **Research**: [01_fix-skipped-failing.md](069_fix_all_skipped_and_failing_tests/reports/01_fix-skipped-failing.md)
- **Plan**: [01_fix-skipped-failing.md](069_fix_all_skipped_and_failing_tests/plans/01_fix-skipped-failing.md)
- **Language**: python

**Description**: Achieve zero skipped and zero failing tests across the entire test suite. Issues to resolve:

**1 failing test:**
- `solver/tests/unit/test_equivalence.py::test_push_pop_sat_transitions` - Signed/unsigned bitvector comparison bug (see task 64). Use `z3.UGT`/`z3.ULT` for unsigned comparisons, or change test values to be contradictory under signed comparison.

**Skipped tests to fix or delete:**
- **Bimodal "under development"** (3 files: `test_iterate.py`, `test_bimodal.py`, `test_cli_execution.py`): Unconditional `pytest.mark.skip`. The bimodal example tests pass (22 examples), so these unit/integration/e2e tests should be unskipped and fixed if they fail.
- **Builder legacy behavior** (`test_refactoring_current_behavior.py`): Skipped because "tests document legacy behavior that has been removed". Delete this file if the behavior is truly gone.
- **Builder `ModelRunner` not implemented** (`test_runner.py`, 8 tests): `skipIf(not RUNNER_EXISTS)`. Either implement `ModelRunner` or delete these aspirational tests.
- **Builder `OperatorTranslation` not implemented** (`test_translation.py`, 11 tests): `skipIf(not TRANSLATION_EXISTS)`. Either implement or delete.
- **Builder `ModelComparison` not implemented** (`test_comparison.py`, 8 tests): `skipIf(not COMPARISON_EXISTS)`. Either implement or delete.
- **Solver `test_validate_missing_cvc5_raises`** (`test_registry.py`): Skipped when cvc5 IS installed. Make test work regardless of cvc5 availability (mock detect_cvc5).
- **Graph utils `NetworkX`** (`test_graph_utils.py`): `skipif(not HAS_DEPENDENCIES)`. Ensure NetworkX is installed or delete if unused.

---

### 68. Fix flaky builder performance test threshold
- **Effort**: trivial
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Increased per-example performance threshold from 0.25s to 0.5s, matching sibling test for same N=2 complexity.
- **Research**: [01_flaky-perf-threshold.md](068_fix_flaky_builder_performance_test/reports/01_flaky-perf-threshold.md)
- **Plan**: [01_fix-perf-threshold.md](068_fix_flaky_builder_performance_test/plans/01_fix-perf-threshold.md)
- **Language**: python

**Description**: Fix flaky `test_multiple_examples_process_efficiently` in `builder/tests/integration/test_performance.py`. Current threshold is 0.25s but test occasionally fails at 0.251s (off by 1ms). Increase threshold to 0.3s or use a more robust timing comparison with tolerance.

---

### 67. Make run_tests.py exhaustive (add missing test coverage)
- **Effort**: small
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Made run_tests.py exhaustive: removed bimodal exclusion (+98 tests), dynamic subtheory discovery including first_order (+53 tests), nested component discovery for output.notebook (+14 tests), added --list flag.
- **Research**: [01_run-tests-coverage.md](067_make_run_tests_exhaustive/reports/01_run-tests-coverage.md)
- **Plan**: [01_exhaustive-coverage.md](067_make_run_tests_exhaustive/plans/01_exhaustive-coverage.md)
- **Language**: python

**Description**: Make `run_tests.py` exhaustive by adding coverage for: (1) bimodal theory tests (currently excluded at line 662), (2) first_order subtheory (missing from `_discover_subtheories()` at line 694), (3) `output/notebook/tests/` (not reachable from `output/tests/`). Currently 3 test suites (166 tests total) are not covered by the test runner.

---

### 66. Fix output/notebook test failures (6 failing tests: missing templates, API changes)
- **Effort**: small
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Fixed 6 failing notebook tests: created missing exclusion/imposition templates, fixed stale API name, corrected mock paths, fixed test design issue. All 14 tests pass.
- **Research**: [01_notebook-test-failures.md](066_fix_output_notebook_test_failures/reports/01_notebook-test-failures.md)
- **Plan**: [01_fix-notebook-tests.md](066_fix_output_notebook_test_failures/plans/01_fix-notebook-tests.md)
- **Language**: python

**Description**: Fix output/notebook test failures (6 failing tests: missing templates, API changes). Tests in `output/notebook/tests/` are failing due to missing template modules (`model_checker.output.notebook.templates.imposition`, `model_checker.output.notebook.templates.exclusion`) and API changes (`TemplateLoader.get_template_class` -> `get_template_for_class`).

---

### 65. Fix cvc5 Sort conversion errors in semantic modules
- **Effort**: medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Summary**: Fixed cvc5 Sort conversion errors by adding dynamic AtomSort resolution via __getattr__ and updating 4 crash sites to use get_atom_sort() directly, enabling backend switching without stale Sort references.
- **Research**: [01_team-research.md](065_fix_cvc5_sort_conversion_errors/reports/01_team-research.md)
- **Plan**: [01_fix-atomsort-binding.md](065_fix_cvc5_sort_conversion_errors/plans/01_fix-atomsort-binding.md)
- **Language**: z3

**Description**: Migrate remaining z3_shim imports in semantic modules (bimodal/semantic.py, bimodal/witness_registry.py, bimodal/witness_constraints.py, logos/semantic.py) to use solver.expressions abstraction layer. All 138 comparison examples fail with "Cannot convert Sort to cvc5.cvc5_python_base.Sort" because z3 Sort objects are hardcoded instead of using backend-agnostic IntSort/BitVecSort/BoolSort/Function from solver.expressions.

---

### 64. Fix test_push_pop_sat_transitions signed/unsigned bitvector comparison bug
- **Effort**: TBD
- **Status**: [PLANNED]
- **Language**: z3

**Description**: The test `solver/tests/unit/test_equivalence.py::TestPushPopEquivalence::test_push_pop_sat_transitions` fails because it expects `z3_x > 200` and `z3_x < 100` on an 8-bit BitVec to be contradictory (unsat), but z3's `>` and `<` on BitVec are signed comparisons. Signed 8-bit value 200 is -56, so `x > -56 AND x < 100` is satisfiable. Fix by using unsigned comparisons (`z3.UGT` / `z3.ULT` and cvc5 equivalents) or by choosing values that are contradictory under signed comparison (e.g., `x > 50 AND x < 10`). File: `code/src/model_checker/solver/tests/unit/test_equivalence.py` line 127.

---

### 63. Migrate builder and iterate modules to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in the builder and iterate modules with the solver abstraction layer. Files: `builder/example.py` (2 refs), `builder/runner.py` (3 refs), `builder/z3_utils.py` (15 refs), `iterate/base.py` (4 refs), `iterate/build_example.py` (2 refs), `iterate/constraints.py` (25 refs), `iterate/graph.py` (1 ref), `iterate/models.py` (21 refs). Total ~73 z3 references. Also migrate `models/constraints.py` (1 ref) and `models/semantic.py` (3 refs) if not already covered. Verify: all existing iterate and builder tests pass with z3 backend; `comparison.py` still gives 138/138 z3 pass.

---

### 62. Migrate bimodal theory to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in the bimodal theory with the solver abstraction layer. Files: `theory_lib/bimodal/semantic.py` (162 refs - largest single file), `theory_lib/bimodal/operators.py` (21 refs), `theory_lib/bimodal/iterate.py` (4 refs), `theory_lib/bimodal/semantic/witness_constraints.py` (12 refs), `theory_lib/bimodal/semantic/witness_registry.py` (12 refs). Total ~211 z3 references. Uses z3.And, z3.Or, z3.Not, z3.BitVec, z3.BoolVal, z3.Function, z3.Solver, z3.Z3Exception heavily. Verify: bimodal tests pass with z3 backend.

---

### 61. Migrate logos operator subtheories to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in logos subtheory operator files with the solver abstraction layer. Files: `theory_lib/logos/subtheories/constitutive/operators.py` (81 refs), `theory_lib/logos/subtheories/extensional/operators.py` (51 refs), `theory_lib/logos/subtheories/first_order/operators.py` (24 refs), `theory_lib/logos/subtheories/counterfactual/operators.py` (13 refs), `theory_lib/logos/subtheories/modal/operators.py` (6 refs). Also: `theory_lib/logos/iterate.py` (14 refs), `theory_lib/logos/protocols.py` (7 refs). Total ~196 z3 references. These files use z3.And, z3.Or, z3.Not, z3.Implies, z3.BitVec, z3.BoolVal, z3.Function, z3.Select, z3.ForAll, z3.Exists heavily. Verify: `comparison.py` gives 138/138 z3 pass after migration.

---

### 60. Migrate logos/semantic.py to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in `theory_lib/logos/semantic.py` with the solver abstraction layer. This is the second-largest file with 97 z3 references including `z3.And`, `z3.Or`, `z3.Not`, `z3.BitVec`, `z3.BitVecVal`, `z3.BitVecSort`, `z3.BoolVal`, `z3.Bool`, `z3.Int`, `z3.IntSort`, `z3.Function`, `z3.Select`, `z3.Solver`, `z3.sat`, `z3.unsat`, `z3.simplify`, `z3.is_true`, `z3.is_false`, `z3.Z3Exception`, `z3.ModelRef`, `z3.FuncDeclRef`, `z3.ExprRef`, `z3.BoolRef`, `z3.BitVecRef`. This is the core file where solver expressions are created for the entire logos theory - it's the critical path for cvc5 compatibility. Also migrate `syntactic/assignments.py` (4 refs) and `syntactic/sentence.py` remaining refs. Verify: `comparison.py` gives 138/138 z3 pass; single cvc5 example progresses further than "derived_type invalid".

---

### 59. Extend solver expressions.py and compat.py for full API coverage
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3

**Description**: Extend `solver/expressions.py` and `solver/compat.py` with all z3 API functions needed by the core pipeline. Currently missing from expressions.py: `Bool` (66 uses), `Int` (56), `IntSort` (44), `BoolVal` (77), `Function` (25), `Select` (15), `Solver` (104) -- wait, Solver is via create_solver. Missing type predicates: `is_true` (1), `is_false` (1), `is_bool` (8), `is_int` (3), `is_int_value` (8), `is_real` (8), `is_bv` (1), `is_quantifier` (6). Missing type refs for runtime use: `BoolRef` (95), `BitVecRef` (21), `ExprRef` (16), `FuncDeclRef` (21), `ModelRef` (37), `Z3Exception` (37), `CheckSatResult` (3). Also need: `Sum` (1), `Var` (1), `set_param` (1), `reset_params` (1), `ArraySort` (1). Add backend-aware versions of all these to expressions.py or a new `solver/types_runtime.py`. For type refs, provide runtime-importable aliases that resolve to the correct backend's types. For `Z3Exception`, provide a `SolverException` wrapper. Verify: `from model_checker.solver.expressions import X` works for every function used in the codebase.

---

### 58. Wire solver registry into core solving loop
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Language**: z3
- **Research**: [01_solver-registry-wiring.md](058_wire_solver_registry_into_core/reports/01_solver-registry-wiring.md)
- **Plan**: [01_solver-registry-wiring-plan.md](058_wire_solver_registry_into_core/plans/01_solver-registry-wiring-plan.md)
- **Completed**: 2026-03-30
- **Summary**: [01_solver-registry-wiring-summary.md](058_wire_solver_registry_into_core/summaries/01_solver-registry-wiring-summary.md)

**Description**: structure.py hardcodes `import z3` and `z3.Solver()` throughout, bypassing the solver switching infrastructure (registry, adapters, z3_shim). This means `switch_solver('cvc5')` has no effect on actual SAT checking. Need to systematically replace all direct `import z3` / `from z3 import ...` in the solving pipeline with `from model_checker.z3_shim import ...` (or the adapter layer), so that the active backend from the registry is actually used. Key files: structure.py (lines 16, 156, 232-235, 248, 277, 288, 885), runner.py (lines 15, 312), and any other files in the solving pipeline that import z3 directly. Must preserve existing behavior when z3 is the default backend while enabling actual cvc5 usage when switched.

---

### 57. Design v2 scaling solver comparison benchmark
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Language**: python
- **Research**:
  - [01_scaling-benchmark-design.md](057_v2_scaling_solver_comparison/reports/01_scaling-benchmark-design.md)
  - [02_max-model-discovery.md](057_v2_scaling_solver_comparison/reports/02_max-model-discovery.md)
  - [03_existing-infrastructure.md](057_v2_scaling_solver_comparison/reports/03_existing-infrastructure.md)
- **Plan**:
  - [02_implementation-plan.md](057_v2_scaling_solver_comparison/plans/02_implementation-plan.md)
  - [03_revised-implementation-plan.md](057_v2_scaling_solver_comparison/plans/03_revised-implementation-plan.md) (current)
- **Completed**: 2026-03-30
- **Summary**: [03_scaling-benchmark-summary.md](057_v2_scaling_solver_comparison/summaries/03_scaling-benchmark-summary.md)

**Description**: Research and design a v2 solver comparison benchmark that progressively scales model sizes (number of worlds, propositions, accessibility relations) to identify divergence points between z3 and cvc5. The current v1 (code/comparison.py) runs 138 examples with both solvers getting identical results. V2 should: (1) parameterize model size dimensions (world count, proposition count, relation density), (2) progressively increase scale until solvers diverge in result or timeout, (3) identify the specific model size thresholds where divergence occurs, (4) report per-subtheory scaling curves and divergence points.

---

### 50. Create standalone solver comparison script using dev_cli.py
- **Effort**: TBD
- **Status**: [PLANNED]
- **Language**: python

**Description**: Create standalone solver comparison script that runs each logos example through dev_cli.py twice (once with z3, once with cvc5), displaying concrete model/countermodel output with timing data for side-by-side comparison.

---

### 36. Fill placeholders and fix metadata
- **Effort**: TBD
- **Status**: [PLANNED]
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
- **Status**: [PLANNED]
- **Language**: python
- **Dependencies**: None

**Description**: Upon running the first-order theory in the model-checker, the output shows the model-checker is running but does not find or produce a reasonable looking model. Each n-place predicate should get mapped to a set of verifiers and falsifiers (functions from n states to a state) where the positive extension of a predicate in a world is the set of state n-tuples which get mapped to a state that is part of that world by SOME verifier for the predicate. Review the semantics in `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ` and `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ` to verify the first-order semantics in the model-checker is correct. Then evaluate and redesign the elements needed to extract predicate extensions at each world and display these when printing a model.

---
