---
next_project_number: 42
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 41. Final conciseness pass: throat-clearing, roadmap, narrative flow
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: latex
- **Dependencies**: Task #40

**Description**: Final polish pass on `latex/paper.tex` for publication readiness. Three focus areas:

1. **Global throat-clearing removal** (topic 7): Search-and-delete filler phrases throughout the paper: "it is worth noting that", "it should be observed that", "it bears mentioning that", "in the remainder of this section", "as one might expect", "it is perhaps unsurprising that". State claims directly without preamble. (~230 words savings with zero content loss.)

2. **Trim paper roadmap** (topic 16): The section-by-section preview in the introduction (Sec 1.3, "Paper Roadmap" paragraph, lines ~285-293) is verbose. Cut to 2-3 sentences or remove entirely -- JAR reviewers find sections from the table of contents.

3. **Narrative flow improvements** (topic 17): Add brief design-rationale paragraphs at key transition points: (a) at the start of Section 3 (Modularity) explaining why modularity matters for this framework; (b) at the start of the Logos case study (Sec 6) explaining what the case study is meant to demonstrate beyond what precedes it. Ensure each section opening motivates what follows rather than just stating what it covers.

---

### 40. Trim code listings, over-explanation, and aspirational content
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: latex
- **Dependencies**: Task #39

**Description**: Targeted verbosity reduction in `latex/paper.tex` across three categories:

1. **Trim code listings** (topic 5): Show only semantically interesting methods in code listings. Use ellipsis (`...`) for boilerplate (`__init__`, `__repr__`, etc.). Where multiple operator classes follow the same pattern, show one representative example and note "analogous definitions for other operators." Cut repeated structural patterns. (~900-1100 words savings.)

2. **Cut over-explanation for JAR audience** (topic 6): Remove elementary explanations that JAR readers don't need: basic Boolean/lattice definitions stated at textbook level, Python OOP concepts ("Python's class system allows us to define..."), and introductory Z3 descriptions. Replace with concise one-sentence reminders or citations. (~450 words savings.)

3. **Condense TheoryLib vision and future work** (topics 8, 9): Section 5 (TheoryLib) includes community model, contribution pathways, incentives, quality standards, and BibTeX citation format that read like a project README rather than a journal paper. Keep the core architectural vision and the comparative research platform concept; cut aspirational community-building content. Similarly, cut generic future work items ("extend to other logics", "improve performance", "add a GUI") and keep only technically specific future directions.

---

### 39. Eliminate structural redundancy across sections
- **Effort**: TBD
- **Status**: [NOT STARTED]
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
