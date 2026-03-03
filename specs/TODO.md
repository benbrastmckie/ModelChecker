---
next_project_number: 20
---

# Task List

## Tasks

### 19. Investigate remaining first-order theorem failures: spurious countermodels in FO_TH_1-4 and FO_TH_6-8, and bare variable TypeError in FO_TH_7
- **Effort**: Medium
- **Status**: [PLANNED]
- **Research**: [research-001.md](019_investigate_first_order_theorem_failures/reports/research-001.md)
- **Plan**: [implementation-001.md](019_investigate_first_order_theorem_failures/plans/implementation-001.md)
- **Language**: python
- **Dependencies**: Task #18

**Description**: Investigate remaining first-order theorem failures: spurious countermodels in FO_TH_1-4 and FO_TH_6-8, and bare variable TypeError in FO_TH_7

### 18. Fix first-order subtheory: 6 interconnected bugs causing crashes and wrong semantic results
- **Effort**: Large
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](018_fix_first_order_subtheory_bugs/summaries/implementation-summary-20260302.md)
- **Language**: python
- **Research**: [research-001.md](018_fix_first_order_subtheory_bugs/reports/research-001.md)
- **Plan**: [implementation-001.md](018_fix_first_order_subtheory_bugs/plans/implementation-001.md)

**Description**: Fix first-order subtheory: 6 interconnected bugs causing crashes and wrong semantic results

### 17. Fix remaining uppercase directory references missed by task 16
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](017_fix_remaining_uppercase_directory_references/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Dependencies**: Task #16
- **Research**: [research-001.md](017_fix_remaining_uppercase_directory_references/reports/research-001.md)
- **Plan**: [implementation-001.md](017_fix_remaining_uppercase_directory_references/plans/implementation-001.md)

**Description**: Follow-up to task 16. Neovim keybinding `<leader>rm` fails with "Could not find Code/dev_cli.py in project" indicating some uppercase directory references were not updated. Carefully research all remaining references throughout the repository that still need to be fixed.

### 16. Update all references to renamed lowercase directories
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](016_update_references_to_renamed_lowercase_directories/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Research**: [research-001.md](016_update_references_to_renamed_lowercase_directories/reports/research-001.md)
- **Plan**: [implementation-001.md](016_update_references_to_renamed_lowercase_directories/plans/implementation-001.md)

**Description**: Review recent git commits to identify which directory names were changed to lowercase. Systematically update all references in documentation and source code to match the new paths and prevent breakage.

### 15. Verify quantifier semantics match Logos manual
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](015_verify_quantifier_semantics_match_logos_manual/summaries/implementation-summary-20260302.md)
- **Language**: python
- **Dependencies**: Task #11
- **Research**: [research-001.md](015_verify_quantifier_semantics_match_logos_manual/reports/research-001.md), [research-002.md](015_verify_quantifier_semantics_match_logos_manual/reports/research-002.md)
- **Plan**: [implementation-002.md](015_verify_quantifier_semantics_match_logos_manual/plans/implementation-002.md)

**Description**: Check that ForAllOperator and ExistsOperator semantics in first-order operators.py follow the Logos manual (02-constitutive.typ and 03-dynamics.typ) where lambda handles all variable binding. Ensure ExistsOperator is defined in terms of ForAllOperator. Add `\all` and `\some` abbreviations that combine lambda binding with quantification. Add arity validation checks with meaningful error messages for formation problems.

### 14. Auto-discover predicates, functions, and constants from formulas
- **Effort**: Medium-Large
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](014_auto_discover_predicates_functions_constants/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Dependencies**: Task #10
- **Research**: [research-001.md](014_auto_discover_predicates_functions_constants/reports/research-001.md), [research-002.md](014_auto_discover_predicates_functions_constants/reports/research-002.md), [research-003.md](014_auto_discover_predicates_functions_constants/reports/research-003.md)
- **Plan**: [implementation-004.md](014_auto_discover_predicates_functions_constants/plans/implementation-004.md)

**Description**: Replace manual registration of predicates, functions, and constants with automatic discovery from parsed formulas. Unify sentence letters as zero-arity predicates (`P[]` notation). When parsing a formula, collect all predicate applications (with their arities), function symbols (with their arities), and constants. Auto-register these with the semantics before evaluation. This extends the existing sentence letter auto-discovery pattern to the full first-order vocabulary, eliminating the need for explicit `register_predicate()`, `register_function()`, and `register_constant()` calls.

### 13. Strengthen first-order parser test coverage
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](013_strengthen_first_order_parser_test_coverage/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Dependencies**: Task #9, Task #14
- **Research**: [research-001.md](013_strengthen_first_order_parser_test_coverage/reports/research-001.md)
- **Plan**: [implementation-001.md](013_strengthen_first_order_parser_test_coverage/plans/implementation-001.md)

**Description**: Strengthen test coverage for first-order parser and vocabulary discovery. Original scope (tasks 7-9): add integration tests connecting term algebra to parser (free_variables on parsed formulas), expand lambdaApp tests to cover substitute(), add parser error handling tests (malformed input: missing body after quantifier, unclosed brackets, invalid variable names), and add TDD-conformant placeholder tests for task 7 operator stubs. Extended scope (task 14): add comprehensive tests for the new syntax convention (bare identifiers as constants, `[]` required for predicates), vocabulary auto-discovery edge cases, arity validation error paths, and semantic TypeError for constant truth evaluation.

### 12. Create first-order examples and integration tests
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](012_first_order_examples_and_tests/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Dependencies**: Task #11
- **Research**: [research-001.md](012_first_order_examples_and_tests/reports/research-001.md), [research-002.md](012_first_order_examples_and_tests/reports/research-002.md)
- **Plan**: [implementation-001.md](012_first_order_examples_and_tests/plans/implementation-001.md)

**Description**: Populate `examples.py` with theorem examples (FO_TH_1 through FO_TH_8: universal distribution, existential distribution, quantifier duality, reflexivity/symmetry/transitivity of identity, Leibniz's Law, lambda beta reduction) and countermodel examples (FO_CM_1 through FO_CM_4: universal to particular, existential instantiation, quantifier scope ambiguity, hyperintensional collapse). Create comprehensive test suite in `tests/test_first_order_examples.py` covering all operators and their interaction with extensional/modal operators.

### 11. Implement first-order operators (Lambda, ForAll, Exists, Identity)
- **Effort**: Medium-Large
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Language**: general
- **Dependencies**: Task #10
- **Research**: [research-001.md](011_implement_first_order_operators/reports/research-001.md)

**Description**: Implement all four first-order operators in `operators.py`. `LambdaOperator`: property formation via variable binding — lambda application `(lambda v.phi)(t)` updates assignment with term denotation and evaluates body; implement `true_at`, `false_at`, `extended_verify`, `extended_falsify`, `find_verifiers_and_falsifiers`. `ForAllOperator`: universal quantification with Z3 constraint generation for finite domain — verifies when all v-variant assignments yield verifiers that fuse into the current state. `ExistsOperator`: defined operator as `not forall v. not phi`. `FirstOrderIdentityOperator`: binary operator on terms, verified at null state when denotations coincide; implement reflexivity, symmetry, transitivity properties.

### 10. Implement variable assignment semantics
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-02
- **Summary**: [implementation-summary-20260302.md](010_implement_variable_assignment_semantics/summaries/implementation-summary-20260302.md)
- **Language**: general
- **Dependencies**: Task #9
- **Research**: [research-001.md](010_implement_variable_assignment_semantics/reports/research-001.md)
- **Plan**: [implementation-001.md](010_implement_variable_assignment_semantics/plans/implementation-001.md)

**Description**: Create infrastructure for variable assignments (`sigma: Var -> State`), v-variant assignments (`sigma[s/v]`), and recursive term denotation computation (`[[t]]^sigma_M`). Extend the semantic evaluation context to thread variable assignments through recursive evaluation. Implement predicate interpretation functions: `|F|+, |F|- : S^n -> P(S)` mapping argument tuples to verifier/falsifier sets. Add Z3 constraint support for finite domain quantification including domain enumeration and assignment-variant generation. Integrate with existing semantic evaluation machinery.

### 9. Extend parser for first-order variable and term syntax
- **Effort**: Large
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260301.md](009_extend_parser_for_first_order_syntax/summaries/implementation-summary-20260301.md)
- **Language**: general
- **Dependencies**: Task #8
- **Research**: [research-001.md](009_extend_parser_for_first_order_syntax/reports/research-001.md), [research-002.md](009_extend_parser_for_first_order_syntax/reports/research-002.md)
- **Plan**: [implementation-002.md](009_extend_parser_for_first_order_syntax/plans/implementation-002.md)

**Description**: Modify `syntactic/syntax.py` and `syntactic/sentence.py` (and related modules) to recognise first-order syntax. Add recognition for: variables (`v`, `v_1`, `v_2`, ...); individual constants (`a`, `b`, `c`); function applications (`f(t_1,...,t_n)`); n-ary predicates with term arguments (`F(x,y)`); lambda binding syntax (`(lambda v.phi)(t)`); quantifier syntax (`forall v.phi`, `exists v.phi`). Handle bound vs free variable scoping correctly and integrate with the existing `Sentence` / `OperatorCollection` pipeline. Write unit tests for each new syntactic form.

### 8. Implement term algebra data structures
- **Effort**: Medium
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260301.md](008_implement_term_algebra_data_structures/summaries/implementation-summary-20260301.md)
- **Language**: general
- **Dependencies**: Task #7
- **Research**: [research-001.md](008_implement_term_algebra_data_structures/reports/research-001.md)
- **Plan**: [implementation-001.md](008_implement_term_algebra_data_structures/plans/implementation-001.md)

**Description**: Implement Python classes for the first-order term algebra, either in a new `terms.py` inside the `first-order/` subtheory or within the syntactic module. Classes needed: `Variable` (with name, e.g. `v_1`); `Constant` (0-place function symbol); `FunctionApplication` (n-place function symbol applied to n terms). Implement `free_variables(t)` returning the set of free variables in a term, and `substitute(term, replacement, var)` implementing capture-avoiding substitution `t[s/v]`. Include full unit test coverage following TDD principles.

### 7. Create first-order module scaffolding
- **Effort**: Small
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260301.md](007_create_first_order_module_scaffolding/summaries/implementation-summary-20260301.md)
- **Language**: general
- **Dependencies**: None
- **Research**: [research-001.md](007_create_first_order_module_scaffolding/reports/research-001.md)
- **Plan**: [implementation-001.md](007_create_first_order_module_scaffolding/plans/implementation-001.md)

**Description**: Create the basic module structure at `Code/src/model_checker/theory_lib/logos/subtheories/first-order/` following the pattern of the extensional and constitutive subtheories. Files to create: `__init__.py` (module init with public API stubs), `operators.py` (empty operator stubs with docstrings), `examples.py` (empty with planned example categories listed as comments), `tests/__init__.py`, `tests/test_first_order_examples.py` (failing placeholder test). Verify the module is importable and the package is discoverable by the theory loader.

### 6. Identify Python and Z3 MCP tools and integrate into .claude/ subagents
- **Effort**: 2-4 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260301.md](006_identify_python_z3_mcp_integrate_subagents/summaries/implementation-summary-20260301.md)
- **Language**: meta
- **Dependencies**: None
- **Research**: [research-001.md](006_identify_python_z3_mcp_integrate_subagents/reports/research-001.md), [research-002.md](006_identify_python_z3_mcp_integrate_subagents/reports/research-002.md)
- **Plan**: [implementation-001.md](006_identify_python_z3_mcp_integrate_subagents/plans/implementation-001.md)

**Description**: Identify which Python and Z3 MCP servers or other tools might be helpful for implementing the first-order and spatial modules of the logos/ theory in the model-checker. Investigate context7 MCP for documentation lookup. Integrate these tools into Python and Z3 research and implementation subagents in the .claude/ agent system.

### 5. Create spatial reasoning README for logos subtheory
- **Effort**: 2 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260228.md](005_logos_spatial_readme/summaries/implementation-summary-20260228.md)
- **Research**: [research-001.md](005_logos_spatial_readme/reports/research-001.md)
- **Plan**: [implementation-001.md](005_logos_spatial_readme/plans/implementation-001.md)
- **Language**: general
- **Dependencies**: None

**Description**: Draw on /home/benjamin/Projects/Logos/Theory/typst/manual/chapters/06-spatial.typ in order to outline the scope and ambitions for adding a spatial reasoning module to the logos/ in this model-checker project, creating a detailed overview in /home/benjamin/Projects/ModelChecker/Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md that conforms to repo documentation standards.

### 4. Create first-order logic README for logos subtheory
- **Effort**: 2.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2026-03-01
- **Summary**: [implementation-summary-20260228.md](004_logos_first_order_readme/summaries/implementation-summary-20260228.md)
- **Research**: [research-001.md](004_logos_first_order_readme/reports/research-001.md)
- **Plan**: [implementation-001.md](004_logos_first_order_readme/plans/implementation-001.md)
- **Language**: general
- **Dependencies**: None

**Description**: Draw on /home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ to outline the scope and ambitions for adding first-order logic to logos/ in this model-checker project, creating a detailed overview in /home/benjamin/Projects/ModelChecker/Code/src/model_checker/theory_lib/logos/subtheories/first-order/README.md that conforms to repo documentation standards.

### 3. Port paper overview content to LaTeX paper
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-02-18
- **Summary**: [implementation-summary-20260218.md](003_port_paper_overview_to_latex/summaries/implementation-summary-20260218.md)
- **Plan**: [implementation-001.md](003_port_paper_overview_to_latex/plans/implementation-001.md)
- **Research**: [research-001.md](003_port_paper_overview_to_latex/reports/research-001.md), [research-002.md](003_port_paper_overview_to_latex/reports/research-002.md)
- **Language**: latex
- **Dependencies**: Task #1

**Description**: Port the content given in /home/benjamin/Projects/ModelChecker/latex/markdown/paper_overview.md over to /home/benjamin/Projects/ModelChecker/latex/paper.tex in order to conform to journal standards.

### 2. Review and improve LaTeX context files for sn-article template
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-02-18
- **Summary**: [implementation-summary-20260218.md](002_review_improve_latex_context_files/summaries/implementation-summary-20260218.md)
- **Plan**: [implementation-001.md](002_review_improve_latex_context_files/plans/implementation-001.md)
- **Research**: [research-001.md](002_review_improve_latex_context_files/reports/research-001.md)
- **Language**: meta
- **Dependencies**: Task #1

**Description**: Building on task 1, review all LaTeX-specific context files in .claude/context/ (if any) in order to revise/improve those files to fully specify all relevant LaTeX standards and details for this project which uses the sn-article template. The aim is for these context files to match the others in being clear, complete, and yet concise, while also being loaded in exactly the right places (e.g., by the various LaTeX subagents) in order to improve performance and consistency of implementation. See latex/README.md for relevant overview.

### 1. Create ModelChecker LaTeX directory for Springer journal paper
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-02-18
- **Summary**: [implementation-summary-20260218.md](001_latex_springer_paper_setup/summaries/implementation-summary-20260218.md)
- **Plan**: [implementation-001.md](001_latex_springer_paper_setup/plans/implementation-001.md)
- **Research**: [research-001.md](001_latex_springer_paper_setup/reports/research-001.md)
- **Language**: latex
- **Dependencies**: None

**Description**: Create a ModelChecker/latex/ directory similar to /home/benjamin/Projects/Logos/Theory/latex/ but do not use subfiles, focusing instead on creating a single paper with the template /home/benjamin/Downloads/v13/sn-article-template/sn-article.tex and other files included in this directory. Carefully research what is required for submission as indicated in /home/benjamin/Downloads/v13/sn-article-template/sn-article.tex and https://link.springer.com/journal/10817/submission-guidelines provided by the journal.

<!-- New tasks are prepended below this line -->
