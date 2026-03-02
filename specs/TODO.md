---
next_project_number: 13
---

# Task List

## Tasks

### 12. Create first-order examples and integration tests
- **Effort**: Medium
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #11

**Description**: Populate `examples.py` with theorem examples (FO_TH_1 through FO_TH_8: universal distribution, existential distribution, quantifier duality, reflexivity/symmetry/transitivity of identity, Leibniz's Law, lambda beta reduction) and countermodel examples (FO_CM_1 through FO_CM_4: universal to particular, existential instantiation, quantifier scope ambiguity, hyperintensional collapse). Create comprehensive test suite in `tests/test_first_order_examples.py` covering all operators and their interaction with extensional/modal operators.

### 11. Implement first-order operators (Lambda, ForAll, Exists, Identity)
- **Effort**: Medium-Large
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #10

**Description**: Implement all four first-order operators in `operators.py`. `LambdaOperator`: property formation via variable binding — lambda application `(lambda v.phi)(t)` updates assignment with term denotation and evaluates body; implement `true_at`, `false_at`, `extended_verify`, `extended_falsify`, `find_verifiers_and_falsifiers`. `ForAllOperator`: universal quantification with Z3 constraint generation for finite domain — verifies when all v-variant assignments yield verifiers that fuse into the current state. `ExistsOperator`: defined operator as `not forall v. not phi`. `FirstOrderIdentityOperator`: binary operator on terms, verified at null state when denotations coincide; implement reflexivity, symmetry, transitivity properties.

### 10. Implement variable assignment semantics
- **Effort**: Medium
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #9

**Description**: Create infrastructure for variable assignments (`sigma: Var -> State`), v-variant assignments (`sigma[s/v]`), and recursive term denotation computation (`[[t]]^sigma_M`). Extend the semantic evaluation context to thread variable assignments through recursive evaluation. Implement predicate interpretation functions: `|F|+, |F|- : S^n -> P(S)` mapping argument tuples to verifier/falsifier sets. Add Z3 constraint support for finite domain quantification including domain enumeration and assignment-variant generation. Integrate with existing semantic evaluation machinery.

### 9. Extend parser for first-order variable and term syntax
- **Effort**: Large
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #8

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
