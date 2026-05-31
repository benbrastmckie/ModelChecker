---
next_project_number: 107
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 106. Architecture review of bimodal refactor plan (tasks 99-105)
- **Effort**: large
- **Status**: [RESEARCHED]
- **Task Type**: python
- **Research**:
  - [106_architecture_review_refactor/reports/01_team-research.md]
  - [106_architecture_review_refactor/reports/02_team-research.md]
  - [106_architecture_review_refactor/reports/03_clean-break-architecture.md]

**Description**: Deep architectural review of the planned bimodal ModelChecker refactor (tasks 99-105). Study the current ModelChecker codebase (code/src/model_checker/), the BimodalHarness OracleProvider protocol (bimodal_harness/oracle/protocol.py in /home/benjamin/Projects/BimodalHarness/), the BimodalLogic interface expectations, and the technical memo (/home/benjamin/Projects/Logos/Vision/shared/strategy/01-overview/03-technical_memo.typ). Evaluate: (1) whether the proposed task decomposition and ordering is optimal, (2) whether the package boundary and public API surface are well-drawn, (3) whether the formula JSON translation approach handles all edge cases (defined operators, operator precedence, round-trip fidelity), (4) whether the countermodel serialization maps cleanly to BimodalStructure's extract_model_elements output, (5) whether tasks 99 (audit) and 100 (strip) should be merged or resequenced, (6) whether the builder/output/settings simplification in task 104 is scoped correctly or risks breaking the Z3 solving pipeline, (7) any missing tasks (e.g., documentation, CI/CD, version pinning against BimodalHarness). Produce a report with concrete architectural recommendations and revised task descriptions where warranted. The end product is updated descriptions and dependencies for tasks 99-105.

### 105. Integration testing and validation
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103, 104

**Description**: End-to-end testing against the OracleProvider protocol and BimodalHarness compatibility. Protocol compliance: verify all 5 properties, both methods, return format matches SimpleCountermodel/StructuredCountermodel schemas. Countermodel correctness: regression test against the existing 43-example bimodal test suite — refactored package must produce identical valid/invalid classifications. Cross-signal scenarios: use BimodalHarness's SPOT_CHECK_FORMULAS (10 known-invalid formulas from _mock.py) as ground truth for validate_self. Edge cases: timeout handling (formula that exceeds timeout_ms), unsupported frame_class ("Dense"→None), malformed formula JSON. Entry-point discovery: verify pip install bmlogic-oracle followed by OracleRegistry.discover() finds the provider. Z3 isolation: run find_countermodel() 100+ times in sequence, verify no state leakage or memory growth. G/H equivalence regression: formulas using derived G/H must produce countermodels equivalent to direct G/H encoding.

### 104. Dead-code cleanup and thin CLI
- **Effort**: small
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103

**Description**: With OracleProvider working as the primary public interface, remove dead code and add a thin CLI. Remove unused builder components: project scaffolding, multi-theory comparison, theory template generation. Simplify output/: remove interactive prompts, notebook templates, progress bars (OracleProvider returns dicts, not formatted output). Simplify settings/: remove file-based settings parsing not used by programmatic pipeline. Remove logos-specific branching remnants in builder/runner.py. Add thin CLI: bmlogic-oracle check '<formula_json>' for standalone countermodel checking. Do NOT change any code that OracleProvider depends on — only remove unreachable code.

### 103. OracleProvider implementation with programmatic pipeline
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 101, 102

**Description**: Implement the OracleProvider protocol class with a new programmatic solving pipeline (current code starts from files on disk — no programmatic path exists). New pipeline: formula_json → json_to_prefix() → Sentence.from_prefix() → BimodalSemantics(N,M) → Syntax(operators, [sentence]) → ModelConstraints → BimodalStructure → Z3 solve → extract model → serialize. OracleProvider properties: provider_id="bmlogic_z3_base_v1", provider_version (semver), semantics_version (pinned to BimodalLogic), supported_frame_classes=frozenset({"Base"}), capabilities dict. find_countermodel(formula_json, frame_class, timeout_ms): implements full pipeline, returns None on UNSAT/timeout/unsupported frame_class. Countermodel serialization: both SimpleCountermodel (trueAtoms/falseAtoms from evaluating atoms at eval point) and StructuredCountermodel (world_histories, task_relation, truth_valuation from extract_model_elements()). Implement structured from the start. validate_self(spot_check_formulas): must find countermodels for all provided known-invalid formulas. Z3 context isolation: clean Z3 state between find_countermodel() calls, fresh solver instances per call, address memory management for repeated instantiation. semantics_version contract: pin to specific BimodalLogic semantics version. Finalize entry point in pyproject.toml.

### 102. Formula JSON translation with G/H equivalence verification
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 100

**Description**: Implement one-directional JSON→internal formula translation with semantic equivalence verification. Create json_to_prefix(formula_json) function mapping 6 JSON tags to internal prefix-list format: atom→variable, bot→\bot, imp→\rightarrow, box→\Box, untl→U, snce→S. Create Sentence.from_prefix(prefix_list, operators) classmethod that constructs Sentence objects programmatically, bypassing the infix parser entirely. Must call update_types()/update_objects() so defined operators (→, ◇, etc.) expand via derive_type(). Critical: G/H equivalence verification — BimodalLogic derives G from U and H from S. The 6-tag JSON has no G/H tags. Verify that G(φ) ≡ ¬U(¬φ,⊤) and H(φ) ≡ ¬S(¬φ,⊤) produce identical Z3 constraints as the direct FutureOperator/PastOperator implementations. This is a soundness requirement — divergence means false training signals. Drop reverse direction (sentence→JSON). Tests: prefix construction for all 6 tag types, nested formulas, G/H equivalence check.

### 101. Restructure as bmlogic-oracle pip package
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 100

**Description**: Restructure the codebase as pip-installable bmlogic-oracle package. BimodalHarness already declares bmlogic-oracle>=0.1.0 as optional dependency — name is not a choice. Major pyproject.toml overhaul: package name bmlogic-oracle (import as bmlogic_oracle), description/classifiers/keywords updated for bimodal-only oracle, dependencies z3-solver>=4.8.0 as core dep (remove networkx, jupyter, cvc5, matplotlib), Python version >=3.10 (protocol uses modern type syntax). Entry point stub: [project.entry-points.'bimodal_harness.oracle_providers'] z3_base = "bmlogic_oracle.provider:Z3OracleProvider" (class created in task 103). Update package directory mapping. Fix testpaths in pytest config. Verify: pip install -e . succeeds in fresh venv.

### 100. Strip non-bimodal code and fix coupling
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python

**Description**: Strip all non-bimodal theories and fix hard coupling points identified in task 106 research. Fix hard logos imports: theory_lib/__init__.py:52 (unconditional from model_checker.theory_lib import logos), builder/example.py:34 (from ..theory_lib.logos import semantic). Remove logos-specific branching: builder/runner.py:82,206 (if 'Logos' in semantics_class.__name__). Delete: theory_lib/logos/ (and subtheories exclusion, imposition), jupyter/, notebook output templates. Collapse theory_lib/__init__.py to direct bimodal-only export (no registry, no lazy loading). Remove iterate/ module and networkx dependency (OracleProvider needs one countermodel, not iteration). Clean top-level code/tests/ of logos-specific tests; ensure bimodal tests at theory_lib/bimodal/tests/ still pass. Gate: PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v passes (43 examples).

