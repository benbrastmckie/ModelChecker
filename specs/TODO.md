---
next_project_number: 111
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 110. Frame class validation for Base frame
- **Effort**: small
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 100

**Description**: Validate that the Z3 oracle's "Base" frame class matches BimodalLogic's base frame class (LinearTemporalFrame + SerialFrame axioms). Currently, task 103 claims supported_frame_classes=frozenset({"Base"}) but "Base" is not formally defined against BimodalLogic's frame hierarchy. This task resolves the ambiguity. Deliverables: (1) Document the mapping between Z3's frame axioms (nullity_identity, forward_comp, converse from semantic.py:274-388) and BimodalLogic's LinearTemporalFrame + SerialFrame Lean axioms; (2) Verify that the disabled task_restriction constraint (semantic.py constraint 10) does not create soundness issues — specifically, confirm that allowing task_rel entries not realized in any world history is consistent with BimodalLogic's frame definition or document the divergence; (3) Document the Z3 frame hierarchy: what does the oracle guarantee about task_rel structure (which axioms hold, which do not), and how does "Base" map to BimodalLogic's frame hierarchy (LinearTemporalFrame < SerialFrame < Dense/Discrete); (4) Write a `test_frame_class_mapping.py` test that asserts all extracted countermodels satisfy the documented frame axioms programmatically. Gate: Frame hierarchy mapping is documented in a comment in `provider.py` and verified by the test suite.

### 109. Cross-oracle differential testing infrastructure
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103

**Description**: Build infrastructure to compare Z3 oracle results against BimodalLogic's findCountermodel for systematic formula comparison. This is the Tier 1 empirical soundness validation mechanism. Deliverables: (1) A test harness that calls both `OracleProvider.find_countermodel()` and BimodalLogic's `findCountermodel` endpoint (via BimodalHarness subprocess or API) for the same formula and asserts agreement on SAT/UNSAT classification; (2) Integration with BimodalLogic's FormulaEnumerator (or equivalent) to generate formulas up to complexity 7 for systematic comparison; (3) A differential report format: for any disagreement, output the formula, the Z3 countermodel (if any), the BimodalLogic result, and the `temporal_depth` and `boundary_safe` flags; (4) CI integration: the differential test suite runs on every oracle code change. Note: requires BimodalHarness integration and may require a subprocess call to BimodalLogic's Python/CLI interface. If the BimodalHarness API is not available, implement the framework with a mock BimodalLogic oracle and document the integration point. Dependencies: requires OracleProvider (task 103) to be implemented; the BimodalHarness SoundnessGateway (bimodal_harness/oracle/gateway.py:219-508) is the integration point.

### 108. Soundness regression test suite for boundary and shift-closure edge cases
- **Effort**: small
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103

**Description**: Test suite specifically probing the soundness gap points identified in task 106 research. The existing test suite (`test_bimodal.py`, etc.) tests general correctness; this suite targets specific failure modes. Test categories: (1) Boundary vacuity tests: construct formulas where G(phi) at the domain edge (t=M-1) is vacuously true; verify the oracle correctly sets boundary_safe=False for formulas of temporal_depth >= M-1, and that the M=max(depth+2,3) formula prevents these from appearing; (2) Shift closure tests: verify that extracted countermodels satisfy shift closure for shifts within (-M+1, M-1); (3) Guarded compositionality tests: verify forward_comp and converse constraints hold for all durations in the extracted task_relation (not just those near the boundary); (4) State isolation regression: run find_countermodel() 100+ times in sequence on a mix of SAT and UNSAT formulas; assert no state leakage (SAT results same as first call, UNSAT results same as first call); (5) Known-boundary-unsafe formulas: hand-craft 5 formulas with temporal_depth >= 2 that would produce boundary artifacts with M=2 but correct results with M=max(depth+2,3); verify oracle produces correct SAT/UNSAT with dynamic M. Gate: All tests in `test_soundness_regression.py` pass; no boundary-unsafe formulas produce incorrect results.

### 107. Boundary effect analysis and temporal_depth mitigation
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 102

**Description**: Full analysis and mitigation of the finite time domain boundary problem identified in task 106 research as the primary soundness gap. The minimum viable mitigation (dynamic M = max(temporal_depth + 2, 3)) is implemented in task 103; this task provides the formal analysis and regression tests. Deliverables: (1) Implement and test temporal_depth(formula_json) function if not already completed by task 102 (this task depends on 102 but provides additional depth analysis); (2) Prove informally (via argument in code comments and documentation) that for formulas of temporal depth d evaluated with M > d + 1, boundary effects cannot create spurious countermodels — specifically, that G(phi) at t=0 with M > d+1 is not vacuously true because t+d < M-1; (3) Add boundary buffer constraints to BimodalSemantics: for formula depth d, add Z3 constraints that assert the evaluation time t=0 is at least d steps from both domain edges (i.e., ForAll t in formula subformulas, is_valid_time(t + d) holds); (4) Regression test: verify that all 43 known-valid formulas still return None (no spurious countermodels from boundary changes), and all 43 known-invalid formulas still return countermodels (no countermodels lost from over-buffering); (5) Document the boundary claim: "For formulas of temporal depth d evaluated with M > d + 1, no boundary effects create spurious countermodels." Include this as a docstring on temporal_depth() and as a comment in OracleProvider.find_countermodel(). Gate: All 43 examples produce correct results with boundary buffer active; temporal_depth() is correct for all 6 JSON formula tag types.

### 106. Architecture review of bimodal refactor plan (tasks 99-105)
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: python
- **Research**:
  - [106_architecture_review_refactor/reports/01_team-research.md]
  - [106_architecture_review_refactor/reports/02_team-research.md]
  - [106_architecture_review_refactor/reports/03_clean-break-architecture.md]
  - [106_architecture_review_refactor/reports/04_architectural-decisions.md]
- **Plan**: [106_architecture_review_refactor/plans/03_implementation-plan.md]

**Description**: Deep architectural review of the planned bimodal ModelChecker refactor (tasks 99-105). Study the current ModelChecker codebase (code/src/model_checker/), the BimodalHarness OracleProvider protocol (bimodal_harness/oracle/protocol.py in /home/benjamin/Projects/BimodalHarness/), the BimodalLogic interface expectations, and the technical memo (/home/benjamin/Projects/Logos/Vision/shared/strategy/01-overview/03-technical_memo.typ). Evaluate: (1) whether the proposed task decomposition and ordering is optimal, (2) whether the package boundary and public API surface are well-drawn, (3) whether the formula JSON translation approach handles all edge cases (defined operators, operator precedence, round-trip fidelity), (4) whether the countermodel serialization maps cleanly to BimodalStructure's extract_model_elements output, (5) whether tasks 99 (audit) and 100 (strip) should be merged or resequenced, (6) whether the builder/output/settings simplification in task 104 is scoped correctly or risks breaking the Z3 solving pipeline, (7) any missing tasks (e.g., documentation, CI/CD, version pinning against BimodalHarness). Produce a report with concrete architectural recommendations and revised task descriptions where warranted. The end product is updated descriptions and dependencies for tasks 99-105.

### 105. Integration testing and validation
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103, 104

**Description**: End-to-end testing against the OracleProvider protocol and BimodalHarness compatibility. Oracle pipeline test: run all 43 examples from `theory_lib/bimodal/examples.py` through `OracleProvider.find_countermodel()` (not the internal `run_test` pipeline) and verify identical SAT/UNSAT classifications — this is `test_oracle_interface.py`. Protocol compliance: verify all 5 properties, both methods, return format matches SimpleCountermodel/StructuredCountermodel schemas. Countermodel correctness: regression test against the existing 43-example bimodal test suite — refactored package must produce identical valid/invalid classifications. Cross-signal scenarios: use BimodalHarness's SPOT_CHECK_FORMULAS (10 known-invalid formulas from _mock.py) as ground truth for validate_self. Boundary regression tests: verify that formulas with known temporal depth d use M = max(d+2, 3) and that `boundary_safe` flag is True for all 43 examples. Ternary serialization validation: verify that all `task_relation` entries are ternary `{source, duration, target}` dicts, not binary pairs. Temporal_depth reporting: verify `temporal_depth` is present and correct in all oracle outputs. Edge cases: timeout handling (formula that exceeds timeout_ms), unsupported frame_class ("Dense"→None), malformed formula JSON. Entry-point discovery: verify pip install bmlogic-oracle followed by OracleRegistry.discover() finds the provider. Z3 isolation: run find_countermodel() 100+ times in sequence, verify no state leakage or memory growth.

### 104. Dead-code cleanup and thin CLI
- **Effort**: small
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 103

**Description**: With OracleProvider working as the primary public interface, remove dead code and add a thin CLI. Remove unused builder components: project scaffolding (`builder/`), multi-theory comparison (`builder/comparison.py`), theory template generation. Simplify output/: remove interactive prompts, notebook templates (`output/notebook/`), progress bars (OracleProvider returns dicts, not formatted output). Remove logos-specific branching remnants in builder/runner.py. Add thin CLI: `bmlogic-oracle check '<formula_json>'` for standalone countermodel checking. DO NOT remove the following — they are required by the oracle pipeline, testing infrastructure, or thin CLI: (1) `theory_lib/bimodal/tests/` — the full test suite (correctness gate), (2) `theory_lib/bimodal/examples.py` — the 43-example evaluation suite, (3) `theory_lib/bimodal/operators.py` — operator implementations, (4) `extract_model_elements()`, `extract_states()`, and all model extraction chain methods, (5) `print_*` methods on BimodalStructure (needed for thin CLI), (6) `output/formatters/` (structured output formatting), (7) `settings/settings.py` (CLI settings parsing). Only remove code that was exclusively used by the multi-theory CLI and is unreachable from the oracle pipeline or test infrastructure.

### 103. OracleProvider implementation with programmatic pipeline
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 101, 102

**Description**: Implement the OracleProvider protocol class with a new programmatic solving pipeline. New pipeline: formula_json → json_to_prefix() → Sentence.from_prefix() → BimodalSemantics(N, M) → Syntax(operators, [sentence]) → ModelConstraints → BimodalStructure → Z3 solve → extract model → serialize. OracleProvider properties: provider_id="bmlogic_z3_base_v1", provider_version (semver), semantics_version (pinned to BimodalLogic git tag or release), supported_frame_classes=frozenset({"Base"}), capabilities dict. find_countermodel(formula_json, frame_class, timeout_ms): implements full pipeline, returns None on UNSAT/timeout/unsupported frame_class. Boundary buffer: compute M = max(temporal_depth(formula_json) + 2, 3) using the temporal_depth() function from task 102 — do NOT use a fixed M. Ternary task_rel extraction: iterate all (source, duration, target) triples and evaluate semantics.task_rel(s, d, u) on z3_model (see ADR Decision 6 for loop). Oracle output must include: `temporal_depth` (int), `boundary_safe` (bool: M > temporal_depth + 1), `time_bound` (M), `semantics_version`. Countermodel serialization: both SimpleCountermodel (trueAtoms/falseAtoms from evaluating atoms at eval point) and StructuredCountermodel (world_histories, task_relation as ternary triples, truth_valuation from extract_model_elements()). Z3 context isolation: construct fresh BimodalSemantics instance per find_countermodel() call; wrap each call in isolated_z3_context() from utils/context.py; do NOT hold a reference to BimodalSemantics between calls (self._semantics = None between calls). validate_self(spot_check_formulas): must find countermodels for all provided known-invalid formulas. Finalize entry point in pyproject.toml: [project.entry-points.'bimodal_harness.oracle_providers'] z3_base = "bmlogic_oracle.provider:Z3OracleProvider". Gate: 100 sequential calls complete without state leakage; 43 examples produce correct SAT/UNSAT (identical to pre-refactor).

### 102. Formula JSON translation with G/H equivalence verification
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 100

**Description**: Implement one-directional JSON→internal formula translation with semantic equivalence verification. Create json_to_prefix(formula_json) function mapping 6 JSON tags to internal prefix-list format: atom→variable name (field: "base"), bot→\bot, imp→\rightarrow (fields: "left", "right"), box→\Box (field: "arg"), untl→U (fields: "guard", "reach"), snce→S (fields: "guard", "reach"). Confirm exact field names from BimodalLogic Formula.toJson output or BimodalHarness schema before implementing. Create temporal_depth(formula_json) -> int function: recursively walks formula AST, returns maximum temporal nesting depth (U/S/box increment depth; atom/bot depth=0; imp passes through max). Create Sentence.from_prefix(prefix_list, operators) classmethod that constructs Sentence objects programmatically, bypassing the infix parser entirely. Must call update_types()/update_objects() so defined operators (→, ◇, etc.) expand via derive_type(). Open question (must resolve in task 102): Does Syntax.__init__() currently accept Sentence objects directly or only infix strings? If only infix strings, add a programmatic constructor overload as part of this task. Critical: G/H equivalence verification — BimodalLogic derives G from U and H from S. The 6-tag JSON has no G/H tags. Verify that G(φ) ≡ ¬U(¬φ,⊤) and H(φ) ≡ ¬S(¬φ,⊤) produce identical Z3 constraints as the direct FutureOperator/PastOperator implementations. This is a soundness requirement — divergence means false training signals. G/H boundary caveat (from Report 02): G/H equivalence holds in infinite domains but Z3's ForAllTime guard with is_valid_time creates a different quantification range at boundaries; the temporal_depth function combined with M = max(depth+2, 3) in task 103 mitigates this. Drop reverse direction (sentence→JSON). Tests: prefix construction for all 6 tag types, nested formulas, temporal_depth for leaf/unary/binary/nested, G/H equivalence check.

### 101. Restructure as bmlogic-oracle pip package
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 100

**Description**: Restructure the codebase as pip-installable bmlogic-oracle package. BimodalHarness already declares bmlogic-oracle>=0.1.0 as optional dependency — name is not a choice. Major pyproject.toml overhaul: package name bmlogic-oracle (import as bmlogic_oracle), description/classifiers/keywords updated for bimodal-only oracle, dependencies z3-solver>=4.8.0 as core dep (remove networkx, jupyter, cvc5, matplotlib), Python version >=3.10 (protocol uses modern type syntax). Existing directory structure is preserved — do NOT create a core/ subdirectory or rename theory_lib/bimodal/; renaming would cause mass import churn across ~20 files (ADR Decision 3 Rec 1). Entry point stub: [project.entry-points.'bimodal_harness.oracle_providers'] z3_base = "bmlogic_oracle.provider:Z3OracleProvider" (class created in task 103 — stub must exist in pyproject.toml now). Update package directory mapping in pyproject.toml. Fix testpaths in pytest config (task 100 removed logos-specific top-level tests; point at theory_lib/bimodal/tests/). New thin files: bmlogic_oracle/__init__.py (public: Z3OracleProvider placeholder), provider.py placeholder, translation.py placeholder, serialization.py placeholder — placeholders are empty stubs that will be filled in task 103/102 respectively. Verify: pip install -e . succeeds in fresh venv; import bmlogic_oracle works.

### 100. Strip non-bimodal code and fix coupling
- **Effort**: medium
- **Status**: [COMPLETED]
- **Task Type**: python
- **Research**: [100_strip_non_bimodal_code/reports/01_codebase-audit.md]
- **Plan**: [100_strip_non_bimodal_code/plans/02_implementation-plan.md]
- **Summary**: [100_strip_non_bimodal_code/summaries/02_strip-non-bimodal-summary.md]

**Description**: Strip all non-bimodal theories and fix hard coupling points identified in task 106 research. Fix hard logos imports first: theory_lib/__init__.py:52 (unconditional `from model_checker.theory_lib import logos` — replace with direct bimodal-only export, no registry, no lazy loading), builder/example.py:34 (`from ..theory_lib.logos import semantic` — remove logos-specific initialization), builder/runner.py:82,206 (`if 'Logos' in semantics_class.__name__` — remove logos-specific branching). Delete non-bimodal theories: theory_lib/logos/ (and all subtheories), theory_lib/imposition/, theory_lib/exclusion/. Delete: jupyter/, output/notebook/ (notebook output templates). Delete: iterate/ module (OracleProvider needs one countermodel, not iteration). Remove: networkx, matplotlib, cvc5, jupyter from pyproject.toml dependencies. Clean top-level code/tests/ of logos-specific tests. Preserve the following (they are the correctness gate, not dead code): theory_lib/bimodal/tests/ (full unit test suite), theory_lib/bimodal/examples.py (43-example evaluation suite), theory_lib/bimodal/operators.py, all Z3 constraint builders in semantic.py. Gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (43 examples) AND all unit tests in `theory_lib/bimodal/tests/unit/` pass (frame constraints, ForAllTime, Until/Since, witness predicates, strict semantics, API consistency, data extraction).

