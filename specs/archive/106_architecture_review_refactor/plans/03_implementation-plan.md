# Implementation Plan: Architecture Review Deliverables for Tasks 99-105

- **Task**: 106 - Architecture review of bimodal refactor plan (tasks 99-105)
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/106_architecture_review_refactor/reports/02_team-research.md, specs/106_architecture_review_refactor/reports/03_clean-break-architecture.md
- **Artifacts**: plans/03_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Task 106 produces updated task descriptions and dependencies for the bimodal refactor plan (tasks 99-105), incorporating findings from three rounds of research. The deliverables are: (1) rewritten descriptions for each of tasks 100-105 that integrate architectural recommendations from the research (boundary buffer, ternary serialization, temporal_depth, testing infrastructure preservation, two-layer package structure), (2) new tasks for boundary effect mitigation, soundness regression testing, cross-oracle differential testing, and frame class validation, (3) a revised dependency graph reflecting the updated task structure, and (4) an architectural decision record capturing the converged design (BimodalLogic as specification, ModelChecker as pure Python oracle, BimodalHarness as soundness bridge). The task is done when TODO.md and state.json reflect all updates and the architectural decision record is written.

### Research Integration

Three research reports inform this plan:

- **Report 01** (team research, round 1): Initial codebase analysis, BimodalLogic alignment mapping, identification of the three-repo architecture pattern.
- **Report 02** (team research, round 2): BimodalLogic alignment mapping with critical boundary effects finding, soundness bridge architecture (Direct Embedding Theorem), 5 missing tasks, serialization gap (ternary task_rel), empirical-first soundness strategy.
- **Report 03** (clean-break architecture): Two-layer package structure recommendation, pipeline architecture (formula_json through Z3 to serialized countermodel), concrete keep/drop/fix inventory, boundary buffer mitigation strategy (temporal_depth + dynamic M), Sentence.from_prefix() design, Z3 context isolation strategy, preserved features inventory.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

ROADMAP.md exists but contains no items relevant to this task. No roadmap alignment applicable.

## Goals & Non-Goals

**Goals**:
- Rewrite task descriptions for tasks 100-105 to incorporate all research findings
- Create 4 new tasks: boundary effect mitigation, soundness regression tests, cross-oracle differential testing, frame class validation
- Update dependency graph across all tasks (99-105 plus new tasks)
- Document architectural decisions as a decision record artifact
- Update state.json with new tasks and revised dependencies

**Non-Goals**:
- Implementing any code changes (that is tasks 100-105+)
- Modifying BimodalHarness or BimodalLogic repositories
- Creating Lean infrastructure tasks (those belong to BimodalHarness, not ModelChecker)
- Resolving the boundary problem (that is a new task to be created)
- Merging or abandoning task 99 (research subsumed it; mark as completed-by-research or fold into 100)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task description rewrites lose important original context | M | M | Keep original intent, add research findings as augmentation |
| New tasks create scope creep beyond what is actionable | M | L | Limit new tasks to what research explicitly identified; defer "nice-to-have" items |
| Dependency graph becomes overly complex with new tasks | L | M | Use wave-based dependency analysis; keep independent tasks independent |
| state.json and TODO.md get out of sync during multi-task update | H | L | Use two-phase update pattern (state.json first, then TODO.md); verify after each write |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Synthesize Research into Architectural Decision Record [COMPLETED]

**Goal**: Produce a single architectural decision record (ADR) that captures the converged design decisions from all three research reports, serving as the authoritative reference for task description rewrites.

**Tasks**:
- [x] Create `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md`
- [x] Document Decision 1: Three-repo architecture (BimodalLogic = specification, ModelChecker = pure Python Z3 oracle, BimodalHarness = soundness bridge)
- [x] Document Decision 2: Zero code-level dependency between ModelChecker and BimodalLogic (JSON schema contracts only)
- [x] Document Decision 3: Two-layer package structure (thin OracleProvider skin over preserved Z3 core, no intermediate representation objects)
- [x] Document Decision 4: Preserve full bimodal test suite and examples.py as correctness gate
- [x] Document Decision 5: Boundary buffer via dynamic M = max(temporal_depth(formula) + 2, 3)
- [x] Document Decision 6: Ternary task_relation serialization (source, duration, target)
- [x] Document Decision 7: Empirical soundness first (Tier 1 testing), formal proofs later (Tier 2-3)
- [x] Document Decision 8: Sentence.from_prefix() as surgical addition (not parser rewrite)
- [x] Document Decision 9: Fresh BimodalSemantics instance per find_countermodel() call for Z3 isolation
- [x] Include the pipeline diagram from Report 03 Section 3
- [x] Include the keep/drop/fix inventory from Report 03 Section 2

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md` - new file

**Verification**:
- ADR covers all 9 decisions with rationale and rejected alternatives
- Pipeline diagram and keep/drop/fix inventory are included
- Document is self-contained (readable without needing to cross-reference research reports)

---

### Phase 2: Rewrite Task Descriptions for Tasks 100-105 [COMPLETED]

**Goal**: Update each task description in TODO.md to incorporate research findings, making each task self-contained with specific file references, acceptance criteria, and research-informed scope.

**Tasks**:
- [x] Rewrite Task 100 (Strip non-bimodal code): Add expanded gate criteria ("43 examples pass AND all unit tests in theory_lib/bimodal/tests/unit/ pass"), add explicit keep-list from Report 03 Section 2, add specific hard-coupling fixes with line numbers (theory_lib/__init__.py:52, builder/example.py:34, builder/runner.py:82,206)
- [x] Rewrite Task 101 (Restructure as bmlogic-oracle): Clarify that existing directory structure is preserved (no core/ subdirectory rename per Report 03 Rec 1), specify entry point format, confirm package name bmlogic-oracle with import name bmlogic_oracle
- [x] Rewrite Task 102 (Formula JSON translation): Add temporal_depth(formula_json) as a required deliverable (Report 03 Rec 2, Section 4), add Syntax programmatic constructor requirement (Report 03 Section 10 Q1), confirm 6-tag JSON field names from BimodalHarness schema, add G/H equivalence boundary caveat from Report 02 Section 1
- [x] Rewrite Task 103 (OracleProvider implementation): Add ternary task_rel extraction loop (Report 03 Section 3), add boundary buffer (M = max(temporal_depth + 2, 3)), add boundary_safe flag and temporal_depth in output, add StructuredCountermodel format from Report 03 Rec 8, add Z3 isolation strategy (fresh BimodalSemantics per call)
- [x] Rewrite Task 104 (Dead-code cleanup): Add explicit "do NOT remove" list from Report 03 Rec 6 (tests, examples.py, operators.py, extract_model_elements, print_* methods), narrow scope to only multi-theory CLI artifacts
- [x] Rewrite Task 105 (Integration testing): Add oracle pipeline test through OracleProvider (Report 03 Rec 2), add boundary regression tests, add ternary serialization validation, add temporal_depth reporting verification
- [x] Update dependency fields: Task 100 depends on none, Tasks 101 and 102 depend on 100, Task 103 depends on 101 and 102, Task 104 depends on 103, Task 105 depends on 103 and 104
- [x] Mark task 99 (audit) as subsumed by task 106 research -- its deliverables are fully covered by the three research reports; update its status to reflect this (Note: task 99 is in specs/archive/ per git log; it was already archived as ABANDONED; no action needed in TODO.md)

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/TODO.md` - rewrite descriptions for tasks 100-105, update task 99 status

**Verification**:
- Each rewritten description references specific research findings
- Each task has explicit acceptance criteria / gate
- Dependency chain is consistent and acyclic
- No information from research reports is lost in the rewrite

---

### Phase 3: Create New Tasks from Research Gaps [COMPLETED]

**Goal**: Create 4 new tasks identified by the research as missing from the original 99-105 plan: boundary effect mitigation, soundness regression test suite, cross-oracle differential testing, and frame class validation.

**Tasks**:
- [x] Create Task 107: "Boundary effect analysis and temporal_depth mitigation" -- Implement temporal_depth(formula_json) validation, add boundary buffer constraints to BimodalSemantics, prove that for M > temporal_depth(phi) + 1 no boundary effects create spurious countermodels, regression test known-valid/invalid formulas. Dependencies: 102 (needs temporal_depth function). Effort: medium. Type: python.
- [x] Create Task 108: "Soundness regression test suite for boundary and shift-closure edge cases" -- Test suite specifically probing boundary effects (G(phi) at t=M-1), incomplete shift closure near edges, guarded compositionality gaps, atom_false_of_not_domain alignment. Dependencies: 103 (needs OracleProvider). Effort: small. Type: python.
- [x] Create Task 109: "Cross-oracle differential testing infrastructure" -- Build infrastructure to compare Z3 oracle results against BimodalLogic's findCountermodel for systematic formula comparison; leverage BimodalLogic's FormulaEnumerator for formulas up to complexity 7. Dependencies: 103 (needs OracleProvider), requires BimodalHarness integration. Effort: medium. Type: python.
- [x] Create Task 110: "Frame class validation for Base frame" -- Validate that Z3's "Base" frame class matches BimodalLogic's base frame class (LinearTemporalFrame + SerialFrame axioms); verify disabled task_restriction constraint (semantic.py constraint 10) does not affect soundness; document frame hierarchy mapping. Dependencies: 100 (needs codebase audit). Effort: small. Type: python.
- [x] Assign task numbers using next_project_number from state.json (107, 108, 109, 110 assigned; next_project_number updated to 111)
- [x] Write task descriptions with effort, status [NOT STARTED], task_type, and dependencies

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `specs/TODO.md` - add 4 new task entries
- `specs/state.json` - add 4 new active_projects entries, update next_project_number to 111

**Verification**:
- All 4 new tasks have descriptions, effort estimates, dependencies, and task types
- Task numbers are sequential from 107
- Dependencies reference only existing tasks
- state.json next_project_number is updated to 111

---

### Phase 4: Update Dependency Graph and Sequencing [COMPLETED]

**Goal**: Produce a complete dependency graph across all tasks (100-110) and verify consistency between TODO.md dependency fields and state.json.

**Tasks**:
- [x] Build dependency adjacency list for all tasks 100-110
- [x] Verify dependency graph is a DAG (no cycles): Topological order confirmed: 100 → 110 → 102 → 107 → 101 → 103 → 108 → 109 → 104 → 105
- [x] Compute wave structure for parallel execution:
  - Wave 1: Task 100 (strip non-bimodal code)
  - Wave 2: Tasks 101, 102, 110 (package restructure, formula translation, frame validation -- all depend only on 100)
  - Wave 3: Tasks 103, 107 (OracleProvider, boundary analysis -- depend on 101+102 and 102 respectively)
  - Wave 4: Tasks 104, 108 (dead-code cleanup, soundness regression tests -- depend on 103)
  - Wave 5: Tasks 105, 109 (integration testing, cross-oracle testing -- depend on 103+104 and 103 respectively)
- [x] Add a dependency graph visualization to the ADR (Phase 1 artifact -- already included in 04_architectural-decisions.md during Phase 1)
- [x] Verify TODO.md dependency fields match the computed graph: all 10 tasks verified, all fields consistent
- [x] Verify state.json entries are consistent: tasks 107-110 have dependencies array; tasks 100-106 present

**Timing**: 20 minutes

**Depends on**: 2, 3

**Files to modify**:
- `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md` - append dependency graph
- `specs/TODO.md` - fix any dependency inconsistencies found
- `specs/state.json` - fix any inconsistencies found

**Verification**:
- Dependency graph is acyclic
- Every task's "Dependencies" field in TODO.md matches the graph
- Wave structure enables maximum parallelism
- No task depends on itself or creates a cycle

---

### Phase 5: Final Validation and State Updates [COMPLETED]

**Goal**: Verify all deliverables are complete, update task 106 status, and ensure TODO.md and state.json are synchronized.

**Tasks**:
- [x] Re-read TODO.md and verify all task descriptions (100-110) are complete and consistent
- [x] Re-read state.json and verify all entries match TODO.md
- [x] Verify ADR artifact exists and is complete (9 decisions, pipeline diagram, keep/drop/fix inventory, dependency graph)
- [x] Update task 106 status to [COMPLETED] in state.json and TODO.md
- [x] Add ADR artifact link to task 106 in TODO.md (added 04_architectural-decisions.md to Research list)
- [x] Run a final consistency check: all 10 tasks have status, task_type, and dependencies; next_project_number=111

**Timing**: 10 minutes

**Depends on**: 4

**Files to modify**:
- `specs/TODO.md` - update task 106 status, add artifact links
- `specs/state.json` - update task 106 status

**Verification**:
- TODO.md and state.json are synchronized
- All tasks 100-110 have descriptions, dependencies, effort, status, and task type
- Task 106 is marked as completed with all artifact links
- No dangling references or missing tasks

## Testing & Validation

- [x] All task descriptions (100-110) in TODO.md have: description, effort, status, task_type, dependencies
- [x] Dependency graph is acyclic (verify by topological sort) -- topological order confirmed: 100→110→102→107→101→103→108→109→104→105
- [x] state.json next_project_number equals 111
- [x] state.json active_projects contains entries for tasks 107-110
- [x] ADR document covers all 9 architectural decisions
- [x] Task 99 status is reflected as absorbed: already archived as "abandoned" with note "Absorbed by task 106 architecture review" prior to this task
- [x] No information from research reports 02 and 03 is lost in the task rewrites (temporal_depth, ternary serialization, G/H boundary caveat, 6-tag field names, Z3 isolation, boundary buffer, keep/drop/fix, all captured in task descriptions)

## Artifacts & Outputs

- `specs/106_architecture_review_refactor/plans/03_implementation-plan.md` - this plan
- `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md` - architectural decision record
- `specs/TODO.md` - updated task descriptions for 100-105, new tasks 107-110, updated task 99
- `specs/state.json` - new task entries for 107-110, updated next_project_number

## Rollback/Contingency

All changes are to TODO.md, state.json, and new markdown files. If the updates introduce inconsistencies:
1. Use `git diff specs/TODO.md` to review changes
2. Use `git checkout specs/TODO.md specs/state.json` to revert to pre-update state
3. The ADR (new file) can simply be deleted
4. No code changes are made in this task, so no code rollback is needed
