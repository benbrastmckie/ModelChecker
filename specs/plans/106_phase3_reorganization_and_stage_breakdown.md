# Phase 3 Reorganization and Stage Breakdown Plan

## ✅ IMPLEMENTATION COMPLETE

**Completion Date**: 2025-10-03
**All Deliverables**: Created successfully
**Status**: Ready for Phase 3 implementation

## Metadata
- **Date**: 2025-10-03
- **Feature**: Reorganize Phase 3 directory structure and create detailed stage implementation files
- **Scope**: Move phase3_abstraction_integration.md into phase3_integration/ and create comprehensive stage files comparable to Phase 1 and Phase 2
- **Estimated Duration**: 1-2 hours (organization and documentation)
- **Standards File**: /home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md
- **Related Phases**: Phase 1 (phase1_pilot), Phase 2 (phase2_abstraction)

## Overview

Phase 3 currently has a single comprehensive plan file (`phase3_abstraction_integration.md`) but lacks the detailed stage breakdown structure used successfully in Phases 1 and 2. This plan reorganizes Phase 3 to match the proven structure:

**Current State**:
- Single file: `cvc5/phase3_abstraction_integration.md` (~858 lines)
- 6 sub-phases described in one document
- No individual stage files
- No STAGE_INDEX.md
- No README.md

**Target State** (matching Phase 1 and Phase 2):
- Directory: `cvc5/phase3_integration/`
- Main plan: `phase3_bimodal_abstraction_integration.md`
- Individual stage files: `stage01_*.md` through `stage06_*.md`
- `STAGE_INDEX.md` for navigation
- `README.md` for overview
- Consistent structure with existing phases

## Success Criteria

- [x] Directory created: `cvc5/phase3_integration/` ✅
- [x] Main plan moved and renamed appropriately ✅
- [x] 6 individual stage files created (stage01 through stage06) ✅
- [x] STAGE_INDEX.md created with progress tracking ✅
- [x] README.md created with phase overview ✅
- [x] All cross-references updated ✅
- [x] Structure matches Phase 1 and Phase 2 patterns ✅
- [x] Ready for `/implement` command usage ✅

## Technical Design

### Directory Structure

```
Code/src/model_checker/theory_lib/bimodal/specs/cvc5/
├── phase1_pilot/                    # ✅ Complete
│   ├── phase1_bimodal_cvc5_pilot.md
│   ├── stage01_core_setup.md
│   ├── stage02_quantifier_helpers.md
│   ├── ...
│   └── STAGE_INDEX.md
├── phase2_abstraction/              # ✅ Complete
│   ├── phase2_abstraction_layer_design.md
│   ├── stage01_interface_capabilities.md
│   ├── stage02_z3_adapter.md
│   ├── ...
│   ├── STAGE_INDEX.md
│   └── README.md
└── phase3_integration/              # 🆕 To be created
    ├── phase3_bimodal_abstraction_integration.md
    ├── stage01_integration_test_setup.md
    ├── stage02_semantic_core_migration.md
    ├── stage03_operators_witness_migration.md
    ├── stage04_examples_iteration_migration.md
    ├── stage05_dual_solver_validation.md
    ├── stage06_documentation_reporting.md
    ├── STAGE_INDEX.md
    └── README.md
```

### Stage Breakdown

Based on the existing sub-phases in phase3_abstraction_integration.md:

**Stage 1: Integration Test Setup** (Sub-Phase 3.1)
- Write integration tests BEFORE migration (TDD)
- Create test fixtures for dual-solver testing
- Establish performance baselines

**Stage 2: Semantic Core Migration** (Sub-Phase 3.2)
- Migrate semantic.py to SolverInterface
- Update imports, signatures, API calls
- Verify unit tests pass

**Stage 3: Operators and Witness Migration** (Sub-Phase 3.3)
- Migrate operators.py
- Migrate witness_constraints.py (CRITICAL)
- Migrate witness_registry.py

**Stage 4: Examples and Iteration Migration** (Sub-Phase 3.4)
- Migrate examples.py to SolverFactory
- Migrate iterate.py
- Runtime solver selection via settings

**Stage 5: Dual-Solver Validation** (Sub-Phase 3.5)
- Z3 regression testing
- CVC5 performance validation
- Equivalence testing
- Performance benchmarking

**Stage 6: Documentation and Reporting** (Sub-Phase 3.6)
- Update bimodal README
- Create migration guide
- Phase 3 results report
- Implementation summary

### File Templates

Each stage file will follow this structure (matching Phase 1 and Phase 2):

```markdown
# Stage N: [Stage Name]

## Metadata
- **Stage**: N/6 (Phase 3 - Bimodal Abstraction Integration)
- **Estimated Duration**: X days (Y hours)
- **Complexity**: Low/Medium/High
- **Dependencies**: Stage N-1 complete, Phase 2 complete
- **Files**: [List of files to be modified/created]
- **Coverage Target**: >85% (bimodal), >90% (witness system)
- **Risk**: [Risk level and description]

## Objective

[Clear statement of what this stage accomplishes]

**Success Criteria**: [Specific, measurable outcomes]

## Implementation Tasks

### Task 1: [TDD-RED/GREEN/etc.] [Task Name]
**Duration**: X hours

- [ ] Specific subtask with file reference
- [ ] Another subtask
- [ ] Testing task

**Implementation Pattern**:
```python
# Example code showing the pattern
```

**Testing Command**:
```bash
# Command to verify task completion
```

**Expected**: [Expected outcome]

### Task 2: [Next Task]
[Continue with additional tasks...]

## Testing Strategy

[Specific testing approach for this stage]

## Success Criteria Checklist

- [ ] Criteria 1
- [ ] Criteria 2
- [ ] All tests passing
- [ ] Coverage target met

## Common Issues & Solutions

### Issue 1: [Potential problem]
**Problem**: [Description]
**Solution**: [Resolution]

## Risk Mitigation

[Specific risks for this stage and mitigations]

## Dependencies for Next Stage

[What must be complete to proceed]

## Notes

[Additional considerations]

---

**Stage N Status**: ☐ Pending
**Previous Stage**: [Link to stage N-1]
**Next Stage**: [Link to stage N+1]
```

## Implementation Phases

### Phase 1: Directory Setup and File Migration [COMPLETED]
**Objective**: Create directory structure and move existing files
**Complexity**: Low

Tasks:
- [x] Create `cvc5/phase3_integration/` directory
- [x] Move `phase3_abstraction_integration.md` to `phase3_integration/`
- [x] Rename to `phase3_bimodal_abstraction_integration.md`
- [x] Update cross-references in moved file

Testing:
```bash
# Verify directory structure
ls -la Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/

# Verify main plan exists
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/phase3_bimodal_abstraction_integration.md && echo "Main plan exists"
```

### Phase 2: Create Stage 1 - Integration Test Setup
**Objective**: Extract Sub-Phase 3.1 into detailed stage file
**Complexity**: Medium

Tasks:
- [ ] Create `stage01_integration_test_setup.md`
- [ ] Extract content from Sub-Phase 3.1
- [ ] Add detailed metadata section
- [ ] Expand task descriptions with code examples
- [ ] Add testing strategy section
- [ ] Add common issues and solutions
- [ ] Add cross-references to Phase 2 equivalence tests

Testing:
```bash
# Verify stage file created
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage01_integration_test_setup.md && echo "Stage 1 created"

# Check file has required sections
grep -q "## Metadata" Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage01_integration_test_setup.md && echo "Has metadata"
```

### Phase 3: Create Stage 2 - Semantic Core Migration
**Objective**: Extract Sub-Phase 3.2 into detailed stage file
**Complexity**: Medium

Tasks:
- [ ] Create `stage02_semantic_core_migration.md`
- [ ] Extract content from Sub-Phase 3.2
- [ ] Add before/after code examples for each migration type
- [ ] Document API translation patterns
- [ ] Add testing validation steps
- [ ] Reference Phase 1 semantic.py for comparison

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage02_semantic_core_migration.md && echo "Stage 2 created"
```

### Phase 4: Create Stage 3 - Operators and Witness Migration
**Objective**: Extract Sub-Phase 3.3 into detailed stage file
**Complexity**: High (witness system critical)

Tasks:
- [ ] Create `stage03_operators_witness_migration.md`
- [ ] Extract content from Sub-Phase 3.3
- [ ] Add detailed witness predicate migration guide
- [ ] Document MBQI+enum-inst validation
- [ ] Add coverage requirements (>90% for witness system)
- [ ] Reference Phase 1 witness implementation

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage03_operators_witness_migration.md && echo "Stage 3 created"
```

### Phase 5: Create Stage 4 - Examples and Iteration Migration
**Objective**: Extract Sub-Phase 3.4 into detailed stage file
**Complexity**: Medium

Tasks:
- [ ] Create `stage04_examples_iteration_migration.md`
- [ ] Extract content from Sub-Phase 3.4
- [ ] Add SolverFactory integration examples
- [ ] Document settings configuration
- [ ] Add runtime solver selection guide

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage04_examples_iteration_migration.md && echo "Stage 4 created"
```

### Phase 6: Create Stage 5 - Dual-Solver Validation
**Objective**: Extract Sub-Phase 3.5 into detailed stage file
**Complexity**: High (comprehensive validation)

Tasks:
- [ ] Create `stage05_dual_solver_validation.md`
- [ ] Extract content from Sub-Phase 3.5
- [ ] Add performance benchmarking methodology
- [ ] Document equivalence test approach
- [ ] Add overhead measurement guide
- [ ] Include performance metrics table template

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage05_dual_solver_validation.md && echo "Stage 5 created"
```

### Phase 7: Create Stage 6 - Documentation and Reporting
**Objective**: Extract Sub-Phase 3.6 into detailed stage file
**Complexity**: Low

Tasks:
- [ ] Create `stage06_documentation_reporting.md`
- [ ] Extract content from Sub-Phase 3.6
- [ ] Add documentation templates
- [ ] Reference Phase 2 Report 015 as template
- [ ] Add migration guide outline

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage06_documentation_reporting.md && echo "Stage 6 created"
```

### Phase 8: Create STAGE_INDEX.md
**Objective**: Create navigation and progress tracking document
**Complexity**: Low

Tasks:
- [ ] Create `STAGE_INDEX.md` following Phase 1/2 pattern
- [ ] Add stage summary table
- [ ] Add completion status tracking
- [ ] Add progress metrics
- [ ] Add quick reference commands
- [ ] Add cross-references to Phases 1 and 2

Template follows Phase 2 STAGE_INDEX.md structure:
- Overview with total stages and duration
- Stage Summary Table
- Stage Details (links to individual files)
- Progress Tracking section
- Key Metrics
- Testing Commands
- Dependencies

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/STAGE_INDEX.md && echo "STAGE_INDEX created"
```

### Phase 9: Create README.md
**Objective**: Create phase overview document
**Complexity**: Low

Tasks:
- [ ] Create `README.md` following Phase 2 pattern
- [ ] Add phase overview and objectives
- [ ] Add prerequisites from Phases 1 and 2
- [ ] Document dual-solver validation strategy
- [ ] Add quick start guide for implementation
- [ ] Add links to all stage files

Testing:
```bash
test -f Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/README.md && echo "README created"
```

### Phase 10: Update Cross-References
**Objective**: Ensure all links and references are correct
**Complexity**: Low

Tasks:
- [ ] Update MASTER_PLAN.md to point to new Phase 3 directory
- [ ] Update Phase 2 docs to reference Phase 3 correctly
- [ ] Update main plan file cross-references
- [ ] Verify all stage file cross-references (Previous/Next Stage)
- [ ] Update any references in Phase 1 documentation

Testing:
```bash
# Check MASTER_PLAN.md has correct reference
grep -q "phase3_integration" Code/src/model_checker/theory_lib/bimodal/specs/cvc5/MASTER_PLAN.md && echo "MASTER_PLAN updated"

# Check for broken links
cd Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/
for md in *.md; do
    echo "Checking $md for broken links..."
    # Check relative links exist
done
```

## Testing Strategy

### Validation Steps

1. **Directory Structure Validation**
   ```bash
   # Verify all files created
   test -d Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration
   ls Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/*.md | wc -l
   # Expected: 9 files (main plan + 6 stages + STAGE_INDEX + README)
   ```

2. **Content Validation**
   ```bash
   # Verify each stage file has required sections
   for stage in stage0{1..6}_*.md; do
       echo "Validating $stage..."
       grep -q "## Metadata" "$stage" && echo "  ✓ Has Metadata"
       grep -q "## Objective" "$stage" && echo "  ✓ Has Objective"
       grep -q "## Implementation Tasks" "$stage" && echo "  ✓ Has Tasks"
       grep -q "## Testing Strategy" "$stage" && echo "  ✓ Has Testing"
   done
   ```

3. **Cross-Reference Validation**
   ```bash
   # Check MASTER_PLAN references
   grep "phase3_integration" Code/src/model_checker/theory_lib/bimodal/specs/cvc5/MASTER_PLAN.md

   # Check stage progression links
   grep "Previous Stage" Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage*.md
   grep "Next Stage" Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/stage*.md
   ```

4. **Consistency Validation**
   ```bash
   # Compare structure to Phase 2
   diff -qr <(ls Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase2_abstraction/) \
           <(ls Code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration/)
   # Should have similar file patterns (main plan, stages, STAGE_INDEX, README)
   ```

## Documentation Requirements

### README.md Structure

```markdown
# Phase 3: Bimodal Theory Abstraction Integration

## Overview
[Brief description of Phase 3 objectives]

## Prerequisites
- ✅ Phase 1 Complete: Bimodal theory migrated to CVC5
- ✅ Phase 2 Complete: Abstraction layer implemented
- Solver package ready with Z3 and CVC5 adapters

## Stages
1. [Integration Test Setup](stage01_integration_test_setup.md)
2. [Semantic Core Migration](stage02_semantic_core_migration.md)
3. [Operators and Witness Migration](stage03_operators_witness_migration.md)
4. [Examples and Iteration Migration](stage04_examples_iteration_migration.md)
5. [Dual-Solver Validation](stage05_dual_solver_validation.md)
6. [Documentation and Reporting](stage06_documentation_reporting.md)

## Quick Start
[How to begin implementation]

## Navigation
- [STAGE_INDEX.md](STAGE_INDEX.md) - Progress tracking
- [Phase 3 Main Plan](phase3_bimodal_abstraction_integration.md)
- [Back to MASTER_PLAN](../MASTER_PLAN.md)
```

### STAGE_INDEX.md Structure

Follows Phase 2 pattern:
- Overview with phase stats
- Stage Summary Table with LOC and duration estimates
- Stage Details sections
- Progress Tracking
- Completion Status checkboxes
- Testing Commands
- Standards Compliance section

## Dependencies

### External Dependencies
- Phases 1 and 2 must be complete
- All Phase 2 documentation available for reference

### Internal Dependencies
- Existing `phase3_abstraction_integration.md` file
- Phase 1 and Phase 2 STAGE_INDEX files (for pattern reference)
- MASTER_PLAN.md (for cross-reference updates)

### Pattern Dependencies
- Phase 1 stage file structure
- Phase 2 stage file structure
- Consistent metadata format
- Consistent section organization

## Notes

### Design Rationale

**Why reorganize Phase 3?**
1. **Consistency**: Phases 1 and 2 use detailed stage files successfully
2. **Navigation**: Individual stage files easier to find and read
3. **Implementation**: `/implement` command works better with granular stages
4. **Progress Tracking**: STAGE_INDEX provides clear visibility
5. **Reference**: Easier for other theories to follow the pattern

**Why 6 stages?**
- Maps directly to existing 6 sub-phases in current plan
- Each stage is focused and testable
- Matches Phase 1's 12-stage granularity principle (Phase 3 sub-phases are larger)
- Aligns with TDD cycle (RED → GREEN → REFACTOR per stage)

### Migration from Current Plan

The existing `phase3_abstraction_integration.md` has excellent content but lacks:
1. Individual stage files for focused implementation
2. Detailed code examples in each stage
3. STAGE_INDEX for progress tracking
4. README for quick navigation

This reorganization preserves all content while adding structure.

### Cross-Phase Consistency

All three phases now follow the same pattern:
```
phaseN_[name]/
├── phaseN_[descriptive_name].md    # Main plan
├── stage01_*.md                    # Stage files
├── stage02_*.md
├── ...
├── STAGE_INDEX.md                  # Progress tracking
└── README.md                       # Overview
```

This makes the entire CVC5 integration project easier to navigate and implement.

## Deliverables

Upon completion:
1. ✅ `cvc5/phase3_integration/` directory created
2. ✅ Main plan moved and properly referenced
3. ✅ 6 detailed stage files created
4. ✅ STAGE_INDEX.md with progress tracking
5. ✅ README.md with navigation
6. ✅ All cross-references updated
7. ✅ Structure matches Phases 1 and 2

**Ready for**: `/implement` command to execute Phase 3 stages systematically
