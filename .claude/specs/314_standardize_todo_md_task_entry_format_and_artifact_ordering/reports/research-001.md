# Research Report: Standardize TODO.md Task Entry Format and Artifact Ordering

**Task**: 314  
**Created**: 2026-01-05  
**Status**: Complete  
**Researcher**: status-sync-manager analysis

---

## Executive Summary

Task 313 in TODO.md exhibits incorrect field ordering where artifact links and timestamps appear BEFORE standard metadata fields (Effort, Status, Priority, Language). This violates the implicit ordering convention established by other tasks and causes inconsistency in task entry format. The root cause is that `status-sync-manager.md` and `tasks.md` do not explicitly specify the canonical field order for task entries.

**Key Finding**: The `artifact_link_update_logic` in status-sync-manager.md (lines 432-455) describes HOW to add artifacts but not WHERE to place them relative to standard metadata fields.

---

## Problem Analysis

### Observed Inconsistency

**Task 312 (Correct Order)**:
```markdown
### 312. Fix workflow command postflight failures
- **Effort**: 6-8 hours
- **Status**: [REVISED]
- **Priority**: High
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None
- **Research**: [Research Report](...)
- **Researched**: 2026-01-05
- **Plan**: [Implementation Plan v2](...)
- **Planned**: 2026-01-05
- **Revised**: 2026-01-05

**Description**: ...
```

**Task 313 (Incorrect Order)**:
```markdown
### 313. Configure opencode agent system
- **Research**: [Research Report](...)
- **Researched**: 2026-01-05
- **Plan**: [Implementation Plan](...)
- **Planned**: 2026-01-05
- **Implementation**: [Implementation Summary](...)
- **Implemented**: 2026-01-05
- **Effort**: 12 hours
- **Status**: [COMPLETED]
- **Priority**: Medium
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Description**: ...
```

### Root Cause

1. **Missing Canonical Order Specification**: Neither `tasks.md` nor `status-sync-manager.md` explicitly defines the order in which fields should appear in task entries.

2. **Ambiguous Artifact Insertion Logic**: The `artifact_link_update_logic` section in `status-sync-manager.md` (lines 432-455) describes:
   - How to detect artifact types
   - How to replace vs append artifacts
   - Edge case handling
   
   But it does NOT specify:
   - WHERE to insert artifacts relative to standard metadata
   - The canonical field order for task entries

3. **Implementation Gap**: The `step_3_prepare_updates` process (lines 399-549) states:
   ```
   2. Update .opencode/specs/TODO.md task entry in memory:
      - Change status marker
      - Add/update timestamp fields
      - Add artifact links from validated_artifacts (with plan link replacement logic)
      - Add blocking/abandonment reason if applicable
      - Add checkmark to title if completed
   ```
   
   This describes WHAT to update but not the ORDER of operations or final field arrangement.

---

## Canonical Field Order

Based on analysis of correctly formatted tasks (312, 301, 307) and the `tasks.md` standard, the canonical order should be:

### 1. Standard Metadata (Required/Core Fields)
```markdown
- **Effort**: {estimate}
- **Status**: [{STATUS_MARKER}]
- **Priority**: {High|Medium|Low}
- **Language**: {lean|markdown|general|python|shell|json|meta}
- **Blocking**: {None or task numbers}
- **Dependencies**: {None or task numbers}
```

### 2. Artifact Links (Dynamic Fields)
```markdown
- **Research**: [Research Report]({path})
- **Plan**: [Implementation Plan]({path})
- **Implementation**: [Implementation Summary]({path})
```

### 3. Timestamps (Dynamic Fields)
```markdown
- **Researched**: {YYYY-MM-DD}
- **Planned**: {YYYY-MM-DD}
- **Revised**: {YYYY-MM-DD}
- **Implemented**: {YYYY-MM-DD}
- **Completed**: {YYYY-MM-DD}
- **Abandoned**: {YYYY-MM-DD}
```

### 4. Description (Required)
```markdown
**Description**: {2-3 sentence description}
```

### Rationale

1. **Standard metadata first**: These are the core fields that define the task's basic properties and are always present.

2. **Artifact links second**: These are dynamic fields added as the task progresses through workflow stages (research → plan → implement).

3. **Timestamps third**: These record when workflow stages completed and are closely related to artifact links.

4. **Description last**: This is the detailed explanation and should come after all metadata for readability.

---

## Affected Components

### 1. status-sync-manager.md

**Location**: `.opencode/agent/subagents/status-sync-manager.md`

**Issues**:
- Lines 432-455: `artifact_link_update_logic` doesn't specify insertion position
- Lines 399-431: `step_3_prepare_updates` doesn't enforce field order
- Line 168-181: `create_task_flow` template shows correct order but isn't enforced

**Required Changes**:
1. Add explicit field order specification to `artifact_link_update_logic`
2. Add field ordering algorithm to `step_3_prepare_updates`
3. Ensure all update operations preserve canonical order

### 2. tasks.md

**Location**: `.opencode/context/core/standards/tasks.md`

**Issues**:
- Lines 34-49: Lists required/optional fields but not their order
- Lines 77-81: Describes content but not field sequence
- No explicit ordering specification

**Required Changes**:
1. Add "Field Order" section specifying canonical order
2. Provide example task entry showing correct order
3. Add to quality checklist: "Fields appear in canonical order"

### 3. Workflow Commands

**Affected Commands**:
- `/research` - Adds Research artifact link and Researched timestamp
- `/plan` - Adds Plan artifact link and Planned timestamp
- `/revise` - Updates Plan link and adds Revised timestamp
- `/implement` - Adds Implementation artifact link and Implemented timestamp

**Required Changes**:
All commands must pass `validated_artifacts` to status-sync-manager in a way that preserves canonical order when inserted.

---

## Implementation Strategy

### Phase 1: Define Canonical Order

1. **Update tasks.md**:
   - Add "Field Order" section with explicit ordering rules
   - Add example task entry showing correct order
   - Update quality checklist to include field order validation

2. **Update status-sync-manager.md**:
   - Add field ordering specification to `artifact_link_update_logic`
   - Add field ordering algorithm to `step_3_prepare_updates`
   - Document insertion position for each field type

### Phase 2: Implement Field Ordering Algorithm

**Algorithm**:
```
1. Parse existing task entry into field groups:
   - standard_metadata = [Effort, Status, Priority, Language, Blocking, Dependencies]
   - artifact_links = [Research, Plan, Implementation, ...]
   - timestamps = [Researched, Planned, Revised, Implemented, ...]
   - description = "**Description**: ..."

2. When adding new artifact:
   a. Detect artifact type (research, plan, implementation)
   b. Add to artifact_links group (replace if plan, append otherwise)
   c. Add corresponding timestamp to timestamps group

3. Reconstruct task entry in canonical order:
   a. Write standard_metadata fields (preserve existing values)
   b. Write artifact_links fields (sorted by workflow stage order)
   c. Write timestamps fields (sorted by workflow stage order)
   d. Write description

4. Validate final order matches canonical specification
```

### Phase 3: Update Workflow Commands

1. **Verify validated_artifacts format**:
   - Ensure all commands pass artifacts with correct type field
   - Ensure timestamps are included in validated_artifacts

2. **Test field ordering**:
   - Create test task
   - Run /research → verify order
   - Run /plan → verify order
   - Run /implement → verify order
   - Verify order preserved across all stages

### Phase 4: Fix Existing Tasks

1. **Identify non-compliant tasks**:
   ```bash
   # Find tasks with artifacts before standard metadata
   grep -B 5 "^\- \*\*Effort\*\*:" TODO.md | grep "^\- \*\*Research\*\*:"
   ```

2. **Automated fix script**:
   - Parse each task entry
   - Reorder fields to canonical order
   - Preserve all content
   - Validate result

3. **Manual review**:
   - Review automated fixes
   - Verify no data loss
   - Commit changes

---

## Validation Criteria

### Field Order Validation

**Check**: Fields appear in canonical order
```
1. Standard metadata (Effort, Status, Priority, Language, Blocking, Dependencies)
2. Artifact links (Research, Plan, Implementation)
3. Timestamps (Researched, Planned, Revised, Implemented)
4. Description
```

**Test Cases**:
1. Create new task → verify order
2. Add research artifact → verify order preserved
3. Add plan artifact → verify order preserved
4. Add implementation artifact → verify order preserved
5. Update status → verify order preserved

### Consistency Validation

**Check**: All tasks in TODO.md follow canonical order

**Test**:
```bash
# Extract all task entries
# Parse field order for each
# Verify matches canonical order
# Report violations
```

---

## Recommendations

### Immediate Actions

1. **Document canonical order** in tasks.md (high priority)
2. **Update status-sync-manager** to enforce order (high priority)
3. **Fix task 313** as proof of concept (medium priority)

### Long-term Improvements

1. **Add field order validation** to /review command
2. **Create automated fix script** for non-compliant tasks
3. **Add field order tests** to validation suite
4. **Update all workflow commands** to preserve order

### Quality Assurance

1. **Pre-commit hook**: Validate task field order before commit
2. **CI/CD check**: Verify all tasks comply with canonical order
3. **Documentation**: Add field order examples to all workflow command docs

---

## References

### Files Analyzed

1. `.opencode/specs/TODO.md` (lines 1061-1077: Task 313, lines 33-48: Task 312)
2. `.opencode/agent/subagents/status-sync-manager.md` (lines 399-549: update logic)
3. `.opencode/context/core/standards/tasks.md` (lines 34-49: field definitions)
4. `.opencode/context/index.md` (context loading patterns)

### Related Tasks

- Task 312: Fix workflow command postflight failures (correct field order example)
- Task 313: Configure opencode agent system (incorrect field order example)
- Task 314: Standardize TODO.md task entry format (this task)

### Standards Referenced

- `tasks.md`: Task entry format standards
- `status-sync-manager.md`: Atomic update protocol
- `delegation.md`: Return format standards
- `state-management.md`: Status markers and transitions

---

## Conclusion

The inconsistent field ordering in task 313 stems from missing canonical order specification in both `tasks.md` and `status-sync-manager.md`. The solution requires:

1. **Explicit order specification** in tasks.md
2. **Field ordering algorithm** in status-sync-manager.md
3. **Validation** in workflow commands
4. **Automated fixes** for existing non-compliant tasks

This standardization will improve:
- **Consistency**: All tasks follow same format
- **Parseability**: Automated tools can reliably extract fields
- **Readability**: Users can quickly scan task metadata
- **Maintainability**: Clear standards reduce errors

**Next Steps**: Create implementation plan for phased rollout of canonical field order specification and enforcement.
