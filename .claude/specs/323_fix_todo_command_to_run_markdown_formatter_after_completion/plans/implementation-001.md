# Implementation Plan: Fix /todo Command Markdown Formatting

**Task**: 323 - Fix /todo command to run markdown formatter after completion
**Created**: 2026-01-07
**Status**: [NOT STARTED]
**Estimated Effort**: 4 hours
**Complexity**: Medium
**Language**: meta

---

## Metadata

- **Task Number**: 323
- **Plan Version**: 1
- **Research Integrated**: Yes
- **Reports Integrated**:
  - reports/research-001.md (2026-01-05)

---

## Overview

### Problem Statement

The /todo command successfully archives completed and abandoned tasks but does not apply comprehensive markdown formatting to TODO.md after archival operations. This results in formatting inconsistencies that accumulate over time:

- Multiple consecutive blank lines (8+ in some sections)
- Inconsistent spacing around dividers and headings
- Trailing whitespace not systematically removed
- Inconsistent list formatting and indentation

The current `todo_cleanup.py` script includes `fix_divider_stacking()` but lacks comprehensive markdown formatting capabilities.

### Research Integration

This plan integrates findings from research-001.md (2026-01-05):

**Key Findings**:
- Current cleanup script handles divider stacking but not comprehensive formatting
- Three viable approaches identified: mdformat integration, custom formatter, extend cleanup script
- Recommended approach: Custom lightweight formatter (no external dependencies, TODO.md-specific rules)
- Implementation complexity: ~150 lines of Python
- Performance: ~5ms overhead (vs ~50ms for mdformat)

**Recommended Formatting Rules** (from research):
1. Preserve frontmatter (YAML between --- markers)
2. Preserve code blocks (fenced or indented)
3. Remove trailing whitespace from all lines
4. Normalize blank lines (max 2 consecutive)
5. Ensure blank line before/after headings (## and ###)
6. Ensure blank line before/after dividers (---)
7. Ensure single trailing newline at EOF

### Scope

**In Scope**:
- Create custom markdown formatter script (format_markdown.py)
- Implement TODO.md-specific formatting rules
- Integrate formatter into /todo command Stage 4
- Add error handling for formatting failures (non-critical)
- Test formatter with current TODO.md
- Document formatting rules

**Out of Scope**:
- mdformat integration (external dependency)
- Formatting other markdown files (future enhancement)
- Pre-commit hook integration (future enhancement)
- CI validation (future enhancement)

### Constraints

- No external dependencies (no mdformat, no Prettier)
- Formatting failure must be non-critical (doesn't abort archival)
- Must preserve frontmatter and code blocks
- Must not break TODO.md structure
- Performance: < 30ms overhead for typical TODO.md

### Definition of Done

- [NOT STARTED] format_markdown.py script created and tested
- [NOT STARTED] Formatter integrated into /todo command Stage 4
- [NOT STARTED] TODO.md formatting validated after test archival
- [NOT STARTED] Error handling for formatting failures implemented
- [NOT STARTED] Formatting rules documented in script header
- [NOT STARTED] All tests pass (frontmatter, code blocks, edge cases)

---

## Goals and Non-Goals

### Goals

1. Create lightweight custom markdown formatter (~150 lines)
2. Apply consistent formatting to TODO.md after archival
3. Preserve frontmatter, code blocks, and content structure
4. Integrate formatter into /todo command workflow
5. Handle formatting failures gracefully (non-critical)

### Non-Goals

1. Format other markdown files (Documentation/, research reports)
2. Add mdformat as external dependency
3. Implement pre-commit hooks
4. Add CI validation for formatting
5. Support advanced markdown features (GFM tables, etc.)

---

## Risks and Mitigations

### Risk 1: Custom Formatter Bugs

**Likelihood**: Medium  
**Impact**: Medium (formatting errors in TODO.md)

**Mitigation**:
- Comprehensive test suite for edge cases
- Test on copy of TODO.md before deployment
- Git rollback available if issues detected
- Formatting failure non-critical (doesn't abort archival)

### Risk 2: Breaking TODO.md Structure

**Likelihood**: Low  
**Impact**: High (TODO.md becomes unreadable or unparseable)

**Mitigation**:
- Preserve frontmatter and code blocks explicitly
- Test with current TODO.md before deployment
- Git rollback available via /todo command's two-phase commit
- Validation step before formatting

### Risk 3: Performance Impact

**Likelihood**: Low  
**Impact**: Low (slight increase in /todo command execution time)

**Mitigation**:
- Lightweight implementation (~5ms overhead)
- Timeout protection (30s max)
- Non-blocking (doesn't delay archival)

---

## Implementation Phases

### Phase 1: Create Markdown Formatter Script [NOT STARTED]

**Estimated Effort**: 1.5 hours

**Objectives**:
- Create `.opencode/scripts/format_markdown.py`
- Implement formatting rules from research
- Add comprehensive docstrings and usage examples

**Tasks**:
1. Create script file with header and imports
2. Implement helper functions:
   - `is_frontmatter_delimiter()` - Detect YAML frontmatter
   - `is_code_fence()` - Detect code blocks
   - `is_heading()` - Detect headings (## and ###)
   - `is_divider()` - Detect dividers (---)
3. Implement main `format_markdown()` function:
   - State tracking (frontmatter, code blocks)
   - Trailing whitespace removal
   - Blank line normalization (max 2 consecutive)
   - Heading/divider spacing enforcement
   - EOF normalization (single trailing newline)
4. Implement `main()` entry point:
   - Argument parsing (file path, --check flag)
   - File reading/writing
   - Error handling
   - Exit codes (0: success, 1: needs formatting, 2: file error)
5. Add comprehensive docstrings and usage examples

**Acceptance Criteria**:
- Script runs without errors
- All helper functions implemented
- format_markdown() applies all 7 formatting rules
- --check flag works correctly
- Exit codes correct

**Dependencies**: None

---

### Phase 2: Test Formatter with TODO.md [NOT STARTED]

**Estimated Effort**: 1 hour

**Objectives**:
- Test formatter with current TODO.md
- Validate formatting rules
- Test edge cases

**Tasks**:
1. Create test copy of TODO.md:
   ```bash
   cp .opencode/specs/TODO.md /tmp/TODO-test.md
   ```
2. Run formatter on test copy:
   ```bash
   python3 .opencode/scripts/format_markdown.py /tmp/TODO-test.md
   ```
3. Validate formatting:
   - Check frontmatter preserved
   - Check task blocks intact
   - Check blank lines normalized (max 2)
   - Check heading/divider spacing
   - Check trailing whitespace removed
   - Check single trailing newline
4. Test edge cases:
   - Empty sections (heading with no content)
   - Dividers at start/end of file
   - Nested lists with mixed indentation
   - Code blocks with --- or ### in content
5. Compare before/after with diff:
   ```bash
   diff -u .opencode/specs/TODO.md /tmp/TODO-test.md
   ```
6. Fix any bugs discovered

**Acceptance Criteria**:
- Formatter preserves all content
- All formatting rules applied correctly
- Edge cases handled properly
- No data loss or corruption
- Diff shows only formatting changes

**Dependencies**: Phase 1

---

### Phase 3: Integrate Formatter into /todo Command [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Add formatter invocation to /todo command Stage 4
- Implement error handling for formatting failures
- Update documentation

**Tasks**:
1. Update `.opencode/command/todo.md` Stage 4:
   - Add formatter invocation after cleanup script
   - Add timeout (30 seconds)
   - Add error handling (non-critical failure)
2. Modify Stage 4 process:
   ```markdown
   4. Format TODO.md (NEW):
      - Command: python3 .opencode/scripts/format_markdown.py .opencode/specs/TODO.md
      - Capture stdout, stderr, exit code
      - Timeout: 30 seconds
   5. Check formatting exit code:
      - 0: Success, proceed to GitPostCommit
      - Non-zero: Log warning, continue (formatting failure non-critical)
   ```
3. Update error handling section:
   - Add formatting_failure case
   - Log to errors.json
   - Continue to GitPostCommit (non-critical)
4. Update validation section:
   - Add mid_flight check for formatting
   - Add post_flight check for formatting

**Acceptance Criteria**:
- /todo command invokes formatter after cleanup
- Formatting failure doesn't abort archival
- Error handling logs failures
- Documentation updated

**Dependencies**: Phase 2

---

### Phase 4: End-to-End Testing [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Test complete /todo workflow with formatting
- Validate git commits include formatted changes
- Test error scenarios

**Tasks**:
1. Create test scenario:
   - Mark 1-2 tasks as completed in state.json
   - Run /todo command
   - Verify archival succeeds
   - Verify TODO.md formatted correctly
2. Validate git commits:
   - Check pre-cleanup snapshot commit
   - Check archival commit includes formatted TODO.md
   - Verify commit messages correct
3. Test error scenarios:
   - Simulate formatting script failure (chmod -x)
   - Verify archival continues
   - Verify error logged
   - Restore script permissions
4. Test rollback scenario:
   - Simulate cleanup script failure
   - Verify rollback includes formatted TODO.md
   - Verify state restored correctly
5. Validate formatting quality:
   - Check blank lines normalized
   - Check heading/divider spacing
   - Check trailing whitespace removed
   - Check frontmatter preserved

**Acceptance Criteria**:
- /todo command completes successfully
- TODO.md properly formatted after archival
- Git commits include formatted changes
- Error scenarios handled gracefully
- Rollback works correctly

**Dependencies**: Phase 3

---

### Phase 5: Documentation and Cleanup [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Document formatting rules
- Update relevant documentation
- Clean up test artifacts

**Tasks**:
1. Add formatting rules to script header:
   - Document all 7 formatting rules
   - Add usage examples
   - Add edge case notes
2. Update `.opencode/command/todo.md`:
   - Document formatting step in Stage 4
   - Update validation checklist
   - Update error handling section
3. Consider adding formatting note to TODO.md header:
   - Optional: Add comment about automatic formatting
   - Document formatting standards
4. Clean up test artifacts:
   - Remove /tmp/TODO-test.md
   - Remove any test commits (if needed)
5. Verify all documentation accurate

**Acceptance Criteria**:
- Script header documents all rules
- /todo command documentation updated
- Test artifacts cleaned up
- Documentation accurate and complete

**Dependencies**: Phase 4

---

## Testing and Validation

### Unit Tests

**Formatter Script Tests**:
1. Test frontmatter preservation:
   - YAML between --- markers preserved
   - Content after frontmatter formatted
2. Test code block preservation:
   - Fenced code blocks (```) preserved
   - Indented code blocks preserved
   - Content with --- or ### in code blocks preserved
3. Test blank line normalization:
   - 3+ consecutive blank lines → 2 blank lines
   - Blank lines at start/end of file removed
4. Test heading spacing:
   - Blank line before ## and ###
   - Blank line after ## and ###
5. Test divider spacing:
   - Blank line before ---
   - Blank line after ---
6. Test trailing whitespace removal:
   - All lines trimmed
   - No trailing spaces
7. Test EOF normalization:
   - Single trailing newline
   - No multiple trailing newlines

### Integration Tests

**/todo Command Tests**:
1. Test archival with formatting:
   - Archive 1 task
   - Verify TODO.md formatted
   - Verify git commit includes formatting
2. Test formatting failure handling:
   - Simulate script failure
   - Verify archival continues
   - Verify error logged
3. Test rollback with formatting:
   - Simulate cleanup failure
   - Verify rollback restores pre-formatted state

### Edge Case Tests

1. Empty sections (heading with no content)
2. Dividers at start/end of file
3. Nested lists with mixed indentation
4. Code blocks with markdown syntax in content
5. Frontmatter with --- in YAML values
6. Very large TODO.md (1000+ lines)

---

## Artifacts and Outputs

### Primary Artifacts

1. **format_markdown.py** (`.opencode/scripts/format_markdown.py`)
   - Custom markdown formatter script
   - ~150 lines of Python
   - Implements 7 formatting rules
   - Includes comprehensive docstrings

2. **Updated /todo Command** (`.opencode/command/todo.md`)
   - Stage 4 modified to invoke formatter
   - Error handling for formatting failures
   - Updated documentation

### Supporting Artifacts

1. **Test Results**
   - Formatter unit test results
   - Integration test results
   - Edge case test results

2. **Documentation Updates**
   - Script header documentation
   - /todo command documentation
   - Optional TODO.md header note

---

## Rollback/Contingency

### Rollback Plan

If formatter causes issues:

1. **Immediate Rollback**:
   ```bash
   git revert <commit-hash>  # Revert formatter integration commit
   ```

2. **Remove Formatter Invocation**:
   - Edit `.opencode/command/todo.md` Stage 4
   - Remove formatter invocation step
   - Commit changes

3. **Verify Archival Still Works**:
   - Run /todo command
   - Verify archival succeeds without formatting

### Contingency Plan

If custom formatter proves insufficient:

1. **Option A: Fix Bugs**:
   - Identify specific formatting issues
   - Fix formatter script
   - Re-test thoroughly

2. **Option B: Migrate to mdformat**:
   - Install mdformat: `pip install mdformat mdformat-frontmatter`
   - Update /todo command to invoke mdformat
   - Remove custom formatter script
   - Update documentation

3. **Option C: Disable Formatting**:
   - Remove formatter invocation from /todo command
   - Keep cleanup script only
   - Accept formatting inconsistencies

---

## Success Metrics

### Quantitative Metrics

1. **Formatting Quality**:
   - 0 consecutive blank lines > 2
   - 100% trailing whitespace removed
   - 100% headings/dividers with proper spacing
   - 1 trailing newline at EOF

2. **Performance**:
   - Formatter execution time < 30ms
   - /todo command overhead < 5%
   - No timeout failures

3. **Reliability**:
   - 0 formatting failures in normal operation
   - 100% archival success rate (formatting non-critical)
   - 0 data loss incidents

### Qualitative Metrics

1. **Code Quality**:
   - Script well-documented (comprehensive docstrings)
   - Error handling robust
   - Edge cases handled

2. **User Experience**:
   - TODO.md consistently formatted
   - No manual formatting needed
   - Archival workflow unchanged

3. **Maintainability**:
   - Simple, readable code (~150 lines)
   - Easy to extend with new rules
   - Clear documentation

---

## Phase Summary

| Phase | Effort | Dependencies | Status |
|-------|--------|--------------|--------|
| Phase 1: Create Formatter Script | 1.5 hours | None | [NOT STARTED] |
| Phase 2: Test Formatter | 1 hour | Phase 1 | [NOT STARTED] |
| Phase 3: Integrate into /todo | 0.5 hours | Phase 2 | [NOT STARTED] |
| Phase 4: End-to-End Testing | 0.5 hours | Phase 3 | [NOT STARTED] |
| Phase 5: Documentation | 0.5 hours | Phase 4 | [NOT STARTED] |
| **Total** | **4 hours** | | |

---

## Notes

- Research recommends custom formatter over mdformat (no external dependencies)
- Formatting failure is non-critical (doesn't abort archival)
- Git rollback available via /todo command's two-phase commit
- Future enhancement: extend formatter to other markdown files
- Future enhancement: add pre-commit hooks and CI validation

---

**End of Implementation Plan**
