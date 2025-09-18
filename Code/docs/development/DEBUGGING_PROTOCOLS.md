# Debugging Protocols

**Navigation**: [← Back to Development](../README.md) | [Maintenance Home](../../README.md) | [Feature Implementation →](FEATURE_IMPLEMENTATION.md) | [Testing Framework →](TESTING_FRAMEWORK.md)

**Related Documentation**: 
- [Feature Implementation](FEATURE_IMPLEMENTATION.md) - Development process that includes debugging
- [Testing Framework](TESTING_FRAMEWORK.md) - Testing methods for validation
- [Quality Assurance](../../quality/README.md) - Code quality standards

## Overview

This document provides a systematic debugging protocol for investigating and resolving issues in the ModelChecker codebase. The protocol emphasizes progressive investigation, minimal code modification, and comprehensive documentation.

## Core Principles

1. **Progressive Investigation**: Start with non-invasive methods before modifying code
2. **Documentation First**: Create tracking documents before investigation
3. **Reversible Changes**: All debug modifications must be easily removable
4. **Systematic Approach**: Follow phases to avoid missing critical information
5. **Knowledge Preservation**: Document findings for future reference

## Phase 1: Non-Invasive Investigation

### 1.1 Create Debug Tracking

```bash
# Create debug analysis document
mkdir -p docs/specs/debug
touch docs/specs/debug/XXX_issue_description.md
```

Document template:
```markdown
# Debug Analysis XXX: [Issue Description]

## Issue Summary
[Brief description of the observed problem]

## Reproduction Steps
1. [Step to reproduce]
2. [Expected behavior]
3. [Actual behavior]

## Investigation Log
### Phase 1: Non-invasive Analysis
- [ ] Created minimal test case
- [ ] Analyzed with existing tools
- [ ] Reviewed related code
- [ ] Checked similar issues

### Phase 2: Code Instrumentation (if needed)
- [ ] Created debug branch
- [ ] Added instrumentation
- [ ] Collected debug output
- [ ] Identified root cause

## Test Cases
### Test 1: [Minimal Case]
### Test 2: [Edge Case]
### Test 3: [Complex Case]

## Findings
### Initial Observations
### Root Cause Analysis
### Related Issues

## Solution & Verification
### Proposed Fix
### Test Results
### Performance Impact
```

### 1.2 Use Existing Tools

1. **Check available debug flags**:
   ```bash
   # Common debug flags in ModelChecker
   ./dev_cli.py --help
   ./dev_cli.py example.py -z -p  # Z3 constraints and proof
   ./run_tests.py --verbose       # Verbose test output
   ```

2. **Create minimal reproduction**:
   ```python
   # test_minimal_issue.py
   from model_checker import relevant_imports
   
   # Minimal code that reproduces the issue
   # Remove all unnecessary complexity
   ```

3. **Analyze output systematically**:
   ```bash
   # Capture output
   ./dev_cli.py test_minimal_issue.py > debug_output.txt 2>&1
   
   # Extract relevant information
   grep -E "error|warning|ERROR|WARNING" debug_output.txt
   grep -A10 -B10 "problematic_pattern" debug_output.txt
   ```

### 1.3 External Analysis Scripts

Create standalone scripts to analyze the issue without modifying core code:

```python
# analyze_issue.py
import sys
sys.path.insert(0, 'src')

from model_checker import relevant_modules

# Analysis code that doesn't modify the codebase
# Can access internal structures for investigation
# Print findings and hypotheses
```

### 1.4 Review Related Code

1. **Find similar patterns**:
   ```bash
   # Search for similar code patterns
   grep -r "pattern" src/
   find . -name "*.py" -exec grep -l "pattern" {} \;
   ```

2. **Check git history**:
   ```bash
   # Find when code was last modified
   git log -p --follow path/to/file.py
   git blame path/to/file.py
   ```

3. **Review related issues**:
   ```bash
   # Check existing findings
   ls docs/specs/findings/
   grep -r "similar_issue" docs/specs/
   ```

## Phase 2: Targeted Code Instrumentation

Only proceed to Phase 2 if Phase 1 doesn't reveal the root cause.

### 2.1 Create Debug Branch

```bash
# Create isolated branch for debugging
git checkout -b debug/issue-description
git commit -m "Checkpoint: Starting debug investigation for [issue]"
```

### 2.2 Add Strategic Instrumentation

#### Instrumentation Guidelines

1. **Clear markers for removal**:
   ```python
   # DEBUG: Temporary instrumentation - REMOVE AFTER INVESTIGATION
   print(f"[DEBUG] Variable state: {variable}")
   # END DEBUG
   ```

2. **Minimal and targeted**:
   ```python
   # Good: Specific debug point
   if self._debug_mode:  # Add debug flag to avoid always printing
       print(f"[DEBUG] constraint_count: {len(constraints)}")
   
   # Bad: Excessive logging
   for item in large_list:
       print(f"[DEBUG] {item}")  # Too much output
   ```

3. **Use debug contexts**:
   ```python
   # Add temporary debug mode
   class MyClass:
       def __init__(self):
           self._debug_mode = os.environ.get('DEBUG_MYCLASS', False)
   ```

#### Common Instrumentation Points

1. **Entry/Exit points**:
   ```python
   def problematic_method(self, args):
       # DEBUG: Method entry - REMOVE AFTER INVESTIGATION
       print(f"[DEBUG] Entering {self.__class__.__name__}.problematic_method")
       print(f"[DEBUG] Args: {args}")
       # END DEBUG
       
       result = # ... existing code ...
       
       # DEBUG: Method exit - REMOVE AFTER INVESTIGATION
       print(f"[DEBUG] Exiting with result: {result}")
       # END DEBUG
       
       return result
   ```

2. **State changes**:
   ```python
   # DEBUG: State tracking - REMOVE AFTER INVESTIGATION
   old_state = self.state
   self.state = new_state
   if old_state != new_state:
       print(f"[DEBUG] State change: {old_state} -> {new_state}")
   # END DEBUG
   ```

3. **Constraint/condition evaluation**:
   ```python
   # DEBUG: Constraint analysis - REMOVE AFTER INVESTIGATION
   print(f"[DEBUG] Evaluating constraint: {constraint}")
   result = evaluate(constraint)
   print(f"[DEBUG] Result: {result}")
   # END DEBUG
   ```

### 2.3 Collect and Analyze Debug Output

```bash
# Run with debug instrumentation
DEBUG_MYCLASS=1 ./dev_cli.py test_case.py > debug_trace.txt 2>&1

# Extract debug output
grep "[DEBUG]" debug_trace.txt > debug_only.txt

# Analyze patterns
sort debug_only.txt | uniq -c | sort -nr  # Frequency analysis
```

### 2.4 Progressive Refinement

If initial instrumentation doesn't reveal the issue:

1. **Add deeper instrumentation** in identified problem areas
2. **Create specialized debug scripts** to test hypotheses
3. **Use binary search** to narrow down the problem location

## Phase 3: Root Cause Analysis and Resolution

### 3.1 Document Findings

1. **Update debug analysis** (`docs/specs/debug/XXX_*.md`):
   - Complete all sections
   - Include code snippets
   - Document failed hypotheses

2. **Create findings document** (`docs/specs/findings/XXX_*.md`):
   ```markdown
   # Finding XXX: [Issue Title]
   
   ## Summary
   [One paragraph summary of issue and resolution]
   
   ## Problem Description
   ### Symptoms
   [What was observed]
   
   ### Impact
   [Who/what was affected]
   
   ### Reproduction
   [Minimal steps to reproduce]
   
   ## Root Cause
   [Detailed technical explanation]
   [Include relevant code snippets]
   
   ## Solution
   ### Approach
   [High-level solution strategy]
   
   ### Implementation
   [Specific code changes with diffs]
   
   ## Verification
   ### Test Cases
   [List of test cases used]
   
   ### Results
   - Before fix: [behavior]
   - After fix: [behavior]
   
   ## Lessons Learned
   [Key insights for future development]
   
   ## Related Issues
   - [Links to related findings]
   - [Links to related documentation]
   ```

### 3.2 Implement Fix

1. **Minimal fix first**:
   ```python
   # Implement the simplest fix that resolves the issue
   # Keep debug output initially to verify
   ```

2. **Verify comprehensively**:
   ```bash
   # Run specific tests
   ./run_tests.py specific_test --verbose
   
   # Run related examples
   ./dev_cli.py affected_examples.py
   
   # Check for regressions
   ./run_tests.py --unit
   ```

### 3.3 Clean Up

1. **Remove all debug code**:
   ```bash
   # Find all debug markers
   grep -r "REMOVE AFTER INVESTIGATION" src/
   
   # Remove debug blocks
   find src/ -name "*.py" -exec sed -i '/DEBUG:.*REMOVE AFTER/,/END DEBUG/d' {} \;
   
   # Verify removal
   grep -r "DEBUG" src/ | grep -v "test"  # Should show no temporary debug code
   ```

2. **Create clean commits**:
   ```bash
   # Commit fix
   git add -A
   git commit -m "Fix: [Issue description]

   - Root cause: [brief description]
   - Solution: [brief description]
   - Verified with: [test cases]
   
   Fixes: [issue reference]
   See: docs/specs/findings/XXX_[issue].md"
   ```

3. **Merge or cherry-pick**:
   ```bash
   # Option 1: Merge debug branch
   git checkout main
   git merge debug/issue-description
   
   # Option 2: Cherry-pick only fix commit
   git checkout main
   git cherry-pick [fix-commit-hash]
   
   # Clean up debug branch
   git branch -d debug/issue-description
   ```

## Quick Reference Checklist

### Phase 1: Non-invasive Investigation
- [ ] Create debug tracking document
- [ ] Create minimal reproduction
- [ ] Use existing debug tools (-z, -p, --verbose)
- [ ] Write external analysis scripts
- [ ] Review git history and related issues

### Phase 2: Code Instrumentation (if needed)
- [ ] Create debug branch
- [ ] Add marked instrumentation
- [ ] Use debug flags/modes
- [ ] Collect systematic output
- [ ] Progressively refine

### Phase 3: Resolution
- [ ] Document in specs/debug/
- [ ] Create specs/findings/ document
- [ ] Implement minimal fix
- [ ] Verify comprehensively
- [ ] Remove all debug code
- [ ] Create clean commits

## Debug Patterns

### Pattern: Binary Search Debugging
```python
# When issue is in a long process
def long_process():
    # DEBUG: Checkpoint 1 - REMOVE AFTER INVESTIGATION
    print("[DEBUG] Starting phase 1")
    phase1()
    
    # DEBUG: Checkpoint 2 - REMOVE AFTER INVESTIGATION
    print("[DEBUG] Starting phase 2")
    phase2()
    
    # Narrow down which phase has the issue
```

### Pattern: State Comparison
```python
# When state changes unexpectedly
# DEBUG: State tracking - REMOVE AFTER INVESTIGATION
import copy
old_state = copy.deepcopy(self.state)
operation()
if old_state != self.state:
    print(f"[DEBUG] State diff: {diff(old_state, self.state)}")
# END DEBUG
```

### Pattern: Constraint Verification
```python
# When constraints might be violated
# DEBUG: Constraint checking - REMOVE AFTER INVESTIGATION
for i, constraint in enumerate(constraints):
    satisfied = check(constraint)
    if not satisfied:
        print(f"[DEBUG] Constraint {i} violated: {constraint}")
# END DEBUG
```

## See Also

- [Feature Implementation](FEATURE_IMPLEMENTATION.md) - Development process and coding standards
- [Testing Framework](TESTING_FRAMEWORK.md) - Testing procedures
- [Quality Assurance](../../quality/README.md) - Code quality standards
- [specs/findings/](../specs/findings/) - Historical issues and resolutions

---

**Navigation**: [← Back to Development](../README.md) | [Maintenance Home](../../README.md) | [Feature Implementation →](FEATURE_IMPLEMENTATION.md) | [Testing Framework →](TESTING_FRAMEWORK.md)