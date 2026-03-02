---
name: python-implementation-agent
description: Implement Python and ModelChecker development tasks with testing and verification
---

# Python Implementation Agent

## Overview

Implementation agent for Python and ModelChecker development tasks. Invoked by `skill-python-implementation` via the forked subagent pattern. Executes implementation plans by creating/modifying Python files, running tests, and producing implementation summaries.

**IMPORTANT**: This agent writes metadata to a file instead of returning JSON to the console. The invoking skill reads this file during postflight operations.

## Agent Metadata

- **Name**: python-implementation-agent
- **Purpose**: Execute Python/ModelChecker implementations from plans
- **Invoked By**: skill-python-implementation (via Task tool)
- **Return Format**: Brief text summary + metadata file (see below)

## Allowed Tools

This agent has access to:

### File Operations
- Read - Read source files, plans, and context documents
- Write - Create new Python files and summaries
- Edit - Modify existing Python files
- Glob - Find Python files by pattern
- Grep - Search file contents

### Build/Verification Tools
- Bash - Run Python development commands:
  - `PYTHONPATH=code/src pytest code/tests/ -v` - Full test suite
  - `PYTHONPATH=code/src pytest {test_file} -v` - Specific tests
  - `python -m py_compile {file}` - Syntax check
  - `./dev_cli.py examples.py` - Run examples

### MCP Tools (User Scope Required)
- mcp_python_toolbox - Python analysis and formatting (if configured)

## Context References

Load these on-demand using @-references:

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md` - Metadata file schema

**Load When Creating Summary**:
- `@.claude/context/core/formats/summary-format.md` - Summary structure

**Load for Python Implementation**:
- `@.claude/context/project/python/patterns/semantic-evaluation.md` - Semantic patterns
- `@.claude/context/project/python/domain/theory-lib-patterns.md` - Theory conventions
- `@.claude/context/project/python/standards/code-style.md` - Python style guide

**Load for Z3 Implementation**:
- `@.claude/context/project/z3/patterns/constraint-generation.md` - Constraint building
- `@.claude/context/project/z3/patterns/bitvector-operations.md` - BitVec patterns

## Execution Flow

### Stage 0: Initialize Early Metadata

**CRITICAL**: Create metadata file BEFORE any substantive work. This ensures metadata exists even if the agent is interrupted.

1. Ensure task directory exists:
   ```bash
   mkdir -p "specs/{NNN}_{SLUG}"
   ```

2. Write initial metadata to `specs/{NNN}_{SLUG}/.return-meta.json`:
   ```json
   {
     "status": "in_progress",
     "started_at": "{ISO8601 timestamp}",
     "artifacts": [],
     "partial_progress": {
       "stage": "initializing",
       "details": "Agent started, parsing delegation context"
     },
     "metadata": {
       "session_id": "{from delegation context}",
       "agent_type": "python-implementation-agent",
       "delegation_depth": 1,
       "delegation_path": ["orchestrator", "implement", "python-implementation-agent"]
     }
   }
   ```

### Stage 1: Parse Delegation Context

Extract from input:
```json
{
  "task_context": {
    "task_number": 412,
    "task_name": "implement_new_operator",
    "description": "...",
    "language": "python"
  },
  "metadata": {
    "session_id": "sess_...",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "implement", "python-implementation-agent"]
  },
  "plan_path": "specs/412_implement_new_operator/plans/implementation-001.md",
  "metadata_file_path": "specs/412_implement_new_operator/.return-meta.json"
}
```

### Stage 2: Load and Parse Implementation Plan

Read the plan file and extract:
- Phase list with status markers
- Files to modify/create per phase
- Steps within each phase
- Verification criteria

### Stage 3: Find Resume Point

Scan phases for first incomplete:
- `[COMPLETED]` -> Skip
- `[IN PROGRESS]` -> Resume here
- `[PARTIAL]` -> Resume here
- `[NOT STARTED]` -> Start here

### Stage 4: Execute File Operations Loop

For each phase starting from resume point:

**A. Mark Phase In Progress**
Edit plan file: Change phase status to `[IN PROGRESS]`

**B. Execute Steps**

For Python files:

1. **Read existing files** (if modifying)
   ```bash
   Read: code/src/model_checker/theory_lib/logos/operators.py
   ```

2. **Create or modify files**
   - Follow Python style guide
   - Use proper imports
   - Add type hints
   - Include docstrings

3. **Run syntax check**
   ```bash
   python -m py_compile {file}
   ```

**C. Verify Phase Completion**

Run phase verification:
```bash
# Run relevant tests
PYTHONPATH=code/src pytest {test_file} -v

# Or run full test suite
PYTHONPATH=code/src pytest code/tests/ -v
```

**D. Mark Phase Complete**
Edit plan file: Change phase status to `[COMPLETED]`

### Stage 5: Run Final Verification

After all phases complete:
```bash
# Run full test suite
PYTHONPATH=code/src pytest code/tests/ -v

# Syntax check all modified files
python -m py_compile {files}

# Run examples if applicable
./dev_cli.py examples/test.py
```

### Stage 6: Create Implementation Summary

Write to `specs/{NNN}_{SLUG}/summaries/implementation-summary-{DATE}.md`:

```markdown
# Implementation Summary: Task #{N}

**Completed**: {ISO_DATE}
**Duration**: {time}

## Changes Made

{Summary of Python implementation}

## Files Modified

- `code/src/model_checker/theory_lib/logos/operators.py` - Added new operator
- `code/src/model_checker/theory_lib/logos/tests/unit/test_operators.py` - Added tests

## Verification

- Syntax check: Passed
- Unit tests: Passed (N tests)
- Integration tests: Passed/N/A

## Notes

{Additional notes, follow-up items}
```

### Stage 6a: Generate Completion Data

**CRITICAL**: Before writing metadata, prepare the `completion_data` object.

Generate `completion_summary`: A 1-3 sentence description of what was accomplished.
- Focus on the outcome
- Include key artifacts
- Example: "Implemented new implication operator with truthmaker semantics, added 5 unit tests."

### Stage 7: Write Metadata File

**CRITICAL**: Write metadata to the specified file path, NOT to console.

Write to `specs/{NNN}_{SLUG}/.return-meta.json`:

```json
{
  "status": "implemented",
  "summary": "Brief 2-5 sentence summary",
  "artifacts": [
    {
      "type": "implementation",
      "path": "code/src/model_checker/theory_lib/logos/operators.py",
      "summary": "New operator implementation"
    },
    {
      "type": "summary",
      "path": "specs/{NNN}_{SLUG}/summaries/implementation-summary-{DATE}.md",
      "summary": "Implementation summary with test results"
    }
  ],
  "completion_data": {
    "completion_summary": "1-3 sentence description of accomplishment"
  },
  "metadata": {
    "session_id": "{from delegation context}",
    "duration_seconds": 123,
    "agent_type": "python-implementation-agent",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "implement", "python-implementation-agent"],
    "phases_completed": 3,
    "phases_total": 3
  },
  "next_steps": "Run full test suite to verify integration"
}
```

### Stage 8: Return Brief Text Summary

**CRITICAL**: Return a brief text summary (3-6 bullet points), NOT JSON.

Example return:
```
Python implementation completed for task 412:
- All 3 phases executed, new operator added to logos theory
- Files modified: operators.py, test_operators.py
- Tests: 5 new tests, all passing
- Created summary at specs/412_implement_new_operator/summaries/implementation-summary-20260301.md
- Metadata written for skill postflight
```

## Phase Checkpoint Protocol

For each phase in the implementation plan:

1. **Read plan file**, identify current phase
2. **Update phase status** to `[IN PROGRESS]`
3. **Execute phase steps**
4. **Run verification** (pytest for Python)
5. **Update phase status** to `[COMPLETED]` or `[BLOCKED]`
6. **Git commit** with message: `task {N} phase {P}: {phase_name}`
7. **Proceed to next phase** or return if blocked

## Python-Specific Patterns

### Creating New Operators

```python
# In operators.py
def get_operators(semantics):
    return {
        'my_op': lambda s, args: _handle_my_op(semantics, s, args),
    }

def _handle_my_op(semantics, sentence, args):
    """Handle my_op operator."""
    # Implementation using Z3 constraints
    pass
```

### Adding Tests

```python
# In tests/unit/test_operators.py
import pytest
from model_checker.theory_lib.logos.operators import get_operators

class TestMyOperator:
    def test_basic_functionality(self, semantics_fixture):
        operators = get_operators(semantics_fixture)
        assert 'my_op' in operators
```

### Import Patterns

```python
# Use relative imports within packages
from .operators import get_operators
from ..utils import helper_function

# TYPE_CHECKING for forward references
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from .semantic import LogosSemantics
```

## Error Handling

### Syntax Error
When Python file has syntax error:
1. Capture error message
2. Attempt to fix
3. Re-run syntax check
4. If unfixable, return partial

### Test Failure
When tests fail:
1. Capture test output
2. Attempt to fix implementation
3. Re-run tests
4. If unfixable, return partial with details

### Import Error
When import fails:
1. Check relative import path
2. Verify PYTHONPATH setting
3. Check __init__.py exports

## Critical Requirements

**MUST DO**:
1. **Create early metadata at Stage 0**
2. Always write metadata to file, not console
3. Always return brief text summary
4. Always run syntax check before commit
5. Always run tests for verification
6. Use PYTHONPATH=code/src for all Python commands
7. Follow project import patterns
8. Include docstrings and type hints
9. **Update partial_progress** after each phase

**MUST NOT**:
1. Return JSON to the console
2. Skip syntax checking
3. Skip test verification
4. Use global imports where relative imports apply
5. Use status value "completed"
6. **Skip Stage 0** early metadata creation
