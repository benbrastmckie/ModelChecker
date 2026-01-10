---
last_updated: 2026-01-10T22:30:00Z
next_project_number: 6
task_counts:
  active: 1
  completed: 1
  in_progress: 0
---

# TODO

---

## High Priority

### 5. Fix /task command implementation bug
- **Effort**: 30 minutes
- **Status**: [NOT STARTED]
- **Priority**: High
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Description**: Fix the /task command which interprets task descriptions as instructions to execute rather than text to record. Apply the solution from .claude/specs/task-command-implementation-bug.md: (1) Restrict allowed-tools to only .claude/specs/* paths, (2) Add prominent "CRITICAL" section explaining $ARGUMENTS is a DESCRIPTION to record, not instructions to execute, (3) Strengthen Constraints section with HARD STOP and explicit forbidden actions list.

**Files Affected**:
- .claude/commands/task.md

---

## Medium Priority

### 4. Reorganize Claude Code documentation to avoid redundancy
- **Effort**: 1-2 hours
- **Status**: [COMPLETED]
- **Started**: 2026-01-10
- **Researched**: 2026-01-10
- **Planned**: 2026-01-10
- **Completed**: 2026-01-10
- **Priority**: Medium
- **Language**: general
- **Blocking**: None
- **Dependencies**: None
- **Research**: [.claude/specs/004_reorganize_claude_code_docs/reports/research-001.md]
- **Plan**: [.claude/specs/004_reorganize_claude_code_docs/plans/implementation-001.md]
- **Summary**: [.claude/specs/004_reorganize_claude_code_docs/summaries/implementation-summary-20260110.md]

**Description**: Review .claude/docs/guides/user-installation.md and Docs/installation/CLAUDE_CODE.md to avoid redundancy. Consider removing user-installation.md in preference of a revised CLAUDE_CODE.md with appropriate cross-links to docs in .claude/. Determine the best way to reorganize information between these files.

**Files Affected**:
- Docs/installation/CLAUDE_CODE.md (add agent commands section)
- .claude/docs/guides/user-installation.md (delete)
- .claude/docs/guides/copy-claude-directory.md (update links)
- .claude/docs/README.md (update links)
- .claude/context/project/modelchecker/installation.md (update links)

---

## Low Priority

---

## Archived

<details>
<summary>3 tasks archived on 2026-01-10</summary>

- #1: Create .claude/ directory copy instructions (completed 2026-01-10)
- #2: Improve metadata system for task tracking (completed 2026-01-10)
- #3: Update documentation for zero-padding standard (completed 2026-01-10)

See `.claude/specs/archive/state.json` for full details.
</details>
