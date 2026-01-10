---
last_updated: 2026-01-10T20:00:00Z
next_project_number: 4
task_counts:
  active: 1
  completed: 2
  in_progress: 0
---

# TODO

---

## High Priority

### 2. Improve metadata system for task tracking
- **Effort**: 4-6 hours
- **Status**: [COMPLETED]
- **Started**: 2026-01-10
- **Researched**: 2026-01-10
- **Planned**: 2026-01-10
- **Completed**: 2026-01-10
- **Priority**: High
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None
- **Research**: [.claude/specs/002_improve_metadata_system/reports/research-001.md]
- **Plan**: [.claude/specs/002_improve_metadata_system/plans/implementation-001.md]
- **Summary**: [.claude/specs/002_improve_metadata_system/summaries/implementation-summary-20260110.md]

**Description**: Enhance the .claude/ metadata system by adopting valuable patterns from ProofChecker while keeping ModelChecker-specific needs in mind. This includes: (1) Adding timestamp fields to task entries (Started, Researched, Planned, Implementing, Completed) for lifecycle tracking, (2) Adding task_counts to TODO.md frontmatter for at-a-glance statistics, (3) Updating all command files (/task, /research, /plan, /implement, /todo) to maintain these new fields consistently, (4) Updating state-management.md and artifact-formats.md rules to document the new schema, (5) Ensuring all metadata updates are atomic and synchronized between TODO.md and state.json.

**Files Affected**:
- .claude/specs/TODO.md (schema update)
- .claude/specs/state.json (schema update)
- .claude/commands/task.md
- .claude/commands/research.md
- .claude/commands/plan.md
- .claude/commands/implement.md
- .claude/commands/todo.md
- .claude/rules/state-management.md
- .claude/rules/artifact-formats.md

---

### 1. Create .claude/ directory copy instructions for Claude Code users
- **Effort**: 2-3 hours
- **Status**: [COMPLETED]
- **Started**: 2026-01-10
- **Researched**: 2026-01-10
- **Planned**: 2026-01-10
- **Completed**: 2026-01-10
- **Priority**: High
- **Language**: general
- **Blocking**: None
- **Dependencies**: None
- **Research**: [.claude/specs/001_claude_directory_copy_instructions/reports/research-001.md]
- **Plan**: [.claude/specs/001_claude_directory_copy_instructions/plans/implementation-001.md]
- **Summary**: [.claude/specs/001_claude_directory_copy_instructions/summaries/implementation-summary-20260110.md]

**Description**: Create a document in .claude/docs/guides/ that explains how to clone and copy the .claude/ directory from the ModelChecker repository (providing the full GitHub URL) into the root directory from which a Claude Code instance is running. Then include an instruction step in /home/benjamin/Projects/ModelChecker/.claude/docs/guides/user-installation.md which directs the user to pass the URL to this document to Claude Code to follow those instructions to copy .claude/ into the directory. Then direct the user to restart Claude Code and test the commands, providing a link to /home/benjamin/Projects/ModelChecker/.claude/docs/commands/README.md for further information. URLs in user-installation.md intended for pasting into Claude Code must be full URLs (not relative paths).

**Files Affected**:
- .claude/docs/guides/copy-claude-directory.md (new)
- .claude/docs/guides/user-installation.md (update)

---

## Medium Priority

---

## Low Priority

### 3. Update documentation for zero-padding standard
- **Effort**: 30 minutes
- **Status**: [NOT STARTED]
- **Priority**: Low
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Description**: Update relevant documentation or context files to enforce the zero-padded directory naming standard (003_slug format) without bloating documentation or over-representing the issue. Add minimal references where needed.

**Files Affected**:
- .claude/CLAUDE.md (if task artifact paths mentioned)
- Other context files as needed

---
