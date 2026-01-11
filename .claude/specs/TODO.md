---
last_updated: 2026-01-11T01:15:00Z
next_project_number: 8
task_counts:
  active: 2
  completed: 2
  in_progress: 0
---

# TODO

---

## High Priority

### 5. Fix /task command implementation bug
- **Effort**: 30 minutes
- **Status**: [COMPLETED]
- **Started**: 2026-01-11
- **Researched**: 2026-01-11
- **Planned**: 2026-01-11
- **Completed**: 2026-01-11
- **Priority**: High
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None
- **Research**: [.claude/specs/005_fix_task_command_implementation_bug/reports/research-001.md]
- **Plan**: [.claude/specs/005_fix_task_command_implementation_bug/plans/implementation-002.md] (v2)
- **Summary**: [.claude/specs/005_fix_task_command_implementation_bug/summaries/implementation-summary-20260111.md]

**Description**: Fix the /task command which interprets task descriptions as instructions to execute rather than text to record. Expanded scope: verify alignment across ModelChecker, ProofChecker (reference), and Global config (~/.config/.claude). Also addresses global config task #11.

**Outcome**: Verification-only task. Security fix was already applied to all three agent systems. Created alignment comparison document.

---

## Medium Priority

### 7. Document gh CLI setup and issue creation
- **Effort**: 30-60 minutes
- **Status**: [NOT STARTED]
- **Priority**: Medium
- **Language**: general
- **Blocking**: None
- **Dependencies**: None

**Description**: In /home/benjamin/Projects/ModelChecker/Docs/installation/CLAUDE_CODE.md, include details about how to get Claude Code to install the gh CLI, help you configure the gh CLI, and then use the gh CLI to create issues when issues occur.

---

### 6. Create model-checker researcher skill
- **Effort**: 2-4 hours
- **Status**: [RESEARCHED]
- **Started**: 2026-01-11
- **Researched**: 2026-01-11
- **Planned**: 2026-01-11
- **Priority**: Medium
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None
- **Research**: [.claude/specs/006_model_checker_skill/reports/research-001.md], [.claude/specs/006_model_checker_skill/reports/research-002.md]
- **Plan**: [.claude/specs/006_model_checker_skill/plans/implementation-001.md]

**Description**: Research the model-checker usage patterns carefully in order to create a skill that is geared for using the model-checker in all of the standard ways, including defining new operators, adjusting frame constraints, running tests, and reporting findings in order to help researchers streamline their work with the model-checker using claude code to facilitate everything.

---

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
