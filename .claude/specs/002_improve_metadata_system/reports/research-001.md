# Research Report: Task #2

**Task**: Improve metadata system for task tracking
**Date**: 2026-01-10
**Focus**: Analyze ProofChecker metadata patterns and identify improvements for ModelChecker

## Summary

ProofChecker has a more mature metadata system with timestamp tracking, task statistics in frontmatter, and detailed artifact metadata. ModelChecker has the core infrastructure (skill-status-sync, commands) but lacks these enhancements. The recommended approach is to adopt a subset of ProofChecker patterns that provide value without adding unnecessary complexity for a Python/Z3 project.

## Findings

### 1. ProofChecker TODO.md Frontmatter (Enhanced)

ProofChecker includes rich statistics in the frontmatter:

```yaml
---
last_updated: 2026-01-09T12:00:00Z
next_project_number: 351
repository_health:
  overall_score: 92
  production_readiness: excellent
  last_assessed: 2026-01-05T02:00:00Z
task_counts:
  active: 49
  completed: 67
  in_progress: 2
  not_started: 43
  abandoned: 7
  total: 124
priority_distribution:
  high: 17
  medium: 22
  low: 14
technical_debt:
  sorry_count: 6        # Lean-specific (sorry placeholders)
  axiom_count: 11       # Lean-specific (axiom declarations)
  build_errors: 11
  status: well-documented
---
```

**Applicable to ModelChecker**: `task_counts` and `priority_distribution`
**NOT applicable**: `technical_debt` (Lean-specific), `repository_health` (overkill for simpler project)

### 2. ProofChecker Task Entry Format (Enhanced)

ProofChecker task entries include lifecycle timestamps:

```markdown
### 350. Task title
- **Effort**: 6-8 hours
- **Status**: [IMPLEMENTING]
- **Started**: 2026-01-10
- **Researched**: 2026-01-10
- **Planned**: 2026-01-10
- **Priority**: High
- **Language**: markdown
- **Blocking**: None
- **Dependencies**: None

**Research Artifacts**:
  - Research Report: [.claude/specs/350_slug/reports/research-001.md]

**Plan Artifacts**:
  - Implementation Plan: [.claude/specs/350_slug/plans/implementation-001.md]

**Description**: ...
```

**Key additions**: `Started`, `Researched`, `Planned`, `Implementing`, `Completed` timestamps

### 3. ProofChecker state.json Task Entry (Enhanced)

```json
{
  "project_number": 350,
  "project_name": "fix_recursive_semantics_tags",
  "status": "implementing",
  "language": "markdown",
  "priority": "high",
  "effort": "6-8 hours",
  "created": "2026-01-10T18:17:28Z",
  "last_updated": "2026-01-10T18:41:35Z",
  "artifacts": [
    ".claude/specs/350_slug/reports/research-001.md",
    ".claude/specs/350_slug/plans/implementation-001.md"
  ],
  "plan_path": ".claude/specs/350_slug/plans/implementation-001.md",
  "plan_metadata": {
    "plan_version": 1
  },
  "implementing_started": "2026-01-10"
}
```

**Key additions**: `artifacts` array, `plan_path`, `plan_metadata`, lifecycle dates

### 4. Current ModelChecker State

**TODO.md frontmatter** (minimal):
```yaml
---
last_updated: 2026-01-10T19:00:00Z
next_project_number: 3
---
```

**state.json task entry** (basic):
```json
{
  "project_number": 1,
  "project_name": "claude_directory_copy_instructions",
  "status": "completed",
  "language": "general",
  "priority": "high",
  "effort": "2-3 hours",
  "created": "2026-01-10T18:18:00Z",
  "last_updated": "2026-01-10T18:18:00Z"
}
```

**Missing**: lifecycle timestamps, artifact tracking, task_counts, priority_distribution

### 5. Command Files Analysis

All ModelChecker commands currently:
- Update `status` field correctly
- Update `last_updated` timestamp
- Add artifact links to TODO.md entries

**Missing updates**:
| Command | Currently Missing |
|---------|------------------|
| `/task` | frontmatter task_counts |
| `/research` | `started` timestamp (if not set), `researched` timestamp |
| `/plan` | `planned` timestamp |
| `/implement` | `implementing_started`, `completed` timestamps |
| `/todo` | frontmatter task_counts recalculation |

### 6. skill-status-sync Analysis

ModelChecker's skill-status-sync is functional but needs:
- Timestamp fields for lifecycle tracking
- Artifact array management
- Frontmatter statistics updates

## Recommendations

### 1. Adopt Selective Frontmatter Statistics

Add to TODO.md frontmatter (simpler than ProofChecker):
```yaml
---
last_updated: ISO_DATE
next_project_number: N
task_counts:
  active: N
  completed: N
  in_progress: N
---
```

**Skip**: `repository_health`, `technical_debt`, `priority_distribution` (overkill)

### 2. Add Lifecycle Timestamps to Task Entries

Update TODO.md entry format:
```markdown
### N. Title
- **Effort**: estimate
- **Status**: [STATUS]
- **Priority**: priority
- **Language**: language
- **Blocking**: None
- **Dependencies**: None
- **Started**: ISO_DATE (when status first leaves NOT STARTED)
- **Researched**: ISO_DATE (when research completes)
- **Planned**: ISO_DATE (when plan completes)
- **Completed**: ISO_DATE (when implementation completes)
```

### 3. Enhance state.json Task Schema

Add to each task entry:
```json
{
  "started": "ISO_DATE",      // When first transitioned from not_started
  "researched": "ISO_DATE",   // When research completed
  "planned": "ISO_DATE",      // When planning completed
  "completed": "ISO_DATE",    // When implementation completed
  "artifacts": ["path1", "path2"]  // Array of artifact paths
}
```

### 4. Update Commands in Phases

**Phase 1**: Update state-management.md and artifact-formats.md with new schema
**Phase 2**: Update skill-status-sync to handle new fields
**Phase 3**: Update commands to pass timestamp data:
  - `/task`: Initialize `task_counts` if missing
  - `/research`: Set `started` (if null), set `researched`
  - `/plan`: Set `planned`
  - `/implement`: Set `completed`
  - `/todo`: Recalculate `task_counts`

### 5. Keep It Simple

Avoid over-engineering:
- **Don't** add repository_health (manual maintenance burden)
- **Don't** add technical_debt metrics (not relevant to Python/Z3)
- **Do** add task_counts (auto-calculable from tasks)
- **Do** add lifecycle timestamps (minimal overhead, high value)

## References

- ProofChecker TODO.md: `/home/benjamin/Projects/ProofChecker/.claude/specs/TODO.md`
- ProofChecker state.json: `/home/benjamin/Projects/ProofChecker/.claude/specs/state.json`
- ProofChecker skill-status-sync: `/home/benjamin/Projects/ProofChecker/.claude/skills/skill-status-sync/SKILL.md`
- ModelChecker skill-status-sync: `.claude/skills/skill-status-sync/SKILL.md`
- ModelChecker state-management.md: `.claude/rules/state-management.md`

## Next Steps

1. **Create implementation plan** with phases:
   - Phase 1: Schema documentation updates
   - Phase 2: skill-status-sync enhancement
   - Phase 3: Command file updates
   - Phase 4: Verification and testing

2. **Consider migration strategy** for existing Task 1:
   - Add missing timestamps retroactively
   - Initialize task_counts in frontmatter

3. **Define rollback plan**:
   - Changes are additive (new fields)
   - Existing functionality should remain intact
