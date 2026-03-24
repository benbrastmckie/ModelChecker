---
paths: specs/**/*
---

# Artifact Format Rules

## Placeholder Conventions

Placeholders in path templates and content follow these conventions:

| Placeholder | Format | Usage | Examples |
|-------------|--------|-------|----------|
| `{N}` | Unpadded integer | Task numbers in text, commits | `389`, `task 389:` |
| `{NNN}` | 3-digit padded | Directory numbers | `014`, `{NNN}_{SLUG}` |
| `{P}` | Unpadded integer | Phase numbers | `1`, `phase 1:` |
| `{DATE}` | YYYYMMDD | Date stamps in filenames | `20260111` |
| `{ISO_DATE}` | YYYY-MM-DD | ISO dates in content | `2026-01-11` |
| `{SLUG}` | snake_case | Task slug from title | `fix_bug_name` |

**Key distinction**: Task numbers in text and JSON (`{N}`) remain unpadded for readability. Directory names and artifact versions (`{NNN}`) use 3-digit zero-padding for proper lexicographic sorting.

**System-specific directory prefixes**:
- Claude Code tasks: `specs/{NNN}_{SLUG}/` (no prefix)
- OpenCode tasks: `specs/OC_{NNN}_{SLUG}/` (OC_ prefix)

## Artifact Naming Convention

All task artifacts use the `MM_{short-slug}.md` format:
- `MM` = Zero-padded sequence number within task (01, 02, 03...)
- `{short-slug}` = 3-5 word kebab-case description

### Slug Generation Rules
1. Extract 3-5 most significant words from task title
2. Convert to kebab-case (lowercase, spaces to hyphens)
3. Remove: articles (a, an, the), prepositions (in, on, at, of), conjunctions (and, or, for, to)
4. Keep: main nouns, verbs, adjectives that capture task essence

### Per-Type Sequential Numbering
Each artifact type maintains its own independent sequence within a task:
- **Reports**: 01, 02, 03... (research reports, chronological)
- **Plans**: 01, 02, 03... (plan versions, sequential)
- **Summaries**: 01, 02, 03... (execution summaries, follows plan execution)

## Phase Status Markers

Use in plan files:
- `[NOT STARTED]` - Phase not begun
- `[IN PROGRESS]` - Currently executing
- `[COMPLETED]` - Phase finished
- `[PARTIAL]` - Partially complete (interrupted)
- `[BLOCKED]` - Cannot proceed

## Versioning

### Research Reports
- `01_initial-research.md`, `02_deep-dive-analysis.md`
- Multiple reports for same task allowed
- Later reports supplement earlier ones

### Plans
- `02_design-approach.md`, `03_revised-design.md`
- New version = revised approach
- Previous versions preserved for history

### Summaries
- `04_implementation-summary.md`
- One per completion
- Includes all phases

## Artifact Linking in TODO.md

Use count-aware format from `.claude/rules/state-management.md`:
- Single artifact (1): Use inline format `- **Type**: [file](path)`
- Multiple artifacts (2+): Use multi-line list format with 2-space indentation

## Template Reference

For complete artifact templates (research reports, implementation plans, summaries, error reports), see:
- [Artifact Templates](.claude/context/core/reference/artifact-templates.md)
