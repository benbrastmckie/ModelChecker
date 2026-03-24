# skill-memory

Memory vault management skill for the /learn command.

## Purpose

Handles memory creation, similarity search, classification, and index maintenance for the Obsidian-compatible memory vault.

## Modes

### Standard Mode

Add text or file content as memory:
- Parse input (text vs file)
- Generate unique memory ID
- Search for similar existing memories
- Present preview with options
- Create memory file with YAML frontmatter
- Update index

### Task Mode

Review task artifacts and create classified memories:
- Locate task directory
- Scan artifact files
- Present interactive selection
- Classify each artifact (TECHNIQUE, PATTERN, CONFIG, WORKFLOW, INSIGHT, SKIP)
- Create categorized memories
- Update index with category grouping

## Files

- `SKILL.md` - Skill definition and execution flow

## Navigation

- [Parent Directory](../README.md)
