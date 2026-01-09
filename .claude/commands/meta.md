---
description: Interactive system builder for agent architectures
allowed-tools: Read, Write, Edit, Glob, Grep, Bash(git:*), Task, TodoWrite, WebSearch
argument-hint: [DOMAIN] | --analyze | --generate
model: claude-opus-4-5-20251101
---

# /meta Command

Interactive system builder for creating agent architectures, commands, and skills.

## Arguments

- No args: Start interactive interview
- `DOMAIN` - Direct domain specification
- `--analyze` - Analyze existing .claude/ structure
- `--generate` - Generate from previous interview

## Modes

### Interactive Mode (Default)

Multi-stage interview process to design agent system.

#### Stage 1: Domain Discovery

```
What domain will this system support?
Examples: "API development", "data pipeline", "game engine", "ML workflow"

Domain: {user_input}
```

#### Stage 2: Use Case Gathering

```
What are the main use cases?
1. {use_case_1}
2. {use_case_2}
3. {use_case_3}
(Enter blank line when done)
```

#### Stage 3: Workflow Analysis

```
For each use case, what's the typical workflow?

Use case: {use_case_1}
Steps:
1. {step}
2. {step}
...
```

#### Stage 4: Tool Requirements

```
What tools/integrations are needed?
- [ ] Web search
- [ ] File operations
- [ ] Git operations
- [ ] External APIs
- [ ] Build tools
- [ ] Testing frameworks
- [ ] Custom MCP servers

Selected: {tools}
```

#### Stage 5: Complexity Assessment

```
System complexity:
- Simple: 2-3 commands, 1-2 skills
- Medium: 4-6 commands, 3-5 skills
- Complex: 7+ commands, 6+ skills

Assessment: {level}
```

#### Stage 6: Architecture Design

Based on interview, propose:

```
Proposed Architecture:

Commands:
1. /{command1} - {description}
2. /{command2} - {description}
...

Skills:
1. {skill1} - {when invoked}
2. {skill2} - {when invoked}
...

Rules:
1. {rule1}.md - {scope}
...

Proceed with generation? (y/n)
```

#### Stage 7: Generation

Generate files:
- `.claude/commands/{command}.md` for each command
- `.claude/skills/{skill}/SKILL.md` for each skill
- `.claude/rules/{rule}.md` for each rule
- Update `.claude/CLAUDE.md` with new patterns

#### Stage 8: Validation

Verify generated files:
- Check frontmatter is valid
- Check tool references exist
- Check no circular dependencies

### Analyze Mode (--analyze)

Examine existing .claude/ structure:

```
Current .claude/ Structure:

Commands ({N}):
- /{command1} - {description}
- /{command2} - {description}

Skills ({N}):
- {skill1} - {description}
- {skill2} - {description}

Rules ({N}):
- {rule1}.md - {paths}

Settings:
- Permissions: {N} allow, {N} deny
- Hooks: {N} configured

Recommendations:
1. {suggestion}
2. {suggestion}
```

### Generate Mode (--generate)

Re-run generation from last interview session.

## Generation Templates

### Command Template

```markdown
---
description: {description}
allowed-tools: {tools}
argument-hint: {hint}
model: claude-opus-4-5-20251101
---

# /{command} Command

{documentation}

## Arguments

- `$1` - {arg description}

## Execution

### 1. {Step}

{details}

### 2. {Step}

{details}

## Output

{expected output format}
```

### Skill Template

```markdown
---
name: {skill-name}
description: {when to invoke}
allowed-tools: {tools}
context: fork
---

# {Skill Name}

## Trigger Conditions

This skill activates when:
- {condition}

## Execution

{steps}

## Return Format

{format}
```

### Rule Template

```markdown
---
paths: {glob pattern}
---

# {Rule Title}

## {Section}

{content}
```

## Output

```
Meta system builder complete.

Generated:
- {N} commands
- {N} skills
- {N} rules

Files created:
- .claude/commands/{...}.md
- .claude/skills/{...}/SKILL.md
- .claude/rules/{...}.md

Updated:
- .claude/CLAUDE.md

Next steps:
1. Review generated files
2. Test commands: /{command1}, /{command2}
3. Adjust as needed
```
