# Agents

Agent definitions for the Claude Code system. Agents perform execution work for research, implementation, and specialized tasks.

## Agent Files

| Agent | Purpose |
|-------|---------|
| general-research-agent.md | General web/codebase research with web search capabilities |
| general-implementation-agent.md | General file implementation and editing |
| planner-agent.md | Implementation plan creation and task planning |
| meta-builder-agent.md | System building for .claude/ architecture changes |
| code-reviewer-agent.md | Code quality assessment and review |

## Agent Structure

All agents follow the standard frontmatter format:

```yaml
---
name: agent-name
description: Brief description of agent purpose
mode: subagent
temperature: 0.1-1.0
tools:
  read: true/false
  write: true/false
  edit: true/false
  bash: true/false
  task: true/false
---
```

## Usage

Agents are invoked by skills, not directly by users. The orchestrator skill routes tasks to appropriate agents based on language and task type.

## Navigation

- [Parent Directory](../README.md)
- [CLAUDE.md](../CLAUDE.md) - Quick reference
