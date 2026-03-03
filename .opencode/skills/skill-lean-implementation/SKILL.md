---
name: skill-lean-implementation
description: Implementation skill for Lean 4 proofs and definitions
allowed_tools: Read, Write, Edit, Bash, Grep, Glob, mcp__lean-lsp__*
context: project/lean4
---

# Lean Implementation Skill

Routes Lean 4 implementation tasks to lean-implementation-agent.

## Usage

Invoked by orchestrator when task language is `lean4` and operation is implementation.

## Agent

- **Agent**: lean-implementation-agent
- **Model**: default

## Context

- Lean 4 tactic patterns
- Proof structure templates
- MCP tools for proof assistance
