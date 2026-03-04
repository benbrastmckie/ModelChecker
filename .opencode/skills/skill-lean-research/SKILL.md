---
name: skill-lean-research
description: Research skill for Lean 4 theorem prover and Mathlib
allowed_tools: Read, Write, Edit, Bash, WebSearch, WebFetch, Grep, Glob, mcp__lean-lsp__*
context: project/lean4
---

# Lean Research Skill

Routes Lean 4 research tasks to lean-research-agent.

## Usage

Invoked by orchestrator when task language is `lean4` and operation is research.

## Agent

- **Agent**: lean-research-agent
- **Model**: opus

## Context

- Lean 4 syntax and semantics
- Mathlib library overview
- MCP tools for proof assistance
