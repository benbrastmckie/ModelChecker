---
name: skill-spreadsheet
description: Spreadsheet to table conversion routing
allowed-tools: Task
---

# Spreadsheet Skill

Thin wrapper that routes spreadsheet-to-table operations to the `spreadsheet-agent`.

## Trigger Conditions

This skill activates when:

### Direct Invocation
- User explicitly runs `/table` command
- User requests spreadsheet to table conversion in conversation

### Implicit Invocation
- Plan steps mentioning spreadsheet/Excel/CSV to LaTeX/Typst conversion

### When NOT to trigger

Do not invoke for:
- Document conversions (use skill-filetypes)
- Presentation conversions (use skill-presentation)

## Execution

### 1. Input Validation
- Validate source file exists
- Validate source is spreadsheet format (.xlsx, .xls, .csv, .ods)
- Determine output path and format

### 2. Context Preparation
Prepare delegation context with source_path, output_path, output_format, sheet_name, metadata.

### 3. Invoke Agent
Use Task tool to spawn spreadsheet-agent.

### 4. Return Validation
Validate return matches subagent-return.md schema.

### 5. Return Propagation
Return validated result to caller without modification.

## Return Format

Expected successful return includes status, summary, artifacts, and metadata with row/column counts.
