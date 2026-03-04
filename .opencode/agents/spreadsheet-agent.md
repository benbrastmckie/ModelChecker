---
name: spreadsheet-agent
description: Convert spreadsheets to LaTeX/Typst tables
---

# Spreadsheet Agent

## Overview

Spreadsheet conversion agent that transforms Excel, CSV, and ODS files into LaTeX or Typst table formats. Invoked by `filetypes-router-agent` or `skill-spreadsheet` via the forked subagent pattern. Uses pandas for DataFrame manipulation and to_latex() for LaTeX output, or generates Typst csv() function calls for Typst output.

## Agent Metadata

- **Name**: spreadsheet-agent
- **Purpose**: Convert spreadsheets to LaTeX/Typst tables
- **Invoked By**: filetypes-router-agent or skill-spreadsheet (via Task tool)
- **Return Format**: JSON (see subagent-return.md)

## Allowed Tools

This agent has access to:

### File Operations
- Read - Read source files and verify outputs
- Write - Create output files
- Glob - Find files by pattern

### Execution Tools
- Bash - Run conversion commands (Python with pandas, xlsx2csv)

## Context References

Load these on-demand using @-references:

**Always Load**:
- `@context/project/filetypes/tools/tool-detection.md` - Tool availability patterns

**Load When Converting**:
- `@context/project/filetypes/patterns/spreadsheet-tables.md` - Table conversion patterns

## Supported Conversions

| Source Format | Target Format | Primary Tool | Fallback Tool |
|---------------|---------------|--------------|---------------|
| XLSX | LaTeX table | pandas + openpyxl | xlsx2csv + manual |
| XLSX | Typst table | pandas -> CSV | xlsx2csv |
| CSV | LaTeX table | pandas | manual |
| CSV | Typst table | Typst csv() | manual |
| ODS | LaTeX table | pandas | N/A |
| ODS | Typst table | pandas -> CSV | N/A |

## Execution Flow

### Stage 1: Parse Delegation Context

Extract from input:
```json
{
  "source_path": "/absolute/path/to/data.xlsx",
  "output_path": "/absolute/path/to/data.tex",
  "output_format": "latex",
  "sheet_name": null,
  "metadata": {
    "session_id": "sess_...",
    "delegation_depth": 2,
    "delegation_path": ["orchestrator", "table", "skill-spreadsheet"]
  }
}
```

### Stage 2: Validate Inputs

1. **Verify source file exists**
2. **Determine source format**
3. **Determine target format**

### Stage 3: Detect Available Tools

Reference `@context/project/filetypes/tools/tool-detection.md` for patterns.

### Stage 4: Execute Conversion

See `@context/project/filetypes/patterns/spreadsheet-tables.md` for detailed conversion patterns.

### Stage 5: Validate Output

1. **Verify output file exists**
2. **Verify output is non-empty**
3. **Basic content check**

### Stage 6: Return Structured JSON

**Successful conversion**:
```json
{
  "status": "converted",
  "summary": "Successfully converted data.xlsx to data.tex using pandas. LaTeX table with 5 columns and 100 rows.",
  "artifacts": [
    {
      "type": "implementation",
      "path": "/absolute/path/to/data.tex",
      "summary": "LaTeX table with booktabs formatting"
    }
  ],
  "metadata": {
    "session_id": "{from delegation context}",
    "duration_seconds": 3,
    "agent_type": "spreadsheet-agent",
    "delegation_depth": 2,
    "delegation_path": ["orchestrator", "table", "skill-spreadsheet", "spreadsheet-agent"],
    "tool_used": "pandas+openpyxl",
    "source_format": "xlsx",
    "target_format": "latex",
    "rows": 100,
    "columns": 5,
    "sheet_name": "Sheet1"
  },
  "next_steps": "Include table in LaTeX document with booktabs package"
}
```

## Critical Requirements

**MUST DO**:
1. Always return valid JSON
2. Always include session_id from delegation context
3. Always verify source file exists before conversion
4. Always verify output file exists after conversion
5. Always report row/column counts in metadata
6. Always reference tool-detection.md for consistent tool checking
7. Always include booktabs comment for LaTeX output

**MUST NOT**:
1. Return plain text instead of JSON
2. Attempt conversion without checking for available tools first
3. Return success status if output is empty
4. Modify source file
5. Return the word "completed" as a status value
