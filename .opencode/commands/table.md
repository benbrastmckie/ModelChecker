---
description: Convert spreadsheets to LaTeX or Typst tables
allowed-tools: Skill, Bash(jq:*), Bash(test:*), Bash(dirname:*), Bash(basename:*), Read
argument-hint: SOURCE_PATH [OUTPUT_PATH] [--format latex|typst]
---

# /table Command

Convert spreadsheet files to LaTeX or Typst table format.

## Arguments

- `$1` - Source file path (required): XLSX, CSV, or ODS file
- `$2` - Output file path (optional, inferred from source if not provided)
- `--format` - Output format: `latex` (default) or `typst`
- `--sheet` - Sheet name for multi-sheet workbooks (optional)

## Usage Examples

```bash
# XLSX to LaTeX (default)
/table data.xlsx                         # -> data.tex

# XLSX to Typst
/table data.xlsx output.typ --format typst

# CSV to LaTeX with explicit output
/table budget.csv budget.tex --format latex

# Specific sheet from workbook
/table workbook.xlsx summary.tex --sheet "Q4 Data"
```

## Supported Conversions

| Source | Target | Notes |
|--------|--------|-------|
| XLSX | LaTeX | Uses pandas + openpyxl, booktabs format |
| XLSX | Typst | Uses pandas, generates csv() or tabut table |
| CSV | LaTeX | Uses pandas DataFrame.to_latex() |
| CSV | Typst | Uses Typst csv() function |
| ODS | LaTeX | Uses pandas |
| ODS | Typst | Uses pandas via CSV intermediate |

## Execution

### CHECKPOINT 1: GATE IN
1. Generate Session ID
2. Parse Arguments
3. Validate Source File Exists
4. Validate Source Format
5. Determine Output Path

### STAGE 2: DELEGATE
Invoke skill-spreadsheet with source_path, output_path, output_format, sheet_name, session_id.

### CHECKPOINT 2: GATE OUT
1. Validate Return
2. Verify Output File Exists
3. Verify Output Non-Empty

### CHECKPOINT 3: COMMIT (Optional)
Git commit if requested.

## Output

**Success**:
```
Table conversion complete!

Source: {source_path}
Output: {output_path}
Format: {output_format}
Size:   {rows} rows x {columns} columns
```
