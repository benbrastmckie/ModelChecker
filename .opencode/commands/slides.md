---
description: Convert presentations to Beamer, Polylux, or Touying slides
allowed-tools: Skill, Bash(jq:*), Bash(test:*), Bash(dirname:*), Bash(basename:*), Read
argument-hint: SOURCE_PATH [OUTPUT_PATH] [--format beamer|polylux|touying]
---

# /slides Command

Convert PowerPoint presentations to academic slide formats.

## Arguments

- `$1` - Source file path (required): PPTX file
- `$2` - Output file path (optional)
- `--format` - Output format: `beamer` (default), `polylux`, or `touying`
- `--theme` - Theme name (optional)

## Usage Examples

```bash
/slides presentation.pptx                # -> presentation.tex (Beamer)
/slides deck.pptx slides.typ --format polylux
/slides talk.pptx talk.typ --format touying
```

## Supported Conversions

| Source | Target | Notes |
|--------|--------|-------|
| PPTX | Beamer | Uses python-pptx + pandoc |
| PPTX | Polylux | Uses python-pptx, generates Typst |
| PPTX | Touying | Uses python-pptx, generates Typst |

## Execution

1. GATE IN: Validate source file and format
2. DELEGATE: Invoke skill-presentation
3. GATE OUT: Verify output file exists
4. COMMIT: Optional git commit
