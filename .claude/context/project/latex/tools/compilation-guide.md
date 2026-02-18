# LaTeX Compilation Guide

## Quick Reference

### Full Build (Recommended)

```bash
cd latex
latexmk -pdf paper.tex
```

### Manual Build (with bibliography)

```bash
cd latex
pdflatex paper.tex
bibtex paper
pdflatex paper.tex
pdflatex paper.tex
```

### Clean Up

```bash
latexmk -c          # Clean auxiliary files, keep PDF
latexmk -C          # Clean everything including PDF
```

## Project Configuration

### latexmkrc File

The project includes a `latexmkrc` configuration file:

```perl
# latexmkrc - Build configuration for ModelChecker paper
# Use with: latexmk -pdf paper.tex

# Use pdflatex
$pdf_mode = 1;
$pdflatex = 'pdflatex -interaction=nonstopmode -synctex=1 %O %S';

# Use bibtex for bibliography
$bibtex_use = 2;
$bibtex = 'bibtex %O %B';

# Clean up extra files
$clean_ext = 'synctex.gz synctex.gz(busy) run.xml tex.bak bbl bcf fdb_latexmk run tdo %R-blx.bib';

# Additional output files to clean
@generated_exts = (@generated_exts, 'synctex.gz', 'run.xml');
```

### Configuration Options

| Option | Value | Description |
|--------|-------|-------------|
| `$pdf_mode` | 1 | Use pdflatex |
| `-interaction=nonstopmode` | - | Don't stop on errors |
| `-synctex=1` | - | Enable SyncTeX for editor integration |
| `$bibtex_use` | 2 | Run bibtex when needed |

## Build Process

### Step 1: Initial Compilation

```bash
pdflatex paper.tex
```

- Generates auxiliary files (.aux, .toc, .out)
- Cross-references will show as "??"

### Step 2: Bibliography

```bash
bibtex paper
```

- Processes references.bib
- Generates .bbl file
- Must run after first pdflatex

### Step 3: Resolve References

```bash
pdflatex paper.tex
pdflatex paper.tex
```

- Two runs to resolve all cross-references
- First run incorporates bibliography
- Second run finalizes TOC and references

## Directory Structure

```
latex/
├── paper.tex              # Main document
├── paper.pdf              # Output (generated)
├── paper.aux              # Auxiliary (generated)
├── paper.log              # Log file (generated)
├── paper.bbl              # Bibliography (generated)
├── paper.blg              # BibTeX log (generated)
├── latexmkrc              # Build configuration
├── sn-jnl.cls             # Document class
├── sn-mathphys-num.bst    # Bibliography style
├── bibliography/
│   └── references.bib     # Reference database
├── figures/               # Figure files
└── assets/                # Template backup files
```

## Common Errors

### Undefined Control Sequence

```
! Undefined control sequence.
l.42 \somecommand
```

**Cause**: Missing package or undefined command
**Fix**: Add `\usepackage{...}` or check spelling

### Missing $ Inserted

```
! Missing $ inserted.
l.55 The formula A → B
```

**Cause**: Math mode not entered for formulas
**Fix**: Wrap in `$...$` or use `\to` instead of →

### Undefined Citation

```
LaTeX Warning: Citation 'author2024' on page 3 undefined
```

**Cause**: BibTeX not run, or key missing from .bib
**Fix**: Run `bibtex paper` and check key exists in references.bib

### Undefined Reference

```
LaTeX Warning: Reference 'thm:soundness' on page 5 undefined
```

**Cause**: Missing label or need to run pdflatex again
**Fix**: Add `\label{thm:soundness}` or run pdflatex twice

### Overfull Hbox

```
Overfull \hbox (15.2pt too wide) in paragraph at lines 42--45
```

**Cause**: Line too long
**Fix**: Break equation with `align` environment or reword text

### Package Not Found

```
! LaTeX Error: File 'somepackage.sty' not found.
```

**Cause**: Package not installed
**Fix**: Install via TeX distribution: `tlmgr install somepackage`

## Output Verification

### Check PDF

1. Open generated PDF
2. Verify cross-references resolved (no "??")
3. Check bibliography appears
4. Verify mathematical formatting
5. Check figure placement

### Log File Review

```bash
grep -i "warning\|error" paper.log
```

### Common Warnings to Address

- `Label ... multiply defined` - duplicate labels
- `Reference ... undefined` - missing label
- `Citation ... undefined` - missing bibliography entry
- `Overfull \hbox` - line breaking issues

### Acceptable Warnings

- `Underfull \hbox` - minor, usually ignorable
- Font substitution warnings - if output looks correct

## Required Packages

### Included in sn-jnl.cls

The document class automatically loads:
- `natbib` - Citation management
- `hyperref` - Hyperlinks

### Standard Packages (usually pre-installed)

- `amsmath`, `amssymb`, `amsfonts` - Mathematical typesetting
- `amsthm` - Theorem environments
- `graphicx` - Figure inclusion
- `booktabs` - Professional tables

### May Need Installation

```bash
tlmgr install algorithm algorithmicx listings manyfoot appendix
```

## Troubleshooting

### Fresh Start

```bash
latexmk -C paper.tex
latexmk -pdf paper.tex
```

### Debug Mode

```bash
pdflatex -interaction=errorstopmode paper.tex
```

Stops at first error for detailed inspection.

### Verbose Output

Check `paper.log` for detailed error messages and line numbers.

### SyncTeX Issues

If editor integration fails:
1. Delete `paper.synctex.gz`
2. Recompile with `latexmk -pdf paper.tex`

## Continuous Compilation

For development with auto-rebuild on save:

```bash
latexmk -pdf -pvc paper.tex
```

**Note**: Requires a PDF viewer that supports auto-reload.
