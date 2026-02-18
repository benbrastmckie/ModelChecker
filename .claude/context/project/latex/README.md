# LaTeX Context README

## Purpose

LaTeX-specific context for the ModelChecker paper using the Springer Nature Journal Article Template (sn-jnl.cls v3.1) for submission to the Journal of Automated Reasoning.

## Project Structure

```
latex/
├── paper.tex              # Main document (single file per Springer requirement)
├── paper.pdf              # Compiled output
├── sn-jnl.cls             # Springer Nature document class
├── sn-mathphys-num.bst    # Bibliography style (numbered citations)
├── latexmkrc              # Build configuration
├── assets/                # Template files (backup/reference)
│   ├── sn-jnl.cls         # Document class (backup)
│   ├── sn-*.bst           # All bibliography styles
│   └── user-manual.pdf    # Springer template documentation
├── bibliography/          # Bibliography files
│   └── references.bib     # Reference database
└── figures/               # Figure files (PDF/PNG/JPG for pdflatex)
```

## Canonical Source

- **Project README**: `latex/README.md` - Complete template documentation and submission requirements
- **Template Manual**: `latex/assets/user-manual.pdf` - Official Springer template documentation

## LaTeX-Specific Files

### Standards
- `standards/sn-article-requirements.md` - Springer Nature sn-article template requirements (CRITICAL)
- `standards/latex-style-guide.md` - Document formatting rules, **semantic linefeeds**
- `standards/document-structure.md` - Single-file sn-jnl document organization

### Rules (Auto-Loaded)
- `../../rules/latex.md` - Formatting rules triggered automatically for `.tex` files

### Patterns
- `patterns/theorem-environments.md` - sn-jnl theorem styles (thmstyleone, thmstyletwo, thmstylethree)
- `patterns/cross-references.md` - Labels, refs, and citation patterns

### Tools
- `tools/compilation-guide.md` - latexmk build process and troubleshooting

## When to Load

Load these files when:
1. Creating or modifying the ModelChecker paper
2. Adding mathematical content (theorems, proofs, definitions)
3. Preparing for JAR submission
4. Troubleshooting compilation issues

**Note**: The `.claude/rules/latex.md` rules file loads automatically when editing `.tex` files, enforcing semantic linefeeds and other formatting conventions.

## Key Requirements

### Single-File Format
Springer Nature requires submission as a single .tex file. Do NOT use:
- `\input{}` or `\include{}`
- `subfiles` package
- Any external .tex includes

### Required Declarations
All papers must include a Declarations section with:
- Funding
- Conflict of interest
- Code availability (REQUIRED for computational papers)
- Data availability

### Theorem Environments
Use the sn-jnl predefined styles:
- `thmstyleone`: theorem, proposition, lemma, corollary
- `thmstyletwo`: example, remark
- `thmstylethree`: definition

See `standards/sn-article-requirements.md` for complete details.
