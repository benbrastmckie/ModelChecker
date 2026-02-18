# ModelChecker LaTeX Paper

This directory contains the LaTeX source for the ModelChecker paper, configured for submission to the **Journal of Automated Reasoning** (Springer Nature).

## Template Information

- **Template**: Springer Nature Journal Article Template v3.1 (December 2024)
- **Reference Style**: sn-mathphys-num (Math and Physical Sciences, Numbered)
- **Document Class**: sn-jnl.cls

## Directory Structure

```
latex/
├── paper.tex              # Main document (single file per Springer requirement)
├── paper.pdf              # Compiled output
├── sn-jnl.cls            # Springer Nature document class
├── sn-mathphys-num.bst   # Bibliography style (primary)
├── latexmkrc             # Build configuration
├── README.md             # This file
├── assets/               # Template files (backup/reference)
│   ├── sn-jnl.cls       # Document class (backup)
│   ├── sn-*.bst         # All bibliography styles
│   └── user-manual.pdf  # Springer template documentation
├── bibliography/         # Bibliography files
│   └── references.bib   # Reference database
└── figures/              # Figure files (PDF/PNG/JPG for pdflatex)
```

## File Descriptions

### Main Files

| File | Description |
|------|-------------|
| `paper.tex` | Main LaTeX document. **Submit this as a single file.** |
| `sn-jnl.cls` | Springer Nature document class (required for compilation) |
| `sn-mathphys-num.bst` | Bibliography style for numbered citations |

### Supporting Files

| File | Description |
|------|-------------|
| `assets/user-manual.pdf` | Complete template documentation from Springer |
| `bibliography/references.bib` | BibTeX database for citations |
| `figures/` | Directory for figure files |

### Bibliography Styles (in assets/)

| Style | Use Case |
|-------|----------|
| `sn-mathphys-num.bst` | **Primary** - Numbered citations (for JAR) |
| `sn-mathphys-ay.bst` | Author-year citations |
| `sn-basic.bst` | Basic Springer Nature style |
| `sn-nature.bst` | Nature Portfolio journals |
| `sn-aps.bst` | American Physical Society |
| `sn-vancouver-num.bst` | Vancouver numbered |
| `sn-vancouver-ay.bst` | Vancouver author-year |
| `sn-apacite.bst` | APA style |
| `sn-chicago.bst` | Chicago humanities style |

## Journal Requirements

### Journal of Automated Reasoning (JAR)

- **Publisher**: Springer Nature
- **Reference Style**: Numbered citations (sn-mathphys-num)
- **Document Format**: Single .tex file (no `\input` or subfiles)
- **Figures**: Separate files, not embedded in .tex

### Springer Nature Policies

#### Code and Data Availability (REQUIRED)

Springer Nature requires a **Code Availability** statement for computational research:

1. **Code Repository**: Deposit code on a persistent repository (Zenodo, GitHub with DOI)
2. **License**: Specify the license under which code is available
3. **Version**: Reference the specific version used in the paper

Example statement:
> The ModelChecker software (version X.Y.Z) is available at https://doi.org/10.5281/zenodo.XXXXXXX under the MIT License.

#### Data Availability

- Describe where data can be accessed
- Use persistent identifiers (DOIs) where possible
- State "Not applicable" if no datasets were generated

### Required Declarations

The Declarations section must include (even if "Not applicable"):

1. **Funding** - Grant numbers and funding sources
2. **Conflict of interest** - Any competing interests
3. **Ethics approval** - For human/animal research
4. **Consent to participate** - For human subjects
5. **Consent for publication** - For identifiable information
6. **Data availability** - Where data can be accessed
7. **Code availability** - Where code can be accessed (REQUIRED for computational papers)
8. **Author contribution** - CRediT-style or prose description

## Build Instructions

### Quick Build

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

### Clean Auxiliary Files

```bash
latexmk -c          # Clean auxiliary files, keep PDF
latexmk -C          # Clean everything including PDF
```

### Required TeX Live Packages

The template requires the following packages (included in TeX Live Full):

- `amsmath`, `amssymb`, `amsfonts` - Mathematical typesetting
- `amsthm` - Theorem environments
- `graphicx` - Figure inclusion
- `booktabs` - Professional tables
- `algorithm`, `algorithmicx`, `algpseudocode` - Algorithm typesetting
- `listings` - Code listings
- `natbib` - Citation management (loaded by sn-jnl.cls)
- `hyperref` - Hyperlinks (loaded by sn-jnl.cls)

## Document Options

### Document Class Options

Modify the `\documentclass` line in `paper.tex`:

```latex
% Standard submission:
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}

% Review copy with double spacing:
\documentclass[referee,pdflatex,sn-mathphys-num]{sn-jnl}

% With line numbers for review:
\documentclass[lineno,pdflatex,sn-mathphys-num]{sn-jnl}
```

### Theorem Environments

Three predefined styles are available:

| Style | Environments | Format |
|-------|-------------|--------|
| `thmstyleone` | theorem, proposition, lemma, corollary | Bold head, italic text |
| `thmstyletwo` | example, remark | Roman head, italic text |
| `thmstylethree` | definition | Bold head, roman text |

## Submission Checklist

Before submission, verify:

- [ ] Single .tex file (no `\input` commands)
- [ ] All figures as separate files (PDF/PNG/JPG)
- [ ] Bibliography compiles without errors
- [ ] All cross-references resolve
- [ ] Declarations section complete
- [ ] Code availability statement with DOI/URL
- [ ] Author information correct
- [ ] Abstract within word limit
- [ ] Keywords appropriate for JAR

### Files to Submit

1. `paper.tex` - Main manuscript
2. `paper.pdf` - Compiled PDF
3. `references.bib` - Bibliography file
4. `sn-jnl.cls` - Document class
5. `sn-mathphys-num.bst` - Bibliography style
6. All figure files (from `figures/`)

## References

- [Journal of Automated Reasoning](https://www.springer.com/journal/10817)
- [Springer Nature Author Guidelines](https://www.springer.com/gp/authors-editors)
- [Springer Editorial Policies](https://www.springer.com/gp/editorial-policies)
- Template User Manual: `assets/user-manual.pdf`
