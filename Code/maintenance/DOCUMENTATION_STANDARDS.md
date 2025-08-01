# Documentation Standards

[← Unicode Guidelines](UNICODE_GUIDELINES.md) | [Back to Maintenance](README.md) | [README Standards →](README_STANDARDS.md)

## Overview

This document establishes general documentation standards for the ModelChecker codebase. For README-specific standards, see [README_STANDARDS.md](README_STANDARDS.md).

## Core Requirements

- **No Emojis**: Never use emojis anywhere in the codebase, documentation, or output
- **No Unicode in Code Examples**: All code examples must use LaTeX notation
- **Working Examples**: All code examples must be tested and functional
- **Cross-References**: Link between related documentation
- **Formula Standards**: Follow formula formatting standards in all examples

## Directory Structure Display

When showing directory structures in documentation, ensure proper comment alignment:

```markdown
# CORRECT - Comments properly aligned
Docs/
├── README.md                       # This file - documentation hub
├── installation/                   # Modular installation guides
│   ├── BASIC_INSTALLATION.md       # Standard pip installation guide
│   └── TROUBLESHOOTING.md          # Platform-specific solutions
└── GETTING_STARTED.md              # Quick start tutorial for new users

# INCORRECT - Comments too close to file names
Docs/
├── README.md # This file
├── installation/ # Guides
└── GETTING_STARTED.md # Tutorial
```

Tab comments far enough right to avoid conflicts with file names, maintaining vertical alignment.

## Content Organization Principles

### Progressive Disclosure
Start with overview and essential information, then provide detailed content as needed.

### Audience Segmentation
Organize information by user type:
- New users need installation and basic usage
- Researchers need theoretical foundations
- Developers need API references and internals

### Quantitative Specificity
Include concrete numbers:
- "19 operators across 5 subtheories"
- "177 test examples"
- "Supports 4 semantic theories"

### Integration Context
Explain how components fit into the larger framework rather than documenting in isolation.

### Theoretical Grounding
Link implementation to academic foundations where relevant, but keep practical usage primary.

### Practical Usability
Always include:
- Working code examples
- Clear command-line usage
- Expected outputs

### Redundancy Reduction
Cross-reference rather than duplicate:
- "See [EXAMPLES.md](../docs/EXAMPLES.md) for complete structure"
- "Settings documented in [SETTINGS.md](docs/SETTINGS.md)"

### Consistent Navigation
Use standardized link patterns:
```markdown
[← Previous Topic](PREVIOUS.md) | [Back to Parent](../README.md) | [Next Topic →](NEXT.md)
```

## Directory Documentation Rule

**EVERY directory in the repository MUST have a README.md file** that documents:
- Purpose of the directory
- Contents overview
- Subdirectory descriptions
- Key files and their roles

## Mathematical Notation

When documenting mathematical concepts:
- Use LaTeX notation in code blocks
- Use Unicode symbols only in explanatory text
- Provide both notations when introducing operators

Example:
```
The conjunction operator `\\wedge` (displayed as ∧) combines two propositions.
```

## Code Example Standards

```python
# Include context comments
from model_checker.theory_lib import logos

# Show complete, runnable examples
theory = logos.get_theory(['modal'])
result = theory.check_validity(premises, conclusions)

# Include expected output where helpful
# Output: CountermodelFound(model=...)
```

## Non-README Documentation Standards

All documentation files that are NOT README.md files must follow these standards:

### Title and Navigation

```markdown
# [Document Title]

[← Back to [Source]](../README.md) | [Related Doc →](related.md)
```

### Table of Contents Requirement

All non-README documentation must have a table of contents with links:

```markdown
## Table of Contents

1. [Introduction](#introduction)
2. [Core Concepts](#core-concepts)
   - [Subsection 1](#subsection-1)
   - [Subsection 2](#subsection-2)
3. [Implementation Details](#implementation-details)
4. [Examples](#examples)
5. [References](#references)
```

### Content Organization

- Use section IDs from the table of contents for proper linking
- Follow content-specific section names rather than generic labels
- Include navigation links at both top and bottom

### Navigation Footer

```markdown
---

[← Back to [Source]](../README.md) | [Next Topic →](next.md)
```

---

[← Unicode Guidelines](UNICODE_GUIDELINES.md) | [Back to Maintenance](README.md) | [README Standards →](README_STANDARDS.md)