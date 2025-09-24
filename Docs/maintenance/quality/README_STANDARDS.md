# README.md Standards

[← Documentation Standards](DOCUMENTATION_STANDARDS.md) | [Back to Maintenance](../README.md) | [Code Organization →](../CODE_ORGANIZATION.md)

## Overview

This document defines the standards for README.md files in the ModelChecker repository. The goal is to ensure **comprehensive, relevant documentation** that serves users effectively without unnecessary rigidity. Each README should cover all essential topics for its component while avoiding extraneous content.

## Special Exception: Code/README.md

The `/Code/README.md` file is **exempt** from these standards because it serves as the package description on PyPI. This file:

- Does not require navigation links
- Does not require a file tree
- Should be formatted for PyPI display
- Must focus on user-facing documentation

All other README.md files should follow the principles below.

## Core Documentation Principles

### 1. Comprehensive Coverage

Every README must thoroughly document its component, including:

- **Purpose and Functionality**: Clear explanation of what the component does
- **Integration Context**: How it fits within the larger framework
- **Usage Patterns**: Practical examples and common workflows
- **Technical Details**: Architecture, design decisions, and implementation notes

### 2. Relevant Content Only

Include only information directly relevant to understanding and using the component:

- Avoid generic boilerplate
- Don't repeat information available elsewhere (link instead)
- Focus on what makes this component unique
- Omit standard Python patterns unless they're unusual

### 3. Consistent Navigation

All READMEs should include:

- **Header Navigation**: Links to parent and key related documents
- **Footer Navigation**: Repeated navigation for long documents
- **Cross-References**: Links to related components and documentation

## Essential Elements

### Title and Navigation

```markdown
# [Component Name]: [Descriptive Tagline]

[← Back to Parent](../README.md) | [Key Doc →](relevant_doc.md) | [Related →](related.md)
```

### Directory Structure (When Applicable)

For directories with multiple files, show the structure:

```markdown
## Directory Structure
```

component/
├── README.md # This file - overview and guide
├── core_file.py # Main implementation
├── support_file.py # Supporting functionality
└── tests/ # Test suite

```

```

### Overview Section

Provide context and orientation:

- Primary purpose and goals
- Key capabilities and features
- Relationship to other components
- Theoretical or academic background (if relevant)

### Usage Examples

Show practical usage with working code:

````markdown
## Usage

### Basic Example

```python
from model_checker.component import Feature
result = Feature().process(input_data)
```
````

### Advanced Usage

[More complex examples as needed]

```

### Technical Documentation
Include sections as appropriate:
- **Architecture**: Design patterns and structure
- **API Reference**: Key classes and functions
- **Configuration**: Settings and customization options
- **Extension Points**: How to extend or modify behavior

### References and Resources
- Academic citations (for theory implementations)
- Related documentation
- External resources

## Theory-Specific Documentation

### Main Theory README
Each theory should document:
- **Theoretical Foundation**: Academic background and key concepts
- **Semantic Approach**: How the theory implements its semantics
- **Operator Inventory**: Available logical operators
- **Settings and Configuration**: Theory-specific settings
- **Example Library**: Representative examples
- **Comparison with Other Theories**: Distinguishing features

### Subtheory Documentation
For modular theories with subtheories:
- **Uniform Structure**: All subtheories documented consistently
- **Operator Reference**: Complete operator documentation including:
  - Symbol (LaTeX and Unicode representations)
  - Arity and type
  - Truth conditions (informal and formal)
  - Usage examples
- **Integration**: How the subtheory relates to the main theory
- **Specific Features**: What makes this subtheory unique

## Component-Specific Guidelines

### Framework Components (builder, iterate, settings, etc.)
Focus on:
- **Integration Role**: How the component fits in the framework
- **API Design**: Key interfaces and usage patterns
- **Extension Patterns**: How to extend or customize
- **Performance Considerations**: Optimization and efficiency notes

### Test Directories
Document:
- **Test Organization**: Structure and naming conventions
- **Coverage Strategy**: What aspects are tested
- **Running Tests**: Commands and options
- **Adding Tests**: Guidelines for new test cases

### Documentation Directories
Provide:
- **Navigation Hub**: Clear paths to all documentation
- **Audience Guidance**: Which docs serve which users
- **Maintenance Notes**: How to keep docs updated

## Quality Standards

### Accuracy Requirements
- Code examples must be tested and working
- File paths and links must be valid
- Counts and statistics must match actual implementation
- Version-specific information must be current

### Clarity Standards
- Use clear, concise language
- Define technical terms on first use
- Provide context before diving into details
- Use consistent terminology throughout

### Maintenance Practices
- Update README when implementation changes
- Verify links during major updates
- Review for relevance periodically
- Remove outdated information promptly

## Verification Checklist

When creating or updating a README:

- [ ] **Purpose Clear**: Reader immediately understands what this component does
- [ ] **Navigation Present**: Header and footer navigation included
- [ ] **Examples Working**: All code examples tested and functional
- [ ] **Links Valid**: All cross-references and external links verified
- [ ] **Content Relevant**: No unnecessary boilerplate or repetition
- [ ] **Structure Logical**: Information flows naturally
- [ ] **Technically Accurate**: Implementation details correct
- [ ] **Audience Appropriate**: Language and detail level fits intended readers

## Best Practices

### Writing Style
- **Active Voice**: "The builder creates models" not "Models are created by the builder"
- **Concrete Examples**: Show actual usage, not abstract descriptions
- **Progressive Disclosure**: Start simple, add complexity gradually
- **Visual Aids**: Use diagrams and formatted output where helpful

### Organization
- **Logical Flow**: Most important information first
- **Clear Sections**: Use headings to organize content
- **Consistent Formatting**: Follow markdown conventions
- **Scannable Layout**: Use lists, tables, and code blocks effectively

### Maintenance
- **Living Documents**: Update as implementation evolves
- **Version Notes**: Document significant changes
- **Deprecation Notices**: Clear warnings for outdated features
- **Migration Guides**: Help users adapt to changes

---

[← Documentation Standards](DOCUMENTATION_STANDARDS.md) | [Back to Maintenance](../README.md) | [Code Organization →](../CODE_ORGANIZATION.md)
```
