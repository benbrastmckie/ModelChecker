# Theory License Inheritance Guidelines

**Navigation**: [← Back to Contracts](../README.md) | [Maintenance Home](../../README.md) | [Iterator Contracts →](ITERATOR_CONTRACTS.md)

**Related Documentation**: 
- [Implementation Guidelines](../implementation/README.md) - Development process
- [Core Architecture](../core/README.md) - Framework licensing structure
- [Quality Assurance](../quality/README.md) - Contribution standards

## Overview

The ModelChecker framework implements a dual licensing structure that distinguishes between the static framework license and the inheritance-based licensing for theory implementations. This guide explains how license inheritance works when creating new theories based on existing ones.

## License Structure

### Framework License (Static)

The ModelChecker framework itself is licensed under GPL-3.0 with a static license that does not change:

```
ModelChecker Framework
Copyright (c) 2024 Benjamin Brast-McKie
Licensed under GPL-3.0
```

This license applies to:
- Core framework code (`model_checker/` excluding `theory_lib/`)
- Builder infrastructure
- CLI tools
- Testing framework

### Theory Licenses (Inheritable)

Individual theory implementations in `theory_lib/` have their own licenses that must be inherited when creating derivative works:

```
Original Theory Implementation
Copyright (c) [Year] [Original Author]
Licensed under GPL-3.0

Derivative works must:
1. Maintain the same license (GPL-3.0)
2. Preserve original author attribution
3. Document novel contributions
```

## Creating Derivative Theories

When you generate a new project based on an existing theory using:

```bash
model-checker -l logos my_new_theory
```

The generated `LICENSE.md` file will automatically include:

1. **Original Theory Copyright** - Attribution to the source theory author
2. **Derivative Work Copyright** - Space for your copyright on novel contributions
3. **Novel Contributions Section** - Where you document your changes
4. **Attribution Requirements** - Clear guidelines for maintaining proper credit

### Example Generated License

```markdown
# License

This theory implementation is a derivative work based on the logos theory.

## Original Theory Copyright

Copyright (c) 2024 Benjamin Brast-McKie

The original logos theory implementation is licensed under GPL-3.0.
This derivative work must maintain the same license terms.

## Derivative Work Copyright

Copyright (c) 2025 [Your Name]

### Novel Contributions

[Describe your novel contributions here. Examples:
- Extended the theory to handle additional operators
- Implemented new semantic constraints for X
- Added support for Y feature
- Optimized performance for Z cases]

For detailed documentation of changes, see: [Link to your contribution docs]

## License Terms

[GPL-3.0 terms...]

## Attribution Requirements

When using or distributing this theory:
1. Maintain attribution to the original logos theory by Benjamin Brast-McKie
2. Include this complete license file
3. Document any modifications in the "Novel Contributions" section
4. Provide links to detailed change documentation
```

## When to Add Your Name

You should add your name to the derivative work copyright when you have made **substantial novel contributions** such as:

### Substantial Contributions
- Adding new operators or semantic features
- Implementing new constraint types
- Extending the theory to handle new logical phenomena
- Creating new subtheories
- Significant algorithmic improvements

### Minor Contributions
For minor changes (bug fixes, documentation improvements, small optimizations), contribute back to the original theory rather than creating a derivative work.

## Best Practices

### 1. Document Everything
Maintain clear documentation of your contributions:
```markdown
### Novel Contributions

1. **Temporal Extension** (v1.0.0)
   - Added temporal operators (□t, ◇t) 
   - Implemented interval-based semantics
   - See: docs/TEMPORAL_EXTENSION.md

2. **Performance Optimization** (v1.1.0)
   - Reduced constraint generation time by 40%
   - Implemented caching for common patterns
   - See: docs/PERFORMANCE_IMPROVEMENTS.md
```

### 2. Link to Detailed Documentation
Always provide links to comprehensive documentation:
```markdown
For detailed documentation of changes, see:
- [CHANGELOG.md](CHANGELOG.md) - Version history
- [docs/CONTRIBUTIONS.md](docs/CONTRIBUTIONS.md) - Technical details
- [docs/API_CHANGES.md](docs/API_CHANGES.md) - API modifications
```

### 3. Maintain Clear Separation
Keep original code and your contributions clearly separated:
```python
# Original logos operators
from .operators import BoxOperator, DiamondOperator

# My novel temporal operators
from .temporal_operators import TemporalBoxOperator, TemporalDiamondOperator
```

### 4. Version Your Contributions
Use semantic versioning to track your changes:
```python
__version__ = "1.2.0"  # Your theory version
__base_theory_version__ = "0.1.0"  # Original theory version
__model_checker_version__ = "0.1.0"  # Framework compatibility
```

## Academic Attribution

### Citation Requirements

For academic work, cite both:

1. **The Original Theory**
   ```bibtex
   @software{original_theory,
     author = {Original Author},
     title = {Theory Name: Implementation for ModelChecker},
     year = {2024},
     url = {https://github.com/...}
   }
   ```

2. **Your Derivative Work** (if substantial contributions)
   ```bibtex
   @software{derivative_theory,
     author = {Your Name},
     title = {Extended Theory Name: Novel Contributions},
     year = {2025},
     note = {Based on Original Theory by Original Author}
   }
   ```

### In Papers

When describing your work:
```
We extend the logos theory implementation [1] by adding temporal
operators and interval-based semantics. Our contributions include...

[1] Brast-McKie, B. (2024). Logos: Hyperintensional semantics for ModelChecker.
[2] Your Name. (2025). Temporal Logos: Extending hyperintensional semantics.
```

## Common Scenarios

### Scenario 1: Creating a Specialized Version

If you're creating a specialized version of a theory for a specific domain:

```markdown
### Novel Contributions

Created a specialized version of logos theory for epistemic logic:
- Restricted to S5 modal frames
- Added knowledge and belief operators
- Optimized for multi-agent reasoning
- Removed unnecessary counterfactual machinery

Domain: Epistemic Logic Applications
Documentation: docs/EPISTEMIC_SPECIALIZATION.md
```

### Scenario 2: Merging Multiple Theories

If combining features from multiple theories:

```markdown
## Original Theory Copyright

Based on multiple theories:
1. logos theory - Copyright (c) 2024 Benjamin Brast-McKie
2. exclusion theory - Copyright (c) 2024 Benjamin Brast-McKie

### Novel Contributions

Unified framework combining:
- Hyperintensional semantics from logos
- Exclusion relations from exclusion theory
- Novel interaction constraints between the two
- Unified operator hierarchy

See: docs/UNIFIED_FRAMEWORK.md
```

### Scenario 3: Theory Extension

If extending a theory with new capabilities:

```markdown
### Novel Contributions

Extended imposition theory with:
1. Probabilistic imposition relations
2. Graded imposition strength (0.0-1.0)
3. Statistical model checking capabilities
4. Monte Carlo countermodel search

These extensions enable reasoning about uncertain impositions.
See: docs/PROBABILISTIC_EXTENSION.md
```

## Licensing Compliance

### GPL-3.0 Requirements

The inheritance model requires maintaining GPL-3.0 compatibility:
- ✅ Can add additional permissions
- ❌ Cannot add restrictions
- ❌ Cannot change to incompatible license
- ✅ Can dual-license your contributions (with GPL-3.0 as one option)

### Distribution Requirements

When distributing derivative theories:

1. **Include complete source code**
2. **Maintain all copyright notices**
3. **Provide LICENSE.md with inheritance documentation**
4. **Document all modifications clearly**
5. **Ensure GPL-3.0 compliance**

## Validation and Enforcement

### License Validation Tools

Use provided tools to validate licensing compliance:

```bash
# Check license consistency across theory
python test_package.py --metadata-report

# Validate copyright notices
python test_package.py --validate-licenses

# Generate missing license files
python test_package.py --create-licenses --author "Your Name"
```

### Compliance Checklist

Before distributing derivative theory:

- [ ] Original theory copyright preserved
- [ ] Your contributions clearly documented
- [ ] LICENSE.md file complete and accurate
- [ ] All source files have appropriate copyright notices
- [ ] GPL-3.0 license terms included
- [ ] Attribution requirements clearly stated
- [ ] Links to detailed documentation provided

## Troubleshooting

### Missing Attribution

If you accidentally published without proper attribution:
1. Update LICENSE.md immediately
2. Add attribution to README.md
3. Create ATTRIBUTION.md with full details
4. Notify users of the correction

### Unclear Contributions

If unsure whether your changes warrant adding your name:
1. List all modifications
2. Evaluate against "Substantial Contributions" criteria
3. When in doubt, maintain original attribution only
4. Consider contributing back to the original theory

### License Conflicts

The inheritance model requires maintaining GPL-3.0 compatibility:
- ✅ Can add additional permissions
- ❌ Cannot add restrictions
- ❌ Cannot change to incompatible license
- ✅ Can dual-license your contributions (with GPL-3.0 as one option)

## Framework Integration

### Theory Registration

When registering derivative theories with the framework:

```python
# In theory __init__.py
THEORY_METADATA = {
    'name': 'temporal_logos',
    'base_theory': 'logos',
    'version': '1.0.0',
    'base_version': '0.1.0',
    'author': 'Your Name',
    'original_author': 'Benjamin Brast-McKie',
    'license': 'GPL-3.0',
    'description': 'Temporal extension of logos theory'
}
```

### Automated License Generation

The framework provides automated license generation for derivative works:

```bash
# Generate license for new derivative theory
model-checker --generate-license \
  --base-theory logos \
  --author "Your Name" \
  --theory-name temporal_logos
```

## References

- [GPL-3.0 License Text](https://www.gnu.org/licenses/gpl-3.0.txt)
- [Implementation Guidelines](../implementation/README.md) - Development standards
- [Core Architecture](../core/README.md) - Framework licensing structure
- [Software Licensing Best Practices](https://opensource.guide/legal/)

---

**Navigation**: [← Back to Contracts](../README.md) | [Maintenance Home](../../README.md) | [Iterator Contracts →](ITERATOR_CONTRACTS.md)