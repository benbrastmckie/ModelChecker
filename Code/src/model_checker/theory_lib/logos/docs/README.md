# Logos Theory Documentation

## Directory Structure
```
docs/
├── README.md          # This file - documentation hub
├── API_REFERENCE.md   # Complete API documentation
├── ARCHITECTURE.md    # System design and implementation
├── USER_GUIDE.md      # Practical usage guide
├── ITERATE.md         # Model iteration features
└── SETTINGS.md        # Configuration reference
```

Welcome to the comprehensive documentation for the Logos semantic theory. This guide will help you understand, use, and extend the most advanced hyperintensional semantic framework in ModelChecker.

## Documentation Overview

The Logos theory implements a unified formal language of thought with 20 logical operators across 5 modular subtheories. This documentation is organized to serve different audiences and use cases.

## Quick Navigation

### Getting Started
- **[User Guide](USER_GUIDE.md)** - Practical guide for using the Logos theory
- **[Settings Documentation](SETTINGS.md)** - Complete reference for all configuration options
- **[Main Theory README](../README.md)** - Overview and quick start

### Technical Deep Dives
- **[Architecture Guide](ARCHITECTURE.md)** - System design and implementation details
- **[Model Iteration](ITERATE.md)** - Finding multiple models and exploring solution spaces
- **[Operator Registry](../operators.py)** - Dynamic operator loading system

### Interactive Learning
- **[Jupyter Notebooks](../notebooks/README.md)** - Interactive tutorials and demonstrations
- **[Main Demo Notebook](../notebooks/logos_demo.ipynb)** - Comprehensive introduction
- **[Subtheory Notebooks](../notebooks/subtheories/)** - Focused explorations

### Reference Documentation
- **[Subtheory Documentation](../subtheories/README.md)** - Individual operator categories
- **[Test Documentation](../tests/README.md)** - Testing methodology and examples
- **[API Reference](#api-reference)** - Complete API documentation

## Documentation by Audience

### For New Users
1. Start with the **[User Guide](USER_GUIDE.md)** for practical examples
2. Explore the **[Jupyter Notebooks](../notebooks/README.md)** for interactive learning
3. Review **[Settings Documentation](SETTINGS.md)** to understand configuration options

### For Researchers
1. Read the **[Architecture Guide](ARCHITECTURE.md)** for theoretical foundations
2. Study the **[Main Theory README](../README.md)** for academic references
3. Examine **[Test Examples](../tests/)** for logical principle validation

### For Developers
1. Understand the **[Architecture Guide](ARCHITECTURE.md)** for system design
2. Review **[Model Iteration](ITERATE.md)** for advanced features
3. Check **[Contributing Guidelines](../README.md#contributing)** for development workflow

### For Educators
1. Use **[Jupyter Notebooks](../notebooks/README.md)** for teaching materials
2. Reference the **[User Guide](USER_GUIDE.md)** for clear explanations
3. Explore **[Subtheory Documentation](../subtheories/)** for focused topics

## Key Concepts

### Hyperintensional Semantics
The Logos theory implements truthmaker semantics where:
- Propositions have both **verifiers** and **falsifiers**
- Content is distinguished even for necessarily equivalent formulas
- States are represented as bit vectors for efficient computation

### Modular Architecture
Five independent but interoperable subtheories:
1. **Extensional** - Extensional operators (¬, ∧, ∨, →, ↔, ⊤, ⊥)
2. **Modal** - Necessity and possibility (□, ◇, CFBox, CFDiamond)
3. **Constitutive** - Content relationships (≡, ≤, ⊑, ≼, ⇒)
4. **Counterfactual** - counterfactual reasoning (□→, ◇→)
5. **Relevance** - Relevance logic (≼ and derived operators)

### Unified Framework
- **Dynamic Loading** - Load only the operators you need
- **Dependency Resolution** - Automatic handling of inter-subtheory dependencies
- **Consistent Semantics** - All operators share the same semantic foundation

## Common Tasks

### Basic Formula Checking
```python
from model_checker.theory_lib import logos
from model_checker import BuildExample

theory = logos.get_theory()
model = BuildExample("my_example", theory)
result = model.check_formula("\\Box p \\rightarrow p")
```

### Loading Specific Subtheories
```python
# Load only modal and extensional operators
theory = logos.get_theory(['extensional', 'modal'])
```

### Finding Countermodels
```python
model = BuildExample("test", theory,
    premises=["\\Box (p \\rightarrow q)"],
    conclusions=["\\Box p \\rightarrow \\Box q"],
    settings={'N': 4, 'iterate': 3}
)
```

### Interactive Exploration
```python
from model_checker.jupyter import ModelExplorer
explorer = ModelExplorer(theory='logos')
explorer.display()
```

## API Reference

### Core Functions
- `logos.get_theory(subtheories=None)` - Load theory with specified subtheories
- `logos.get_operator_class(op_name)` - Get specific operator implementation
- `logos.list_operators(subtheory=None)` - List available operators

### Key Classes
- `LogosSemantics` - Core semantic framework
- `LogosOperatorRegistry` - Dynamic operator management
- `LogosProposition` - Bilateral proposition representation
- `LogosModelStructure` - Model construction and evaluation

### Settings
See **[SETTINGS.md](SETTINGS.md)** for complete configuration reference.

## Troubleshooting

### Common Issues
1. **Import Errors** - Ensure ModelChecker is properly installed
2. **Operator Not Found** - Check subtheory is loaded
3. **Z3 Timeouts** - Increase `max_time` setting or reduce `N`
4. **Memory Issues** - Use smaller models or load fewer subtheories

### Getting Help
- Check existing documentation first
- Review test examples for similar use cases
- Consult the [main ModelChecker documentation](../../../../README.md)
- Open an issue on GitHub for bugs or feature requests

## Related Resources

### Academic Papers
- Brast-McKie (2021) "Identity and Aboutness"
- Brast-McKie (2025) "Counterfactual Worlds"
- Fine (2017) "A Theory of Truthmaker Content I & II"

### Other Theories
- **[Exclusion Theory](../../exclusion/)** - Unilateral semantics
- **[Bimodal Theory](../../bimodal/)** - Temporal modal logic
- **[Imposition Theory](../../imposition/)** - Fine's counterfactual semantics

### Framework Documentation
- **[ModelChecker Main Docs](../../../../README.md)**
- **[Settings System](../../../settings/README.md)**
- **[Development Guide](../../../../docs/DEVELOPMENT.md)**

## Contributing

We welcome contributions! See the [Contributing section](../README.md#contributing) in the main README for guidelines on:
- Adding new operators
- Creating subtheories
- Improving documentation
- Reporting issues

---

[← Back to Logos Theory](../README.md) | [API Reference →](API_REFERENCE.md) | [User Guide →](USER_GUIDE.md)
