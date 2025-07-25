# Development Guide

## Environment Setup
- Python version: 3.x (check pyproject.toml for specifics)
- Key dependencies: z3-solver, jupyter, pytest
- Virtual environment: Use project's shell.nix on NixOS
- Platform support: Linux (primary), with NixOS-specific tooling

## Commands

### Testing Commands
- Run theory tests: `python test_theories.py` (for all theory_lib tests)
- Run specific theory tests: `python test_theories.py --theories logos bimodal`
- Run package tests: `python test_package.py` (for all non-theory component tests)
- Run specific component tests: `python test_package.py --components builder settings`
- List available components: `python test_package.py --list`
- Run Z3 isolation tests: `python test_package.py --components utils.tests`
- Run with verbose output: Add `-v` flag (e.g., `python test_theories.py -v`)
- Run with failfast: Add `-x` flag (e.g., `python test_package.py -x`)
- **Note**: All tests should be run through either `test_theories.py` (for theory-specific tests) or `test_package.py` (for all other tests). Do not create standalone test runners.

### Development Commands
- Package update with testing: `python run_update.py`
- Run main module: `./dev_cli.py`
- Create a new theory: `./dev_cli.py -l <theory_name>`
- Check an example file: `./dev_cli.py <example_file.py>`
- Development CLI: `./dev_cli.py <example_file.py>` (run from project root)
  - Always specify a target file: `./dev_cli.py [flags] <example_file.py>`
  - Use `-p` flag to show constraints: `./dev_cli.py -p <example_file.py>`
  - Use `-z` flag to show Z3 output: `./dev_cli.py -z <example_file.py>`
  - Combine flags: `./dev_cli.py -p -z <example_file.py>`
- Run jupyter notebooks: `./run_jupyter.sh`

For detailed documentation on advanced features like iterate settings, theory comparison, maximize mode, and debugging flags, see [TOOLS.md](../../Docs/TOOLS.md).

### NixOS-specific Testing
When working on NixOS, always use the provided scripts (`test_theories.py`, `test_package.py`, `dev_cli.py`) rather than direct Python commands to ensure proper PYTHONPATH configuration.

## Git Workflow
- Main branch: master
- Test before commit: Run both test suites
- Breaking changes: Acceptable per design philosophy
- Commit requirements: Ensure all tests pass before committing

## Common Workflows

### Adding a New Theory
1. Create a new directory in `theory_lib/`: `mkdir theory_lib/new_theory_name`
2. Implement required files: `semantic.py`, `operators.py`, `examples.py`
3. Add theory to registry in `theory_lib/__init__.py`: Add 'new_theory_name' to AVAILABLE_THEORIES
4. Create tests in `theory_lib/new_theory_name/test/`
5. Verify with `pytest theory_lib/new_theory_name/test/`

### Adding a New Operator
1. In the relevant theory's `operators.py`:
   - For primitive operators: Create a subclass of `Operator`
   - For derived operators: Create a subclass of `DefinedOperator`
2. Define semantic clauses for the operator
3. Register the operator in the theory's operator collection
4. Add test cases in `examples.py` or test files

### Working with Jupyter Integration
1. Start the Jupyter server: `./run_jupyter.sh`
2. Use high-level functions: `check_formula()`, `find_countermodel()`
3. For interactive exploration: `ModelExplorer().display()`
4. For theory-specific demos: Navigate to theory-specific notebook directories

### Debugging Issues
1. Check logs and error messages for tracebacks
2. Use the debugging tools in `jupyter/debug/`
3. Review the debug logging in `__main__.py` and `cli.py`
4. Follow the systematic debugging approach in `jupyter/debug/DEBUGGING.md`

## Common Error Patterns

### Z3 Solver Issues
- **Z3 timeout errors**: Complex models may hit solver timeouts (adjust the max_time setting)
- **Bitvector capacity**: Some logical structures may exceed bitvector capacity
- **Undecidable structures**: Some logical structures may be undecidable

### Path and Import Issues
- **Import path issues**: Use provided scripts, not direct python commands
- **NixOS Path Issues**: On NixOS, PYTHONPATH management is critical. Use the provided scripts (`run_jupyter.sh`, `dev_cli.py`) instead of direct commands
- **Module loading**: Always run commands from project root

### Theory-Specific Issues
- **World reference errors**: In bimodal logic, always use consistent world references. World IDs should be explicitly provided where needed rather than attempting conversions
- **Theory Compatibility**: Different theories may have incompatible operators or semantics. Use the theory adapter system for conversion

### Jupyter Issues
- **Widget Display**: If widgets don't display properly, ensure ipywidgets is properly installed and nbextensions are enabled
- **Kernel issues**: Restart kernel if experiencing import problems

## Known Challenges

1. **Theory Compatibility**: Different theories may have incompatible operators or semantics. Use the theory adapter system for conversion.

2. **NixOS Path Issues**: On NixOS, PYTHONPATH management is critical. Use the provided scripts (`run_jupyter.sh`, `dev_cli.py`) instead of direct commands.

3. **Z3 Solver Limitations**: 
   - Complex models may hit solver timeouts (adjust the max_time setting)
   - Some logical structures may be undecidable or exceed bitvector capacity

4. **Jupyter Widget Display**: If widgets don't display properly, ensure ipywidgets is properly installed and nbextensions are enabled.

## Documentation

### For New Contributors
- **[Installation Guide](INSTALLATION.md)** - Environment setup and dependencies
- **[Style Guide](STYLE_GUIDE.md)** - Coding standards and conventions
- **[Architecture Overview](ARCHITECTURE.md)** - System design and component relationships

### For Theory Developers  
- **[Theory Library Guide](../src/model_checker/theory_lib/README.md)** - Theory implementation patterns
- **[API Reference](../src/model_checker/README.md)** - Core framework APIs
- **[Example Theories](../src/model_checker/theory_lib/)** - Reference implementations

### For Core Developers
- **[Testing Guide](TESTS.md)** - Comprehensive testing methodology
- **[Cleanup Recommendations](CLEANUP_RECOMMENDATIONS.md)** - Technical debt and improvements
- **[Advanced Tools](../../Docs/TOOLS.md)** - Framework debugging and analysis tools

## API Reference Examples

### Core Framework Usage
```python
from model_checker import BuildExample, get_theory

# 1. Load a semantic theory
theory = get_theory("logos")

# 2. Create example with premises and conclusions
model = BuildExample("modus_ponens", theory)
model.add_premises(["p", "p \\rightarrow q"])
model.add_conclusions(["q"])

# 3. Check validity and analyze results
valid = model.check_validity()
if not valid:
    model.print_countermodel()
    print(f"Countermodel found with {model.model_size} states")
```

### Advanced Theory Usage
```python
# Custom settings and iteration
settings = {
    'N': 4,                    # Larger state space
    'contingent': True,        # Contingent propositions
    'iterate': 3,              # Find multiple models
    'max_time': 5000          # Extended timeout
}

model = BuildExample("complex_modal", theory, settings=settings)
result = model.check_formula("\\Box (p \\rightarrow q) \\rightarrow (\\Box p \\rightarrow \\Box q)")

# Access iteration results
if hasattr(model, '_iterator'):
    models = model.get_all_models()
    for i, m in enumerate(models, 1):
        print(f"Model {i}: {m.get_differences()}")
```

### Jupyter Integration Patterns
```python
# High-level interactive functions
from model_checker.jupyter import check_formula, ModelExplorer, find_countermodel

# Quick validation
result = check_formula("(p \\wedge q) \\rightarrow p")

# Countermodel discovery
counter = find_countermodel("p \\rightarrow \\Box p")
if counter:
    print(f"Countermodel: {counter}")

# Interactive exploration
explorer = ModelExplorer(theory_name="exclusion")
explorer.display()  # Launches widget interface
```

## References

### Implementation Documentation
- Development workflow follows modular design principles described in [ARCHITECTURE.md](ARCHITECTURE.md)
- Testing methodology detailed in [TESTS.md](TESTS.md) with dual-system approach

### Related Resources
- **[Main Documentation Hub](README.md)** - Development documentation overview
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Semantic theory implementations
- **[Jupyter Integration](../src/model_checker/jupyter/README.md)** - Interactive development tools

## License

All development documentation is licensed under GPL-3.0 as part of the ModelChecker framework.

---

[← Back to Development Hub](README.md) | [Architecture →](ARCHITECTURE.md) | [Testing Guide →](TESTS.md)