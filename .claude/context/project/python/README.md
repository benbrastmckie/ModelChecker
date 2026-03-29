# Python Context

This directory contains context files for Python development, specifically for the ModelChecker framework.

## Structure

- `domain/` - ModelChecker API references, theory library patterns
- `patterns/` - Testing patterns, code organization
- `standards/` - Code style, conventions

## Key Files

- `standards/code-style.md` - Python coding conventions
- `patterns/testing-patterns.md` - Pytest patterns and fixtures
- `domain/model-checker-api.md` - ModelChecker framework API and key classes
- `domain/theory-lib-patterns.md` - Theory library file structure and conventions

## Quick Reference

### Project Setup
```bash
python -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
```

### Testing
```bash
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v
pytest                    # Run all tests
pytest -v                 # Verbose output
pytest -k "test_name"     # Run specific tests
pytest --cov=src          # With coverage
```

### Code Quality
```bash
ruff check src/           # Lint
ruff format src/          # Format
mypy src/                 # Type check
```

## For Research

Load: `domain/model-checker-api.md`, `domain/theory-lib-patterns.md`, `standards/code-style.md`

## For Implementation

Load: `domain/model-checker-api.md`, `patterns/testing-patterns.md`, `standards/code-style.md`
