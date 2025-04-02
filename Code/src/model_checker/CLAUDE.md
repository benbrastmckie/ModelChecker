# ModelChecker Guide for Agents

## Commands
- Run all tests: `pytest theory_lib/<theory_name>/test/`
- Run specific test: `pytest theory_lib/<theory_name>/test/test_<theory_name>.py -k "<test_name>"`
- Run with verbose output: `pytest -v theory_lib/<theory_name>/test/`
- Run main module: `python -m model_checker`

## Code Style
- **Imports**: Standard libraries first, then local imports
- **Spacing**: 4-space indentation
- **Naming**: 
  - Functions: `snake_case`
  - Classes: `PascalCase`
  - Modules: `lowercase`
- **Error handling**: Use descriptive exception messages
- **Documentation**: Triple-quoted docstrings for modules and functions
- **Architecture**: 
  - Maintain separation between semantic and syntactic components
  - Each theory in `theory_lib/` follows same structure (operators.py, semantic.py, examples.py)
  - New theories should match existing module patterns

## Project Structure
The codebase implements a model-checker for various logical operators with a modular architecture allowing for different types of semantic theories with different operators.
