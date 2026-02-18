# Theory Refactoring Prompt for Parallel Subagents

## Objective
Launch three parallel general-purpose subagents to refactor the theory modules in `Code/src/model_checker/theory_lib/` (excluding `bimodal/`) based on their analysis reports, while preserving their unique characteristics and ensuring all tests continue to pass.

## Critical Requirements for All Theories

### Testing Compliance (Per Code/docs/core/TESTING.md)
- **MANDATORY**: All existing tests must pass after refactoring
- **MANDATORY**: Run `python Code/dev_cli.py Code/src/model_checker/theory_lib/{theory}/examples.py` to verify examples work
- **MANDATORY**: Follow TDD approach - write failing tests for new functionality first
- **Test Organization**: Maintain proper separation of unit/integration/e2e tests
- **Test Isolation**: Ensure tests run independently without environment contamination

### Base Class Usage
- Import shared functionality from existing model_checker packages, NOT create new `theory_lib/common/`
- Reuse existing base classes from `model_checker.builder`, `model_checker.utils`, etc.
- Avoid duplicating functionality that already exists in the framework

### Standards Compliance
- Follow Code/docs/core/CODE_STANDARDS.md for code quality
- Follow Code/docs/core/ARCHITECTURE.md for structural patterns
- Follow Code/docs/contracts/ITERATOR_CONTRACTS.md for iterator implementation
- Maintain backward compatibility for all public APIs

## Theory-Specific Refactoring Prompts

### PROMPT 1: Exclusion Theory Refactoring

```
You are refactoring the EXCLUSION theory module located at Code/src/model_checker/theory_lib/exclusion/.

IMPORTANT CONTEXT:
- This theory uses WITNESS-BASED SEMANTICS which is fundamentally different from the other theories
- The witness predicate approach makes witness functions first-class model citizens
- This unique architecture MUST be preserved as it's the theory's core innovation
- Authors: Ben Brastmckie and others (see LICENSING.md)

CRITICAL REQUIREMENTS:
1. ALL tests must continue to pass after refactoring
2. Run tests with: pytest Code/src/model_checker/theory_lib/exclusion/tests/
3. Verify examples work: python Code/dev_cli.py Code/src/model_checker/theory_lib/exclusion/examples.py
4. Preserve the witness-based implementation paradigm

PHASE 1: CRITICAL FIXES (Priority 1)
Based on the analysis report, address these URGENT issues:

1. Fix Import Chaos in semantic.py:
   - Remove ALL duplicate import statements (5+ duplicate "import sys")
   - Organize imports properly: stdlib → third-party → local
   - Remove redundant utility imports
   - File: semantic.py:1-50 (multiple duplicate imports)

2. Break Up Monolithic semantic.py (1,566 lines):
   Create this modular structure while PRESERVING witness semantics:
   ```
   exclusion/
   ├── semantic/
   │   ├── __init__.py          # Re-export main classes
   │   ├── core.py              # WitnessSemantics class only
   │   ├── model.py             # WitnessAwareModel class
   │   ├── structure.py         # WitnessStructure class
   │   ├── registry.py          # WitnessRegistry class
   │   ├── constraints.py       # WitnessConstraintGenerator class
   │   └── protocols.py         # Type protocols for witness functions
   ├── operators.py             # Keep as is
   ├── iterate.py               # Keep as is
   ├── examples.py              # Keep as is
   └── __init__.py              # Maintain backward compatibility
   ```

   CRITICAL: The OLD semantic.py must be replaced with proper imports from the new modules to maintain backward compatibility.

3. Add Type Hints:
   - Focus on public API methods first
   - Use Protocol classes for witness function interfaces
   - Add TypeVar for generic witness types
   - Ensure mypy passes with no errors

PHASE 2: ARCHITECTURE IMPROVEMENTS (Priority 2)

1. Extract Common Patterns:
   - Identify repeated witness validation logic
   - Create helper functions in semantic/utils.py
   - DO NOT create theory_lib/common/ - use existing framework utilities

2. Improve Error Handling:
   - Add specific exception classes for witness-related errors
   - Provide helpful error messages for common issues
   - Example: "WitnessNotFoundError: No witness function defined for operator '∧'"

3. Documentation Enhancement:
   - Add comprehensive docstrings explaining witness semantics
   - Include examples in docstrings
   - Document the theoretical foundation

PHASE 3: TESTING & VALIDATION

1. Run Existing Tests:
   ```bash
   pytest Code/src/model_checker/theory_lib/exclusion/tests/ -v
   ```

2. Verify Examples:
   ```bash
   python Code/dev_cli.py Code/src/model_checker/theory_lib/exclusion/examples.py
   ```

3. Check Type Hints:
   ```bash
   mypy Code/src/model_checker/theory_lib/exclusion/
   ```

EXPECTED DELIVERABLES:
- Modularized semantic implementation preserving witness paradigm
- Clean import structure with no duplicates
- Type hints for all public APIs
- All tests passing
- Examples running successfully via dev_cli.py

WHAT NOT TO CHANGE:
- The witness-based semantic approach
- Public API signatures
- Example definitions
- Test logic (tests should pass without modification)

Report all changes made and any issues encountered.
```

### PROMPT 2: Imposition Theory Refactoring

```
You are refactoring the IMPOSITION theory module located at Code/src/model_checker/theory_lib/imposition/.

IMPORTANT CONTEXT:
- This theory is based on Kit Fine's truthmaker semantics
- It inherits heavily from logos theory (imports logos base classes)
- The similarity to logos is INTENTIONAL and should be maintained
- Focus on file size issues and test coverage

CRITICAL REQUIREMENTS:
1. ALL tests must continue to pass after refactoring
2. Run tests with: pytest Code/src/model_checker/theory_lib/imposition/tests/
3. Verify examples work: python Code/dev_cli.py Code/src/model_checker/theory_lib/imposition/examples.py
4. Maintain inheritance from logos base classes

PHASE 1: FILE SIZE MANAGEMENT (Priority 1)

1. Split Oversized semantic.py (662 lines):
   Create focused modules while maintaining logos inheritance:
   ```
   imposition/
   ├── semantic/
   │   ├── __init__.py          # Re-export main classes
   │   ├── core.py              # ImpositionSemantics (inherits from logos)
   │   ├── model.py             # ImpositionModel classes
   │   └── helpers.py           # Utility functions
   ├── operators.py             # Keep as is
   ├── iterate.py               # Keep as is
   ├── examples.py              # Need to split (see below)
   └── __init__.py              # Maintain backward compatibility
   ```

2. Restructure examples.py (1,062 lines - CRITICAL):
   Split into logical groups:
   ```
   imposition/
   ├── examples/
   │   ├── __init__.py          # Import all example groups
   │   ├── basic.py             # Basic imposition examples
   │   ├── complex.py           # Complex formula examples
   │   ├── edge_cases.py        # Edge cases and special scenarios
   │   └── test_suite.py        # Test case definitions
   └── examples.py              # Thin wrapper importing from examples/
   ```

PHASE 2: QUALITY IMPROVEMENTS (Priority 2)

1. Enhance Type Hints:
   - Add comprehensive type hints (currently ~55% coverage)
   - Use same type protocols as logos where applicable
   - Ensure compatibility with logos type system

2. Improve Test Coverage:
   - Current unit tests are minimal (50 lines)
   - Add unit tests for each semantic method
   - Add integration tests for imposition-specific features
   - Target 80% coverage minimum

3. Code Deduplication:
   - Identify patterns repeated from logos
   - Use logos base functionality instead of reimplementing
   - Extract imposition-specific logic into focused methods

PHASE 3: TESTING & VALIDATION

1. Run Existing Tests:
   ```bash
   pytest Code/src/model_checker/theory_lib/imposition/tests/ -v
   ```

2. Verify Examples:
   ```bash
   python Code/dev_cli.py Code/src/model_checker/theory_lib/imposition/examples.py
   ```

3. Check Coverage:
   ```bash
   pytest Code/src/model_checker/theory_lib/imposition/tests/ --cov=imposition --cov-report=term-missing
   ```

EXPECTED DELIVERABLES:
- Properly sized files (<500 lines each)
- Organized example structure
- Enhanced test coverage (>80%)
- Type hints for all public methods
- All tests passing
- Examples running successfully via dev_cli.py

WHAT NOT TO CHANGE:
- Inheritance from logos base classes
- Core imposition semantics logic
- Public API compatibility
- Integration with Fine's truthmaker framework

Report all changes made and test coverage improvements.
```

### PROMPT 3: Logos Theory Refactoring

```
You are refactoring the LOGOS theory module located at Code/src/model_checker/theory_lib/logos/.

IMPORTANT CONTEXT:
- This is the most sophisticated theory with SUBTHEORY ARCHITECTURE
- Has 5 subtheories: extensional, modal, constitutive, counterfactual, relevance
- The subtheory system is a KEY FEATURE that must be preserved
- Best organized of the three theories but needs standardization

CRITICAL REQUIREMENTS:
1. ALL tests must continue to pass after refactoring
2. Run tests with: pytest Code/src/model_checker/theory_lib/logos/tests/
3. Verify examples work: python Code/dev_cli.py Code/src/model_checker/theory_lib/logos/examples.py
4. PRESERVE the subtheory plugin architecture

PHASE 1: STANDARDS COMPLIANCE (Priority 1)

1. Complete Type Hint Coverage:
   - Current coverage: ~60% - target 95%
   - Add Protocol classes for subtheory interfaces
   - Use TypeVar for generic subtheory types
   - Files needing attention:
     * semantic.py - Add complete type hints
     * All subtheories/*/semantic.py files
     * iterate.py - Add iterator type hints

2. Iterator Contract Compliance:
   Based on Code/docs/contracts/ITERATOR_CONTRACTS.md:
   - Add missing iterator methods if any
   - Ensure proper state management
   - Add type hints for iterator protocol
   - File: iterate.py

3. Subtheory Test Integration:
   - Subtheory tests are currently isolated
   - Create test orchestration in main tests/
   - Ensure all subtheory tests run in CI
   - Add integration tests across subtheories

PHASE 2: ARCHITECTURAL ENHANCEMENTS (Priority 2)

1. Standardize Subtheory Interface:
   Create explicit protocol for subtheories:
   ```python
   # logos/protocols.py
   class SubtheoryProtocol(Protocol):
       """Standard interface for all logos subtheories."""
       def get_operators(self) -> Dict[str, Type[Operator]]: ...
       def get_semantics(self) -> Type[Semantics]: ...
       def validate_config(self, config: Dict) -> bool: ...
   ```

2. Improve Error Handling:
   - Add specific exceptions for subtheory loading
   - Better error messages for configuration issues
   - Example: "SubtheoryNotFoundError: Unknown subtheory 'quantum'"

3. Performance Optimizations:
   - Profile Z3 constraint generation
   - Add caching for expensive operations
   - Optimize model iteration for large state spaces

PHASE 3: DOCUMENTATION & TESTING

1. Run All Tests Including Subtheories:
   ```bash
   pytest Code/src/model_checker/theory_lib/logos/tests/ -v
   pytest Code/src/model_checker/theory_lib/logos/subtheories/*/tests/ -v
   ```

2. Verify Examples:
   ```bash
   python Code/dev_cli.py Code/src/model_checker/theory_lib/logos/examples.py
   ```

3. Verify Each Subtheory:
   ```bash
   for subtheory in extensional modal constitutive counterfactual relevance; do
     echo "Testing $subtheory..."
     python Code/dev_cli.py -l logos -c $subtheory <test_file>
   done
   ```

EXPECTED DELIVERABLES:
- 95% type hint coverage
- Full iterator contract compliance
- Integrated subtheory testing
- Standardized subtheory protocol
- All tests passing (including subtheories)
- Examples running successfully via dev_cli.py

WHAT NOT TO CHANGE:
- The subtheory plugin architecture
- Fine's truthmaker semantic foundation
- Subtheory-specific logic
- Public API signatures
- The sophisticated operator system

SPECIAL CONSIDERATIONS:
- Logos serves as base for imposition - changes must not break imposition
- Subtheory system is unique - preserve its flexibility
- Most mature codebase - focus on polish, not restructuring

Report all changes made and verify subtheory compatibility.
```

## Execution Instructions for Main Agent

```
Launch three general-purpose subagents IN PARALLEL to refactor the theories.

Each subagent should:
1. Read their specific prompt above
2. Analyze the current code structure
3. Implement refactoring in phases
4. Run tests after each phase
5. Verify examples work with dev_cli.py
6. Report results

CRITICAL: All three subagents must work simultaneously. Use parallel Task tool invocations.

After all complete, create a summary report at:
Code/src/model_checker/theory_lib/specs/reports/refactoring_results.md

The summary should include:
- Changes made to each theory
- Test results (all must pass)
- dev_cli.py verification status
- Any issues encountered
- Recommendations for future work

IMPORTANT REMINDERS:
1. Do NOT create theory_lib/common/ - use existing framework packages
2. Preserve each theory's unique characteristics:
   - Exclusion: witness-based semantics
   - Imposition: Fine's truthmaker, logos inheritance
   - Logos: subtheory architecture
3. ALL tests must pass
4. ALL examples must work via dev_cli.py
5. Maintain backward compatibility
```

## Success Criteria

✅ All existing tests pass for all theories
✅ Examples run successfully via `python Code/dev_cli.py {theory}/examples.py`
✅ No breaking changes to public APIs
✅ File sizes under 500 lines (except where justified)
✅ Type hint coverage improved (target >90%)
✅ Import organization fixed (no duplicates)
✅ Each theory's unique characteristics preserved
✅ Code follows ModelChecker standards from Code/docs/

## Risk Mitigation

1. **Test First**: Run tests before any changes to establish baseline
2. **Incremental Changes**: Refactor in small steps, testing after each
3. **Preserve Uniqueness**: Don't force uniformity where differences are intentional
4. **Backward Compatibility**: Keep all public APIs unchanged
5. **Version Control**: Ensure git tracks all changes for easy rollback