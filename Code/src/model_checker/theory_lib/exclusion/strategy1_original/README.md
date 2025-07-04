# Strategy 1: Original Single-Strategy Implementation

## Overview
**Date**: Pre-2024  
**Status**: Base Strategy  
**Key Feature**: Single approach to exclusion operator

## Description
This is the original implementation of exclusion semantics with a single strategy for the exclusion operator. It uses a straightforward approach without the complexity of multiple sub-strategies.

## Key Files
- `semantic.py`: Original semantic implementation (from semantic_old.py)
- `operators.py`: Original operators with single exclusion approach (from operators_old.py)
- `examples.py`: 34 test examples

## Known Issues
- 8 examples produce models with false premises:
  - Double Negation Elimination
  - Triple Negation Entailment
  - Quadruple Negation Entailment
  - Conjunctive DeMorgan's (both directions)
  - Disjunctive DeMorgan's (both directions)
  - EX_TH_17

## Running This Strategy
```bash
cd /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/strategy1_original/examples.py
```

## Documentation
- [`docs/unilateral_semantics.md`](docs/unilateral_semantics.md): Theoretical foundation

## Why Multiple Refactoring Attempts Were Made
The false premise issue prompted several attempts to fix this implementation, leading to various refactoring efforts documented in attempt1_refactor_old/.