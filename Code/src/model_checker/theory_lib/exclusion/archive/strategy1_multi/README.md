# Strategy 1: Multi-Strategy Implementation

## Overview
**Date**: Pre-2024  
**Status**: Base Strategy with Multiple Sub-Strategies  
**Key Feature**: 12 different sub-strategies for the exclusion operator

## Description
This implementation introduced a complex multi-strategy architecture with 12 different approaches to implementing the exclusion operator:
- QA (Quantify Arrays)
- QI (Quantify Indices)
- QI2 (Quantify Indices 2)
- BQI (Bounded Quantify Indices)
- NF (Name Functions)
- NA (Name Arrays)
- SK (Skolemized)
- CD (Constraint-Based)
- MS (Multi-Sort) - default
- UF (Uninterpreted Functions)
- WD (Witness-Driven)

## Key Files
- `semantic.py`: Multi-strategy semantic implementation with strategy support
- `operators.py`: Contains all 12 exclusion operator strategies
- `examples.py`: Compatible test examples

## Known Issues
- Same false premise issue persists across all strategies
- 8-10 examples with false premises depending on strategy
- Complex codebase (~1000 lines in operators.py)

## Running This Strategy
```bash
cd /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code
./dev_cli.py -p -z src/model_checker/theory_lib/exclusion/strategy2_multi/examples.py
```

To use a different strategy, modify the DEFAULT_STRATEGY in operators.py.

## Documentation
- [`docs/old_strategies.md`](docs/old_strategies.md): Documentation of all 12 strategies

## Why This Approach Was Eventually Simplified
The multi-strategy approach added significant complexity without solving the false premise issue, leading to the simplification effort in attempt4_new_implementation/.
