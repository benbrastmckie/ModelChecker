# Exclusion Theory Test Suite for Improvements

This test suite is designed for evaluating and tracking improvements to exclusion theories, particularly focusing on reducing false premise and true conclusion rates.

## Test Files Overview

### 1. `test_suite_for_improvements.py` - **Main Comprehensive Test**
**Purpose**: Full evaluation of all strategies on all examples
**Usage**:
```bash
# Test all strategies with default settings
python test_suite_for_improvements.py

# Test specific strategies with custom timeout
python test_suite_for_improvements.py --strategies QA,CD,MS --timeout 3

# Test without saving results
python test_suite_for_improvements.py --no-save

# Compare with baseline
python test_suite_for_improvements.py --baseline baseline_20250129_143022.json
```

**Output**: 
- Comprehensive strategy comparison table
- Rankings by total issues and performance
- Saves timestamped JSON results for tracking improvements

### 2. `quick_strategy_test.py` - **Rapid Iteration Test**
**Purpose**: Fast testing of key examples for rapid development iteration
**Usage**:
```bash
python quick_strategy_test.py
```

**Features**:
- Tests 3 main strategies (QA, CD, MS) on 5 key problematic examples
- Very fast execution (~10-30 seconds)
- Perfect for testing small changes quickly

### 3. `baseline_comparison.py` - **Progress Tracking**
**Purpose**: Compare results before/after improvements
**Usage**:
```bash
# Compare two result files
python baseline_comparison.py baseline.json current.json

# Create a new baseline
python baseline_comparison.py baseline.json current.json --create-baseline new_baseline.json
```

**Features**:
- Detailed comparison report
- Shows improvements/regressions per strategy
- Performance comparison
- Example-specific change analysis

### 4. Legacy Tests (Keep for Reference)
- `test_detailed_analysis.py` - Detailed example-by-example analysis
- `test_false_premise_fix.py` - Validation that the fix works
- `test_strategy_false_premises.py` - Original strategy comparison

## Workflow for Theory Improvements

### 1. **Establish Baseline**
```bash
# Run full evaluation to establish baseline
python test_suite_for_improvements.py
# This creates: exclusion_evaluation_YYYYMMDD_HHMMSS.json
```

### 2. **Make Theory Changes**
Edit exclusion theory files (semantic.py, operators.py, etc.)

### 3. **Quick Testing During Development**
```bash
# Fast check of key examples
python quick_strategy_test.py
```

### 4. **Full Evaluation After Changes**
```bash
# Full test with comparison to baseline
python test_suite_for_improvements.py --baseline exclusion_evaluation_YYYYMMDD_HHMMSS.json
```

### 5. **Detailed Analysis of Changes**
```bash
python baseline_comparison.py baseline.json current.json
```

## Key Metrics to Track

### Primary Metrics (Lower is Better)
- **Total Issues**: False premises + True conclusions
- **Models with Issues**: Count of problematic models
- **Issue Rate**: Percentage of models with issues

### Secondary Metrics
- **Performance**: Average runtime per model
- **Model Count**: Total models found (higher can be good or bad)
- **Example-Specific**: Which examples are most/least problematic

## Current Baseline Results (Reference)

### Strategy Rankings (Best to Worst by Total Issues)
1. **QA**: 13 total issues (best accuracy, slower)
2. **CD**: 17 total issues (good balance)
3. **MS**: 17 total issues (fastest)
4. **Others**: 17-18 total issues

### Most Problematic Examples
- DISJ_SYLL: Both false premises and true conclusions
- CONJ_DM_RL/LR: Consistent false premises
- DISJ_DM_RL/LR: Consistent false premises
- DN_ELIM: False premises across strategies

### Clean Examples (No Issues)
- DN_ID: Valid across all strategies
- DN_INTRO: Valid across all strategies
- EMPTY: Basic test case
- DISJ_DIST_ID: Valid countermodel

## Tips for Theory Improvements

### Focus Areas
1. **Constraint Generation**: Most issues stem from Z3 finding models with empty verifiers
2. **Exclusion Function Implementation**: Different strategies have different issue patterns
3. **Truth Evaluation**: Already fixed, but validate any changes don't break it

### Testing Strategy
1. Use `quick_strategy_test.py` for rapid iteration
2. Focus on QA strategy first (most reliable baseline)
3. Test improvements on most problematic examples first
4. Use full test suite to validate improvements don't cause regressions

### Success Criteria
- **Primary Goal**: Reduce total issues across all strategies
- **Secondary Goal**: Maintain or improve performance
- **Quality Goal**: Increase number of "clean" examples with no issues

## File Locations

All test files are in: `src/model_checker/theory_lib/exclusion/test/`

Result files are saved in the same directory with timestamps for easy tracking.