# Scripts

Utility scripts for the ModelChecker project.

## comparison.py

Benchmark Z3 vs CVC5 on logos theory examples. Runs examples against both solvers, compares results (sat/unsat/timeout), and records timing data.

Outputs both JSON and Markdown reports.

### Usage

```bash
# Run curated 24 examples with ASCII table output
./code/scripts/comparison.py --curated --table

# Run all examples (full benchmark)
./code/scripts/comparison.py

# Curated examples with timing-focused JSON
./code/scripts/comparison.py --curated --format timing

# Filter to a single subtheory
./code/scripts/comparison.py --curated --subtheory modal

# Custom output path and timeout
./code/scripts/comparison.py --curated --output results.json --timeout 60
```

### Flags

| Flag | Description |
|------|-------------|
| `--curated, -c` | Run curated 24 examples (4 per subtheory: 2 theorems + 2 countermodels) |
| `--format, -f` | Output format: `full` (default) or `timing` (simplified) |
| `--table` | Print ASCII table to console |
| `--output, -o` | Output file path (default: `output.json`); markdown written alongside as `.md` |
| `--subtheory, -s` | Filter to a specific subtheory |
| `--verbose, -v` | Show detailed per-example output |
| `--timeout, -t` | Timeout per example per solver in seconds (default: 30) |

### Output Files

Each run produces two files:

- **JSON** (`output.json`): Machine-readable results with metadata, timing summaries, per-example results, and disagreements
- **Markdown** (`output.md`): Human-readable report with tables for timing summary, comparison statistics, and per-example results

## first_order_benchmark.py

Benchmark comparing four quantifier configurations for the first-order subtheory: finitary-z3, finitary-cvc5, native-z3, and native-cvc5. Includes 46 stress test examples across five test suites designed to expose performance boundaries and correctness differences.

### Usage

```bash
# Quick test with 4 baseline examples
cd code && python scripts/first_order_benchmark.py --quick --format table -v

# Run all suites across all 4 modes
cd code && python scripts/first_order_benchmark.py --suite all --format table -v

# Run a specific suite (scaling, nesting, alternation, complexity, stress)
cd code && python scripts/first_order_benchmark.py --suite scaling --format table -v

# Specific solver modes only
cd code && python scripts/first_order_benchmark.py --modes finitary-z3,native-z3 --format table -v

# Find the N value where an example times out
cd code && python scripts/first_order_benchmark.py --find-choke-point N_SCALE_TH_1
```

### Flags

| Flag | Description |
|------|-------------|
| `--quick, -q` | Run quick test with 4 baseline examples |
| `--suite, -s` | Test suite: `baseline`, `scaling`, `nesting`, `alternation`, `complexity`, `stress`, `all` |
| `--modes, -m` | Comma-separated modes (default: all four) |
| `--format, -f` | Output format: `json` (default), `table`, `markdown` |
| `--output, -o` | Output file path (default: `first_order_output.json`) |
| `--timeout, -t` | Timeout per example in seconds (default: 30) |
| `--verbose, -v` | Print progress during benchmark |
| `--find-choke-point` | Binary search for the N value where an example times out |

### Test Suites

| Suite | Description |
|-------|-------------|
| `baseline` | Original FO_TH/FO_CM examples at N=2 |
| `scaling` | Domain size scaling (N=2 through N=10) |
| `nesting` | Quantifier nesting depth (1-5 levels) |
| `alternation` | Quantifier alternation patterns (AA, EE, AE, EA, AEA, EAE) |
| `complexity` | Formula complexity (conjunctions, disjunctions, nested implications) |
| `stress` | Extreme cases (N=10, depth 5, many predicates) |

### Output Files

- **JSON** (`first_order_output.json`): Per-example results with timing and correctness data
- **Markdown** (`first_order_output.md`): Human-readable comparison tables

## quantifier_benchmark.py

Benchmark comparing finitary vs native quantifier implementations across three configurations: finitary+Z3, native+Z3, and native+CVC5. Predates `first_order_benchmark.py` and uses the general `examples.py` quantifier examples rather than the first-order subtheory.

### Usage

```bash
cd code && python scripts/quantifier_benchmark.py --quick --format table
cd code && python scripts/quantifier_benchmark.py --modes finitary,z3-native
cd code && python scripts/quantifier_benchmark.py --timeout 60
```

## test_cvc5_stability.py

CVC5 vs Z3 performance stability benchmark. Runs curated examples multiple times to measure timing variance and produce statistically meaningful comparisons. Reports mean, stddev, min, max per example.

### Usage

```bash
cd code && PYTHONPATH=src python scripts/test_cvc5_stability.py
```

