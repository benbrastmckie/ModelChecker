# Scripts

Utility scripts for the ModelChecker project.

## Background: Finitary vs Native Quantifiers

The model checker operates over finite state spaces (bit vectors of width N, giving 2^N domain elements), so quantifiers can be implemented two ways:

- **Finitary** (`\forall`, `\exists`): Iterates the bound variable through every value in the finite domain (0 to 2^N - 1), evaluating the formula body at each value. `ForAll` takes the conjunction of all 2^N instances; `Exists` takes the disjunction. The result is a flat boolean constraint with no quantifiers -- the solver sees only propositional logic over bit vectors.

- **Native** (`\all`, `\some`): Creates a single symbolic bound variable and passes it with the formula body to the solver's built-in `z3.ForAll()` or `z3.Exists()`. The solver then handles quantifier instantiation internally using its own heuristics (e-matching, MBQI, model-based reasoning). The constraint sent to the solver contains an actual quantifier rather than an expanded boolean combination.

Each approach can be paired with either Z3 or CVC5 as the solver backend, giving four configurations. Native quantifiers are generally faster (2-3x) since the solver can reason about the quantifier structure directly rather than processing 2^N separate constraints. However, native-cvc5 has a critical correctness bug where it returns incorrect UNSAT for all countermodel (sat) queries.

## first_order_benchmark.py

Benchmark comparing the four quantifier configurations for the first-order subtheory: finitary-z3, finitary-cvc5, native-z3, and native-cvc5. Includes 35 examples across six test suites designed to expose performance boundaries and correctness differences between solver/quantifier combinations.

Known issue: native-cvc5 returns incorrect UNSAT for all countermodel (sat) examples.

### Usage

```bash
# Recommended: all suites, all 4 modes, table output with progress
cd code && python scripts/first_order_benchmark.py --suite all --format table -v

# Quick 4-example smoke test
cd code && python scripts/first_order_benchmark.py --quick --format table -v

# Run a specific suite (baseline, scaling, nesting, alternation, complexity, stress)
cd code && python scripts/first_order_benchmark.py --suite scaling --format table -v

# Specific solver modes only
cd code && python scripts/first_order_benchmark.py --suite all --modes finitary-z3,native-z3 --format table -v

# Find the N value where an example times out
cd code && python scripts/first_order_benchmark.py --find-choke-point N_SCALE_TH_1

# Custom timeout and output path
cd code && python scripts/first_order_benchmark.py --suite all --timeout 60 --output results.json
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

| Suite | Examples | Description |
|-------|----------|-------------|
| `baseline` | 12 | Original FO_TH/FO_CM examples at N=2 |
| `scaling` | 3 | Domain size scaling via N parameter |
| `nesting` | 6 | Quantifier nesting depth (1-5 levels) |
| `alternation` | 7 | Quantifier alternation patterns (AA, EE, AE, EA, AEA, EAE) |
| `complexity` | 4 | Formula complexity (conjunctions, disjunctions, nested implications) |
| `stress` | 3 | Extreme cases (N=10, depth 5, many predicates) |
| `all` | 35 | All suites combined |

### Output Files

- **JSON** (`first_order_output.json`): Per-example results with timing and correctness data
- **Markdown** (`first_order_output.md`): Human-readable comparison tables with timing summary, 2x2 comparison matrix, and disagreement details

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

