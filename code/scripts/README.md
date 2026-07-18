# Scripts

Utility scripts for the ModelChecker project.

## Background: Finitary vs Native Quantifiers

For a deep dive on how quantifiers work internally in Z3 and CVC5, see [Quantifier Handling in SMT Solvers](../../docs/theory/QUANTIFIER_SOLVERS.md).

The model checker operates over finite state spaces (bit vectors of width N, giving 2^N domain elements), so quantifiers can be implemented two ways:

- **Finitary** (`\forall`, `\exists`): Iterates the bound variable through every value in the finite domain (0 to 2^N - 1), evaluating the formula body at each value. `ForAll` takes the conjunction of all 2^N instances; `Exists` takes the disjunction. The result is a flat boolean constraint with no quantifiers -- the solver sees only propositional logic over bit vectors.

- **Native** (`\all`, `\some`): Creates a single symbolic bound variable and passes it with the formula body to the solver's built-in `z3.ForAll()` or `z3.Exists()`. The solver then handles quantifier instantiation internally using its own heuristics (e-matching, MBQI, model-based reasoning). The constraint sent to the solver contains an actual quantifier rather than an expanded boolean combination.

Each approach can be paired with either Z3 or CVC5 as the solver backend, giving four configurations. Native quantifiers are generally faster (2-3x) since the solver can reason about the quantifier structure directly rather than processing 2^N separate constraints. However, native-cvc5 returns incorrect UNSAT for all countermodel (sat) queries in benchmarks.

### Why Native Quantifiers Can Fail

When a solver receives a native quantifier, it uses heuristic strategies to decide which values to instantiate:

- **E-matching** (Z3, CVC5): Instantiates the quantifier only when ground terms matching a trigger pattern appear in the proof context. Fast but incomplete -- if no patterns fire, nothing happens.
- **MBQI** (Z3 only): Builds a candidate model, checks if the quantifier is violated, and adds the violating instance as a new constraint. Complete for bit-vector (QBVF) fragments but can be slow.
- **CEGQI** (CVC5 only): Uses algebraic inversion to compute exact instantiation terms. Precise for arithmetic and bitvectors, but requires invertible formulas.

The critical behavioral difference: when strategies exhaust without a definitive answer, **Z3 may return `unsat` even for satisfiable formulas** (an incorrect result), while **CVC5 returns `unknown`** (conservative but honest). For countermodel search, both mean "no model found," but Z3's answer looks like a valid proof when it is not.

For ModelChecker's small bit-vector domains (N=2 to N=6), finitary quantifiers are recommended because explicit enumeration is tractable and always correct. Native quantifiers are useful for exploring solver-level reasoning or domains too large to enumerate.

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

Benchmark comparing finitary vs native quantifier implementations across three configurations: finitary+Z3, native+Z3, and native+CVC5. Uses the general `examples.py` quantifier examples.

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

