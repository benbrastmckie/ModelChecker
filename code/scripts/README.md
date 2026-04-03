# Scripts

Utility scripts for the ModelChecker project.

## comparison.py

Benchmark z3 vs cvc5 on logos theory examples. Runs examples against both solvers, compares results (sat/unsat/timeout), and records timing data.

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

