# Violation Inventory: Doc-Flag Lint RED Demonstration

**Source**: `PYTHONPATH=code/src pytest code/tests/cli/test_docs_flag_matrix.py -v` (Phase 2,
before Phase 3-8 fixes).

## Summary (before fixes)

- Files scanned: 204
- Violating files: 11
- Violating tokens: 46

Plan's Scope Hypothesis predicted "10 violating files and roughly 47 violating tokens." The
actual scan found 11 files and 46 tokens — close enough (one extra file, one fewer token) that no
phase-to-file reconciliation is needed; the discrepancy is accounted for by the plan-time
prototype rounding and by `docs/usage/OUTPUT.md`/`TOOLS.md` token counts differing slightly from
the prototype estimate.

## Violations grouped by owning phase

### Phase 3 — `docs/usage/WORKFLOW.md`, `docs/usage/PROJECT.md`, `docs/installation/GETTING_STARTED.md`

```
docs/usage/WORKFLOW.md:30: --subtheory
docs/usage/WORKFLOW.md:31: --subtheory
docs/usage/WORKFLOW.md:32: -st
docs/usage/WORKFLOW.md:410: --subtheory

docs/usage/PROJECT.md:20: --subtheory
docs/usage/PROJECT.md:21: --subtheory
docs/usage/PROJECT.md:22: -st
docs/usage/PROJECT.md:117: --subtheory
docs/usage/PROJECT.md:118: --subtheory
docs/usage/PROJECT.md:119: -st
docs/usage/PROJECT.md:460: --test-all-settings
docs/usage/PROJECT.md:463: --benchmark

docs/installation/GETTING_STARTED.md:217: --subtheory
docs/installation/GETTING_STARTED.md:218: --subtheory
docs/installation/GETTING_STARTED.md:219: -st
```

16 tokens (WORKFLOW.md 4, PROJECT.md 8, GETTING_STARTED.md 3 — WORKFLOW.md has one additional
`--subtheory` mention at line 410 beyond the plan's estimate of 5 for that file's total, still
within the same rewrite).

### Phase 4 — `docs/usage/OUTPUT.md`, `docs/usage/TOOLS.md`

```
docs/usage/OUTPUT.md:351: --output-dir
docs/usage/OUTPUT.md:351: --verbose
docs/usage/OUTPUT.md:374: --output-dir
docs/usage/OUTPUT.md:388: --output-dir
docs/usage/OUTPUT.md:417: --output-dir

docs/usage/TOOLS.md:201: --subtheory
docs/usage/TOOLS.md:202: --subtheory
docs/usage/TOOLS.md:203: -st
docs/usage/TOOLS.md:434: --verbose
docs/usage/TOOLS.md:440: --output-dir
```

10 guard-visible tokens. Additional prose-only sites the guard cannot see (per the plan's Risks
table): `--no-terminal` bullet and the `notebook`-as-`--save`-value discussion in OUTPUT.md, to
be fixed by hand.

### Phase 5 — `docs/architecture/PIPELINE.md`, `docs/architecture/SETTINGS.md`, `docs/architecture/ITERATE.md`

```
docs/architecture/PIPELINE.md:56: --format
docs/architecture/PIPELINE.md:56: --verbose
docs/architecture/PIPELINE.md:420: --verbose
```

3 guard-visible tokens, all in PIPELINE.md. SETTINGS.md and ITERATE.md violations are prose/
diagram-only (the `--verbose` diagram bullet, the `# Debug messages (with --verbose)` comment,
and the `DEBUG_CONFIG['verbose']` dict entry) and do not appear in this guard-visible list; they
are fixed by hand per the plan's Risks table.

### Phase 6 — `code/src/model_checker/settings/README.md`

```
code/src/model_checker/settings/README.md:195: --print-z3
code/src/model_checker/settings/README.md:195: -N
code/src/model_checker/settings/README.md:258: --non-null
code/src/model_checker/settings/README.md:261: --non-empty
code/src/model_checker/settings/README.md:264: --M
code/src/model_checker/settings/README.md:264: --align-vertically
code/src/model_checker/settings/README.md:265: --coherence-check
code/src/model_checker/settings/README.md:265: --witness-optimization
code/src/model_checker/settings/README.md:268: --max-time
code/src/model_checker/settings/README.md:268: --print-constraints
code/src/model_checker/settings/README.md:268: --print-impossible
code/src/model_checker/settings/README.md:268: --print-z3
```

12 tokens in this one file, matching the plan's Scope Hypothesis (`--print-z3` appears twice, at
lines 195 and 268, both counted).

### Phase 7 — `code/docs/contracts/THEORY_LICENSING.md`, `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`, `docs/installation/DEVELOPER_SETUP.md`, `code/src/model_checker/output/errors.py`

```
code/docs/contracts/THEORY_LICENSING.md:358: --author
code/docs/contracts/THEORY_LICENSING.md:358: --base-theory
code/docs/contracts/THEORY_LICENSING.md:358: --generate-license
code/docs/contracts/THEORY_LICENSING.md:358: --theory-name

code/src/model_checker/theory_lib/docs/CONTRIBUTING.md:81: -t

docs/installation/DEVELOPER_SETUP.md:173: --profile
```

6 guard-visible tokens across three markdown files, matching the plan's Scope Hypothesis exactly.
Plus one source-string fix in `code/src/model_checker/output/errors.py` (the `--output-dir`
suggestion in `OutputDirectoryError`'s permission branch), which the doc lint does not cover
directly — verified separately by a dedicated unit test.

## Final counts (after Phases 3-8)

To be updated by Phase 8 once the guard's `xfail` marker is removed and the full scan is
confirmed at zero violations.
