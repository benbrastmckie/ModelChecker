# Examples and the CLI
[← Spec map](./README.md)

> The example-file format — the user's real input language — examples as the executable
> behavioral specification, the CLI surface, entry points, and project generation, Jupyter, and
> packaging in brief.

## The example file: an ordinary module, executed on load

An examples file is **an ordinary Python module, executed on load** — not a data format read by a
parser. The loader requires exactly two module-level names and accepts a third:

| Name | Required | Shape |
|---|---|---|
| `semantic_theories` | yes | `{display_name: TheoryDict}` — one or more theories to run each example under |
| `example_range` | yes | `{example_name: ExampleCase}` — what actually runs |
| `general_settings` | no | a settings override dict |

`TheoryDict` carries the theory's four `get_theory()` components (see
[`10-theory-contract.md`](./10-theory-contract.md)) plus an optional fifth key, `dictionary`: an
operator-rename map applied by **plain string substitution** to every premise and conclusion
before parsing — a mechanism for running the same example text under a theory that uses different
operator tokens. `ExampleCase` is a three-element list: `[premises, conclusions, settings]`.

## Conventions that *are* the behavioral specification

Nothing in the loader enforces these, but every shipped example file follows them, and the
`expectation` setting is the actual oracle:

- `{PREFIX}_CM_{n}` names a countermodel-expected example (`expectation: True` — the argument is
  invalid); `{PREFIX}_TH_{n}` names a theorem (`expectation: False` — the argument is valid).
- A `unit_tests` dict holds the *complete* set of examples in a module, consumed by the test
  suite; `example_range` is a smaller, curated subset selected for interactive/default runs,
  conventionally maintained as a dict literal with most entries commented out.
- Each theory's test suite parametrizes directly over `unit_tests` and rebuilds the five-stage
  pipeline without going through the CLI/builder layer at all — **the examples corpus is the
  executable specification**, not illustrative sample input.

```mermaid
flowchart TD
    A["model-checker examples.py"] --> B[module executes:<br/>semantic_theories, example_range]
    B --> C{"for each example_name<br/>× each theory"}
    C --> D[apply operator<br/>dictionary translation]
    D --> E["build → solve → print"]
    E --> F{--save?}
    F -->|yes| G[collect + write<br/>EXAMPLES.md / MODELS.json]
    F -->|no| H[terminal output only]
```

## The CLI surface

One positional argument (the examples file path) plus 17 options.

| Flag | Short | Effect |
|---|---|---|
| `file_path` | — | path to the examples file (optional; omitted ⇒ interactive project generation) |
| `--load_theory` | `-l` | generate a new project from a theory instead of running a file |
| `--contingent` | `-c` | settings override |
| `--non_null` | `-n` | settings override |
| `--non_empty` | `-e` | settings override |
| `--disjoint` | `-d` | settings override |
| `--maximize` | `-m` | theory-comparison mode (see [`09-output-and-display.md`](./09-output-and-display.md)) |
| `--save [FMT...]` | `-s` | enable output saving; no format given = both markdown and json |
| `--sequential` | `-q` | **registered but nonfunctional** — parses successfully, then raises a not-implemented error before doing anything |
| `--align_vertically` | `-a` | vertical temporal display (the temporal theory only) |
| `--z3` | — | select the Z3 backend (mutually exclusive with `--cvc5`) |
| `--cvc5` | — | select the cvc5 backend |
| `--print_constraints` | `-p` | show solver constraints |
| `--print_z3` | `-z` | show raw solver output |
| `--print_impossible` | `-i` | include impossible states in display |
| `--version` | `-v` | print version and exit |
| `--upgrade` | `-u` | upgrade the installed package |

The `--sequential` entry is marked nonfunctional deliberately: the flag exists, is documented
elsewhere in the repository as working, and is registered on the parser — but its implementation
was removed and the code path now raises unconditionally. A guard test that scans documentation
for invocation examples and checks flag registration cannot catch this class of gap (the flag
*is* registered); it is worth naming explicitly so a port does not treat "the flag exists" as
evidence the feature does.

## Entry points

Three ways to invoke the tool: an installed console script, `python -m` module execution, and a
development wrapper that prepends the working tree's source directory to the import path so local
changes are picked up ahead of any installed copy. All three converge on the same `main()`. With
no file-path argument, every entry point runs interactive project generation instead of executing
an examples file.

## Project generation, Jupyter, and packaging

**Project generation** copies a theory's directory according to an explicit required/optional
manifest (not a verbatim tree copy), writes a marker file recording which theory the project was
generated from, and rewrites version strings in the copied package by regex. **Jupyter
integration** is two-tier: always-available helpers (Unicode ↔ LaTeX conversion, environment
setup) plus a dependency-gated interactive layer (a full widget UI with a formula box, theory
dropdown, per-theory settings, and a graph visualization of the found model) that degrades to
typed stub errors when its optional dependencies are absent; the notebook path bypasses the
ordinary module-loading machinery entirely and constructs the pipeline directly.
**Packaging** uses an explicit package-data allowlist rather than a blanket glob (so stray files
under a theory's directory are not silently shipped), with a dedicated test suite that builds real
wheels and sdists and asserts on their contents, entry points, and console-script execution.

## Source files

- [`builder/validation.py`](../../code/src/model_checker/builder/validation.py) — `TheoryDict`
  and `ExampleCase` validation
- [`builder/translation.py`](../../code/src/model_checker/builder/translation.py) — the
  `dictionary` operator-rename substitution
- [`__main__.py`](../../code/src/model_checker/__main__.py) — the argument parser, the 17-option
  surface
- [`builder/module.py`](../../code/src/model_checker/builder/module.py) — `BuildModule`, module
  loading and execution flow
- [`builder/project.py`](../../code/src/model_checker/builder/project.py) — `BuildProject`,
  project generation
- [`jupyter/`](../../code/src/model_checker/jupyter/) — the notebook integration layer

## Related

- [Output and display](./09-output-and-display.md) — where `--save`/`--maximize` route to
- [The theory contract](./10-theory-contract.md) — the `TheoryDict` shape this file's loader
  validates
- [Settings and the registry](./12-settings-and-registry.md) — the full precedence chain these
  flags feed into
