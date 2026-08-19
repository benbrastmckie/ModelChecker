# ModelChecker User-Facing Surface: CLI, Build Layer, Example-File Format, Jupyter, Packaging

Territory: `code/src/model_checker/builder/`, `code/src/model_checker/__main__.py`,
`code/src/model_checker/jupyter/`, `code/dev_cli.py`, `code/pyproject.toml`, `code/tests/`
(CLI contract only), user docs. All line numbers verified against the working tree on this
date; every flag below was verified against the actual `argparse` definitions, not docs.

## 1. CLI Surface

The single parser is built by `ParseFileFlags._create_parser()` in
`code/src/model_checker/__main__.py:35-193`. `prog='model-checker'`, usage
`%(prog)s [options] [file_path]` (`__main__.py:43-60`). One positional argument plus 17
options in 6 argparse groups. The theory list for `-l` is derived at parser-construction
time from the runtime registry (`__main__.py:74-75`: `registry.get_registered()`), which
`theory_lib/__init__.py:63-68` populates as `['bimodal', 'logos', 'exclusion', 'imposition']`
(registration order; `theory_lib/__init__.py:472-475`).

| Flag | Short | argparse kind | Default | Effect | Definition |
|---|---|---|---|---|---|
| `file_path` (positional) | — | `nargs='?'`, `type=str` | `None` | Path to Python examples file | `__main__.py:62-68` |
| `--load_theory THEORY` | `-l` | `type=str`, `choices=registry.get_registered()` | `None` | Skip file execution; run `BuildProject(theory).ask_generate()` (`__main__.py:288-292`) | `__main__.py:77-84` |
| `--contingent` | `-c` | `store_true` | `False` | Settings override: propositions neither necessary nor impossible | `__main__.py:88-93` |
| `--non_null` | `-n` | `store_true` | `False` | Settings override: null state can't verify/falsify | `__main__.py:94-99` |
| `--non_empty` | `-e` | `store_true` | `False` | Settings override: non-empty verifier/falsifier sets | `__main__.py:100-105` |
| `--disjoint` | `-d` | `store_true` | `False` | Settings override: disjoint subject matters | `__main__.py:106-111` |
| `--maximize` | `-m` | `store_true` | `False` | Theory-comparison mode (`ModelComparison.run_comparison()`, `__main__.py:301-303`) | `__main__.py:112-117` |
| `--save [FMT ...]` | `-s` | `nargs='*'`, `choices=['markdown','json']` | `None` | Enable output saving; zero args = both formats | `__main__.py:121-129` |
| `--sequential` | `-q` | `store_true` | `False` | **Nonfunctional**: raises `NotImplementedError` at `BuildModule` init (`builder/module.py:145-152`) | `__main__.py:130-135` |
| `--align_vertically` | `-a` | `store_true` | `False` | Settings override: vertical temporal display (bimodal) | `__main__.py:136-141` |
| `--z3` | — | `store_true`, mutually exclusive with `--cvc5` | `False` | Select Z3 backend (`__main__.py:268-270`) | `__main__.py:145-150` |
| `--cvc5` | — | `store_true` | `False` | Select cvc5 backend; validated, friendly error if not installed (`__main__.py:271-279`) | `__main__.py:151-155` |
| `--print_constraints` | `-p` | `store_true` | `False` | Show solver constraints | `__main__.py:159-164` |
| `--print_z3` | `-z` | `store_true` | `False` | Show raw Z3 output | `__main__.py:165-170` |
| `--print_impossible` | `-i` | `store_true` | `False` | Include impossible states in display | `__main__.py:171-176` |
| `--version` | `-v` | `action='version'` | — | Print `model-checker:  {__version__}` and exit | `__main__.py:180-186` |
| `--upgrade` | `-u` | `store_true` | `False` | `pip install --upgrade model-checker` via subprocess (`__main__.py:281-287`) | `__main__.py:187-192` |

Flag-to-settings plumbing: `parse()` (`__main__.py:195-237`) attaches two private attributes
to the parsed namespace — `_short_to_long` (a hand-maintained short→long map,
`__main__.py:208-223`) and `_parsed_args` (the raw `sys.argv[1:]`, `__main__.py:227`). The
settings layer (`settings/settings.py:202-240`) inspects `_parsed_args` to determine which
flags the user *actually typed*, because `store_true` defaults are indistinguishable from
explicit `False` in the namespace. Only explicitly-typed flags override example settings.
Known gap, documented in source: clustered short flags (`-cn`) are parsed by argparse but NOT
detected as user-provided, so their overrides silently don't apply
(`settings/settings.py:213-220`). The absence of `_parsed_args` is used as a mock-detection
heuristic (`settings/settings.py:190-199`): mock flag objects apply ALL attributes as
overrides.

Settings priority order (docstring at `settings/settings.py:6-10`): theory defaults <
module `general_settings` < example settings < CLI flags. `standard_args` — flags exempt
from "unknown setting" warnings — still lists `'interactive'`, `'output_mode'`,
`'sequential_files'`, which no longer exist as flags (`settings/settings.py:252-254`).

Wrapper-only flags (accepted by `./dev_cli.py`, unknown to argparse): `--iso-debug`
(consumed, enables isomorphism debug logging, `code/dev_cli.py:36-41`), `-load`/`--load`
(rewritten in place to `-l`, `code/dev_cli.py:48-55`). These are allowlisted in
`code/tests/cli/test_docs_flag_matrix.py:41-44`.

## 2. Entry Points

- **Installed console script**: `model-checker = "model_checker.__main__:run"` —
  `code/pyproject.toml:65-66` (`[project.scripts]`). `run()` is a trivial wrapper over
  `main()` (`__main__.py:308-310`).
- **Module execution**: `python -m model_checker` hits the
  `if __name__ == '__main__': run()` guard (`__main__.py:312-313`). Same behavior as the
  console script.
- **Development CLI**: `code/dev_cli.py` (65 lines). Prepends `code/src` to `sys.path`
  (`dev_cli.py:16-17`) so the working tree shadows any installed wheel, configures a
  root logger at INFO to stdout (`dev_cli.py:8-13`), rewrites the wrapper flags above, then
  calls the same `main()`. With no args it mimics installed behavior:
  `BuildProject().ask_generate()` (`dev_cli.py:60-64`).
- **No-argument behavior** (both entry points): `main()` with `len(sys.argv) < 2` runs
  interactive project generation, `BuildProject().ask_generate()` (`__main__.py:260-263`),
  defaulting to the first registered theory (`builder/project.py:116-124` — i.e. `bimodal`
  per registration order, though `dev_cli.py`'s no-arg path constructs `BuildProject()`
  identically).
- Test infrastructure distinguishes three CLI invocation modes via
  `MODELCHECKER_CLI_TEST_MODE` = `source` | `installed` | `installed-module`
  (`code/tests/cli/test_cli_mode.py:24-37`), with an anti-shadowing guard asserting the
  source tree is NOT importable in installed modes
  (`code/tests/cli/test_installed_mode_guard.py`).

## 3. Execution Flow (`model-checker examples.py` → printed results)

1. `run()` → `main()` (`__main__.py:239-306`). Solver backend selected from `--z3`/`--cvc5`
   (`__main__.py:267-279`); `--upgrade` and `-l` short-circuit and return.
2. `BuildModule(module_flags)` (`__main__.py:294-298`; class at `builder/module.py:27`).
   Its `__init__` (`module.py:48-85`) sequences: `_load_module()` → capture
   `module_variables` → `_initialize_settings()` → `_initialize_output_management()` →
   `_initialize_components()`.
3. **Module loading** (`module.py:87-102`): `ModuleLoader(module_name, module_path)`
   (`builder/loader.py:20`) where `module_name` is the filename stem (`module.py:61`).
   `load_module()` (`loader.py:47-73`) fail-fasts if the file doesn't exist, then picks one
   of three import strategies (`builder/strategies.py`):
   - `TheoryLibImportStrategy` if the file resolves under the theory_lib package root
     (detected via the registry, `loader.py:83-102`, `loader.py:179-201`): converts the file
     path to a dotted module name and does a real `importlib.import_module` +
     `importlib.reload` (`strategies.py:279-310`) so relative imports inside theories work.
   - `PackageImportStrategy` if an ancestor directory contains a `.modelchecker` marker file
     with `package=true` (`builder/detector.py:52-65`, `strategies.py:140-165`): permanently
     inserts the package root and its parent into `sys.path` (`strategies.py:75-82`), imports
     `<pkg>.<relpath-as-dots>`; on relative-import failure falls back to a manual
     `exec(compile(...))` with `__package__` forced (`strategies.py:100-132`).
   - `StandardImportStrategy` otherwise (`strategies.py:168-230`): permanently inserts the
     file's directory into `sys.path`, `spec_from_file_location` + `exec_module`. The user's
     file is **executed as arbitrary Python** (configuration-by-execution).
   Failure mode: everything is wrapped into `PackageImportError` with a
   message/context/suggestion triple (`strategies.py:219-230`, `builder/errors.py:62`).
4. **Required attributes** are pulled with `loader.load_attribute()` which raises
   `ImportError` naming the missing attribute (`loader.py:115-132`): `semantic_theories`
   and `example_range` are mandatory (`module.py:98-99`); `general_settings` is optional
   (`module.py:102`).
5. **Settings** (`module.py:104-127`): a temporary `SettingsManager` seeded with the *first*
   theory's defaults validates `general_settings` and applies CLI overrides, with warnings
   printed during this phase deliberately swallowed via `redirect_stdout`
   (`module.py:118-121`). Each resulting key is also `setattr` onto the BuildModule
   (`module.py:126-127`). Base general-settings vocabulary comes from
   `SemanticDefaults.DEFAULT_GENERAL_SETTINGS` (`models/semantic.py:78-86`):
   `print_impossible, print_constraints, print_z3, save_output, sequential, maximize,
   solver` — augmented by theory `ADDITIONAL_GENERAL_SETTINGS`
   (`settings/settings.py:78-82`).
6. **Output management** (`module.py:129-166`): `create_output_config(flags, settings)`
   (`output/config.py:42-89`) maps `--save`/`--sequential` into an `OutputConfig`;
   `sequential=True` raises `NotImplementedError` (`module.py:145-152`). An `OutputManager`
   (`output/manager.py:22`) is created; if saving, a directory `output_{YYYYMMDD_HHMMSS}`
   is created in the CWD (`output/manager.py:88-100`).
7. **Components** (`module.py:168-181`): `ModelRunner(self)`, `ModelComparison(self)`,
   `OperatorTranslation()`.
8. Back in `main()`: `--maximize` (or `general_settings["maximize"]`) routes to
   `module.comparison.run_comparison()` (`__main__.py:301-303`); otherwise
   `module.runner.run_examples()` (`__main__.py:306`).
9. **`ModelRunner.run_examples()`** (`builder/runner.py:722-779`): nested loop —
   `for example_name, example_case in example_range.items(): for theory_name,
   semantic_theory in semantic_theories.items():` — copies the settings dict per theory
   (`runner.py:736-737`), and wraps each example in `isolated_z3_context()` (a fresh Z3
   C-level context swapped into `z3.z3._main_ctx`, `runner.py:739-745`), clearing the
   per-example solver backend override and caches afterwards (`runner.py:746-752`).
   `KeyboardInterrupt` finalizes partial saved output and exits 1 (`runner.py:754-760`).
10. **`process_example()`** (`runner.py:263-298`): suppresses logging to ERROR, resets Z3
    params (z3 backend only, `runner.py:300-324`), applies the theory's operator
    `dictionary` translation (`runner.py:326-348`; `builder/translation.py:13-38` — naive
    substring `str.replace` over premise/conclusion strings), reads
    `settings['iterate']` (default handling in `runner_utils.py:164`); `iterate == 1` →
    `_process_single_model()` (constructs `BuildExample`, prints via
    `BuildModule._capture_and_save_output`, `runner.py:362-384`); `iterate > 1` →
    `_process_with_iterations()` with a `UnifiedProgress` bar and generator- or list-based
    theory iteration (`runner.py:386-463`, `runner.py:547-597`). The theory's iterate
    function is discovered via the registry (`runner.py:844-892`), preferring
    `iterate_example_generator` over `iterate_example` (`runner.py:885-892`).
11. **`BuildExample`** (`builder/example.py:30`, internal-only since
    `builder/__init__.py:19-24` exports just `BuildModule` and `BuildProject`): `__init__`
    (`example.py:49-84`) configures the per-example solver backend from
    `settings['solver']` (`example.py:85-105`), validates and destructures the theory dict
    and example triple (`builder/validation.py`), builds per-theory merged settings via its
    own `SettingsManager` (`example.py:137-168`, comparison mode = more than one theory,
    `example.py:151`), then runs the pipeline: `Syntax(premises, conclusions, operators)` →
    `ModelConstraints(settings, syntax, semantics(settings), proposition)` →
    `model_structure_class(model_constraints, settings)` → `interpret()`
    (`example.py:170-197`). Solving happens inside model-structure construction.
12. **Output**: `BuildModule._capture_and_save_output()` (`module.py:191-224`) either
    prints directly (`example.print_model` → `model_structure.print_to`,
    `example.py:244-270`) or redirects `sys.stdout` into a `StringIO`, re-prints to
    console, converts ANSI→markdown, collects model data
    (`output.ModelDataCollector`), and hands `MarkdownFormatter` output to
    `OutputManager.save_example` (`module.py:226-342`). Batch outputs finalize into
    `EXAMPLES.md`/`MODELS.json` + `summary.json` in the output dir
    (`output/manager.py:189-262`). After all examples, a module- or theory-level
    `print_example_report()` hook is called if defined (`runner.py:781-819`).

Comparison mode (`--maximize`): `ModelComparison.run_comparison()`
(`builder/comparison.py:140-184`) prints per-example headers, then
`compare_semantics()` (`comparison.py:91-138`) serializes each theory
(classes → module/class-name strings, `builder/serialize.py:78-155`) and races them in a
`ProcessPoolExecutor`, each worker incrementing `N` until timeout
(`comparison.py:20-75`, `runner.py:49-116` `try_single_N_static`); result = max `N` per
theory, sorted descending, 300 s overall future timeout (`comparison.py:130`).

## 4. Example-File Format (the user's input language)

An examples file is an ordinary Python module, executed on load. The loader contract
(`module.py:98-102`) requires exactly two module-level names, with a third optional:

- **`semantic_theories`** (required): `Dict[str, TheoryDict]` mapping a display name (any
  string; shown in output headers, e.g. `"Brast-McKie"`, `"Primary"`) to a theory dict.
  Empty dict → `ImportError` at settings init (`module.py:113-114`).
- **`example_range`** (required): `Dict[str, ExampleCase]` mapping example names to example
  triples. This is what actually runs.
- **`general_settings`** (optional): `Dict[str, Any]` drawn from the general-settings
  vocabulary (Section 3 step 5). Unknown keys warn, never fail
  (`settings/settings.py:104-112`).

**TheoryDict shape**, enforced by `validate_semantic_theory()`
(`builder/validation.py:19-84`):

| Key | Required | Type constraint |
|---|---|---|
| `"semantics"` | yes | subclass of `SemanticDefaults` |
| `"proposition"` | yes | subclass of `PropositionDefaults` |
| `"operators"` | yes | instance of `OperatorCollection` |
| `"model"` | yes | subclass of `ModelDefaults` |
| `"dictionary"` | no | `Dict[str, str]` operator-rename map, applied by plain string replacement to every premise/conclusion before parsing (`builder/translation.py:29-38`) |

**ExampleCase shape**, enforced by `validate_example_case()`
(`builder/validation.py:86-130`): a list/tuple of exactly 3 elements
`[premises, conclusions, settings]` — premises: `List[str]` of LaTeX-style formulas
(`'A'`, `'(A \\rightarrow B)'`, `'\\neg A'`), conclusions: `List[str]`, settings:
`Dict[str, Any]`. Recognized example-settings keys come from each theory's
`DEFAULT_EXAMPLE_SETTINGS`; the conventional keys used throughout theory files are `N`
(state-space bit width), `contingent`, `non_null`, `non_empty`, `disjoint`, `max_time`
(seconds), `iterate` (number of distinct models to find), `expectation` (whether a
countermodel is expected — consumed by `ModelDefaults.check_result()`,
`models/structure.py:332-345`), plus theory-specific keys (`M` for bimodal times, etc.).

**Optional conventions** consumed elsewhere:
- `unit_tests`: `Dict[str, ExampleCase]` of ALL examples — the pytest-facing superset (see
  Section 9). `test_example_range` is a common alias (`theory_lib/logos/examples.py:135`).
- `print_example_report()`: zero-arg function called once after a run
  (`runner.py:781-819`).
- A `if __name__ == '__main__':` block that shells out to `model-checker` on itself, making
  the file directly runnable (`theory_lib/logos/subtheories/extensional/examples.py:394-397`).

**Verbatim real example** (abridged only in the middle of the repetitive example blocks;
from `code/src/model_checker/theory_lib/logos/subtheories/extensional/examples.py`):

```python
import os
import subprocess
import sys

from ...operators import LogosOperatorRegistry
from ...semantic import LogosSemantics, LogosProposition, LogosModelStructure

# EXT_CM_1: CONTRADICTION (A does not entail not-A)
EXT_CM_1_premises = ['A']
EXT_CM_1_conclusions = ['\\neg A']
EXT_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 2,
    'expectation': True,
}
EXT_CM_1_example = [
    EXT_CM_1_premises,
    EXT_CM_1_conclusions,
    EXT_CM_1_settings,
]

# EXT_TH_1: MODUS PONENS (Valid inference)
EXT_TH_1_premises = ['A', '(A \\rightarrow B)']
EXT_TH_1_conclusions = ['B']
EXT_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# ... (EXT_CM_2, EXT_TH_2 .. EXT_TH_12 follow the same pattern) ...

countermodel_examples = {
    "EXT_CM_1": EXT_CM_1_example,
    "EXT_CM_2": EXT_CM_2_example,
}
theorem_examples = {
    "EXT_TH_1": EXT_TH_1_example,
    # ...
    "EXT_TH_12": EXT_TH_12_example,
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# Default settings
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Create operator registry for extensional theory
extensional_registry = LogosOperatorRegistry()
extensional_registry.load_subtheories(['extensional'])

# Define the semantic theory
extensional_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": extensional_registry.get_operators(),
}

# Specify which theories to use
semantic_theories = {
    "Brast-McKie": extensional_theory,
}

# Specify which examples to run by default when running this module directly
example_range = {
    "EXT_CM_2": EXT_CM_2_example,  # AFFIRMING THE CONSEQUENT
    "EXT_TH_5": EXT_TH_5_example,  # DOUBLE NEGATION ELIMINATION
    # (other keys present but commented out — users toggle lines to select runs)
}

# Make this module runnable from the command line
if __name__ == '__main__':
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=parent_parent_dir)
```

Naming conventions visible across all theory example files: `PREFIX_CM_n` = countermodel
expected (`expectation: True`), `PREFIX_TH_n` = theorem expected (`expectation: False`);
per-example variables named `{NAME}_premises/_conclusions/_settings/_example`. These are
conventions only — nothing enforces them.

## 5. Project Generation (`BuildProject`)

`builder/project.py:85`. Constructor takes a theory name (default: first registered theory,
`project.py:116-124`) and resolves `source_dir` to
`src/model_checker/theory_lib/<theory>` (`project.py:127`), fail-fast if missing
(`project.py:133-136`).

`generate(name, destination_dir=None)` (`project.py:177-226`):
- Project directory = `{destination_dir or cwd}/project_{name}` (`project.py:196-202`);
  `FileExistsError` if present; cleanup via `shutil.rmtree` on any failure
  (`project.py:222-226`).
- **Copy manifest** (not a verbatim tree copy): `REQUIRED_COPY_ITEMS = ['__init__.py',
  'operators.py', 'examples.py', 'tests', 'docs', 'README.md', 'CITATION.md',
  'LICENSE.md']` (`project.py:43-52`); at least one of `SEMANTIC_ALTERNATIVES = ['semantic',
  'semantic.py']` (`project.py:55`); `OPTIONAL_COPY_ITEMS = ['VERSION', 'iterate.py',
  'notebooks', 'protocols.py', 'subtheories']` (`project.py:58-78` — `iterate.py` is
  optional only because bimodal lacks one, a tracked contract gap). Missing required items
  are a hard `FileNotFoundError` (`project.py:271-279`); non-manifest items are skipped with
  a warning (`project.py:284-287`); `__pycache__`/`.ipynb_checkpoints`/`*.pyc` always
  excluded (`project.py:82`, `project.py:254-257`).
- **Marker**: writes `.modelchecker` containing `theory=`, `package=true`, `version=1.0`,
  `created=<ISO>`, `model_checker_version=` (`project.py:317-339`). This marker is what
  later triggers `PackageImportStrategy` when running the generated project's files
  (`builder/detector.py:52-65`).
- Ensures `__init__.py` exists at root and in every subdir containing `.py` files
  (`project.py:341-398`).
- **Substitution**: rewrites `__version__` (→ `"0.1.0"`) and `__model_checker_version__`
  (→ current package version) in the copied `__init__.py` via regex (`project.py:400-499`);
  creates `LICENSE.md` (GPL-3.0 template with inheritance from source theory's copyright)
  and a boilerplate `CITATION.md` if absent (`project.py:501-616`).

## 6. Interactive/UI Affordances (terminal)

All prompting uses bare `input()`:
- `BuildProject.ask_generate()`: `"Would you like to generate a new {theory}-project?
  (y/n)"` then `"Enter the name of your project using snake_case:"`
  (`project.py:152-175`).
- `BuildProject._handle_example_script()`: `"Would you like to test an example in your
  project? (y/n)"`; if yes, runs `model-checker examples.py` as a subprocess with a 30 s
  timeout and PYTHONPATH pointing at the project's parent (`project.py:700-772`).
- `ModelRunner.prompt_for_iterations()`: `"Enter a number to iterate or hit return to
  continue:"` with recursive re-prompt on bad input (`runner.py:821-842`) — reachable only
  when `build_module.prompt_manager` is non-None (`runner.py:526-537`), which is currently
  never (`module.py:144`), so this path is dead in practice.
- Progress display: `Spinner` during single checks (`runner.py:161-169`),
  `UnifiedProgress` animated bars during iteration with a deliberate
  "bar → output → bar" deferred-completion ordering protocol
  (`runner.py:386-463`, docstring at `runner.py:394-402`).

## 7. Jupyter Integration

`code/src/model_checker/jupyter/` is a two-tier package (`jupyter/__init__.py`):
- **Always available** (no optional deps): `unicode_to_latex`/`latex_to_unicode`
  (`unicode.py:33-160` — regex/character-map conversion between `□,◇,¬,∧,→,↔,▷` and
  `\\Box`, `\\rightarrow`, etc.), `setup_environment`/`get_available_theories`
  (`environment.py`), `load_examples` (`utils.py:15`), `create_build_example`/
  `build_and_check` (`builder_utils.py`), and an exception hierarchy (`exceptions.py`).
- **Dependency-gated**: `has_jupyter_dependencies()` probes for
  `ipywidgets`, `matplotlib`, `networkx` via `find_spec` (`__init__.py:57-64`). If absent,
  the module exports stub functions that raise `JupyterDependencyError` on call
  (`__init__.py:66-92`); if present, real implementations are swapped in
  (`__init__.py:107-113`). Extras: `pip install model-checker[jupyter]`
  (`pyproject.toml:36-43`: ipywidgets>=7.0.0, matplotlib>=3.0.0, networkx>=2.0, jupyter,
  ipython).

High-level API (`interactive.py`):
- `check_formula(formula, theory_name=None, premises=None, settings=None)`
  (`interactive.py:46-98`): resolves theory via registry (default theory = `logos`,
  `interactive.py:23-43`, `theory_lib/__init__.py:488-489`), builds
  `[premises, [formula], settings]` (defaults `{'N': 3, 'max_time': 5}`), runs it through
  `create_build_example`, renders green "Valid"/red "Invalid" HTML.
- `find_countermodel(...)` (`interactive.py:99-180`): same, forcing
  `settings['expectation'] = False`, and embedding captured model output in a
  `<details>` block.
- `ModelExplorer` (`interactive.py:208`): full ipywidgets UI — formula text box, premises
  textarea, theory dropdown, settings accordion (per-theory: N slider, max_time, checkbox
  toggles — `ui_builders.py:130-236`), check button, "Find Next Model" button, and a
  text/graph visualization radio selector; graph view renders the model as a networkx
  digraph via matplotlib with theory-specific `TheoryAdapter`s
  (`display.py:117-247`, `adapters.py:16-407` — one adapter per theory, attached to
  registry entries, `adapters.py:109-134`).
- `FormulaChecker` (`interactive.py:529`): simplified check-only widget.

Bridging to the build layer: `create_build_example` fabricates a `MinimalBuildModule` mock
(name, `general_settings` merged with the example's settings dict, single-entry
`semantic_theories`, ad-hoc flags object) and constructs a real `BuildExample` directly
(`builder_utils.py:10-73`) — i.e., the notebook path bypasses `BuildModule`, `ModuleLoader`,
and `OutputManager` entirely. Environment repair for source checkouts (path guessing,
`importlib.reload`) lives in `environment.py:15-110`; note it contains hard-coded personal
fallback paths (`~/Documents/Philosophy/Projects/ModelChecker/Code`,
`environment.py:42-46`). Two demo notebooks ship in `jupyter/notebooks/`
(`basic_demo.ipynb`, `options_demo.ipynb`); a `debug/` subpackage holds troubleshooting
scripts and docs.

**Defect (verified against source, worth knowing for any port)**:
`BuildExample.check_result()` compares `z3_model_status` against `settings.get("model",
True)` (`builder/example.py:336-344`) — a stale settings key; the rest of the system uses
`"expectation"` (`models/structure.py:332-345`, every theory example file). Since no caller
supplies a `"model"` key, `check_result()` degenerates to "was a Z3 model found". In
`check_formula` (`interactive.py:74-89`), `valid = model.check_result()` therefore reports
"Valid" precisely when a **countermodel exists**, and `find_countermodel`'s branch logic
(`interactive.py:134-137`) is likewise inverted: its forced `expectation: False` is never
read by `check_result()`. The CLI path is unaffected (it uses
`ModelDefaults.check_result()`, the `"expectation"`-based one, via pytest and printing).

## 8. Packaging / Distribution

- **Build system**: setuptools (`pyproject.toml:1-3`), `package-dir = {"" = "src"}`
  (`pyproject.toml:69-74`), built with `python -m build`. Version `1.3.3` declared once at
  `pyproject.toml:11`; `model_checker.__version__` reads it back from installed metadata
  (`model_checker/__init__.py:22-24` via `get_model_checker_version()`), and the release
  workflow asserts tag == pyproject version (`pyproject.toml:6-10` comment).
- **Runtime deps** (`pyproject.toml:29-32`): `z3-solver>=4.8.0`, `networkx>=2.0`. Python
  `>=3.10` (`pyproject.toml:33`). Extras: `jupyter`/`all` (widget stack), `dev`
  (pytest-xdist, pytest-timeout) (`pyproject.toml:35-52`). Known undeclared dependency:
  `typing_extensions` imported by `theory_lib/logos/protocols.py` (documented in
  `flake.nix:~100`).
- **Console script**: `model-checker` (`pyproject.toml:65-66`).
- **Wheel contents**: all packages under `src` plus a package-data allowlist —
  `README.md`, `CITATION.md`, `LICENSE.md`, `docs/*.md`, `notebooks/*.ipynb` per package
  (`pyproject.toml:76-88`); explicitly NOT a blanket `*.md` glob. The sdist mirrors this via
  `code/MANIFEST.in`, which additionally `prune`s `theory_lib/*/history`,
  `theory_lib/*/reports`, `theory_lib/*/examples_refactored` and `global-exclude`s
  `TODO.md`, `__pycache__`, `*.pyc` (`MANIFEST.in:34-41`). The `oracle/` differential-oracle
  tree lives at the repo root, outside `code/`, and is therefore not in the wheel at all
  (top-level `CLAUDE.md` project-structure note).
- **Packaging tests**: `code/tests/packaging/` builds real wheels/sdists and asserts
  inclusions, exclusions, wheel/sdist parity, entry-point presence, console-script
  execution, and generate-then-execute round trips (`test_inclusions.py`,
  `test_exclusions.py`, `test_parity.py`, `test_entry_point.py`,
  `test_cli_console_script.py`, `test_generate_then_execute.py`), all marked
  `packaging`+`slow`.
- **Nix flake** (`/flake.nix`): `packages.default` = the wheel built with
  `buildPythonPackage` on Python 3.12, version derived by parsing `code/pyproject.toml`
  (`flake.nix:15-21`); uses the nixpkgs-native Z3 bindings and strips the `z3-solver`
  metadata requirement (`pythonRemoveDeps`, `flake.nix:39-49`). `devShells.default`
  exposes a python-with-packages environment (z3, pytest(+xdist,+timeout), ipywidgets,
  matplotlib, typing-extensions) and a shellHook that puts `code/src` (plus an optional
  sibling `BimodalHarness/src`) on `PYTHONPATH` (`flake.nix:110-126`). `checks.default`
  runs the full suite `pytest src/model_checker tests -m "not packaging and not
  performance and not unstable" -n 6` inside the sandbox (`flake.nix:150-176`).

## 9. Testing Surface (examples as tests)

- Convention: each theory's `examples.py` exports `unit_tests` (all examples) and often the
  alias `test_example_range`; theory unit tests parametrize over it:
  `@pytest.mark.parametrize("example_name,example_case", test_example_range.items())`
  (`theory_lib/imposition/tests/unit/test_imposition.py:35-47`).
- The harness is `model_checker.utils.run_test()` (`utils/testing.py:12-55`): rebuilds the
  same pipeline as `BuildExample` (Syntax → semantics(settings) → ModelConstraints →
  model_structure) without any builder involvement, and returns
  `model_structure.check_result()` — i.e. `z3_model_status == settings["expectation"]`
  (`models/structure.py:332-345`). So `expectation: True` examples pass iff a countermodel
  is found, `expectation: False` iff none is. A richer variant `run_enhanced_test`
  returning `TestResultData` (premise/conclusion evaluations, timing, witnesses) also
  exists (`utils/testing.py:58+`).
- Repo-level pytest config: `pythonpath = "src"`, `testpaths = ["tests",
  "src/model_checker"]`, `--import-mode=importlib`, and registered markers
  `countermodel/theorem/performance/differential/slow/packaging/unstable`
  (`pyproject.toml:90-103`).
- CLI contract tests live in `code/tests/cli/`: `test_parse_file_flags.py` (parser
  behavior), `test_flag_matrix.py`, `test_docs_flag_matrix.py` (see Section 10),
  `test_cli_mode.py` + `test_installed_mode_guard.py` (source vs installed-wheel
  invocation modes).

## 10. Doc/Source Divergences

The repo actively guards against stale documented flags:
`code/tests/cli/test_docs_flag_matrix.py` scans every fenced shell block in the docs for
`model-checker`/`dev_cli.py`/`python -m model_checker` invocation lines and asserts every
flag token is registered on the real parser (derived from `parser._actions`, never
hand-listed) or in the dev_cli wrapper set (`test_docs_flag_matrix.py:34-58`). Its declared
blind spots (docstring, lines 12-18): prose mentions, ASCII diagrams, and — critically —
*flags that exist but don't work*. Divergences found:

1. **`--sequential`/`-q` is documented as working but is nonfunctional.**
   `docs/usage/OUTPUT.md:145-180` documents a full "Interactive Save Mode" workflow
   (`model-checker --save --sequential ...`, mode-selection prompts, per-model save
   prompts, directory-change prompt). In source, the flag parses
   (`__main__.py:130-135`) but `BuildModule._initialize_output_management` raises
   `NotImplementedError` whenever it is set: `SequentialSaveManager`/
   `ConsoleInputProvider` were deliberately deleted and are "not being restored"
   (`builder/module.py:139-152`). The flag-matrix guard cannot catch this class of rot
   (flag exists, behavior doesn't).
2. **Dead interactive-mode remnants in source**: `module.py:73-76` checks
   `module_flags.interactive`, but no `--interactive` flag exists in the parser; the
   settings layer still exempts `'interactive'`, `'output_mode'`, `'sequential_files'`
   as "standard args" (`settings/settings.py:252-254`) though none is a current flag.
   `runner.py`'s whole interactive branch (`prompt_manager` truthy: `runner.py:526-537`,
   `runner.py:775-776`, `module.py:329-339`) is unreachable since `prompt_manager` is
   hard-set to `None` (`module.py:144`).
3. **`__main__.py` module docstring is stale**: says "run: `python -m src.model_checker`"
   (`__main__.py:4`) — the actual working invocations are `python -m model_checker` (with
   `code/src` on `sys.path`) or the console script.
4. **`BuildProject` internal inconsistencies**: `_add_license_file` references
   `self.source_theory` which is never assigned (attribute is `self.theory`,
   `project.py:524`, `project.py:538` vs `project.py:125`) — the resulting
   `AttributeError` is swallowed by the enclosing `except` and logged as a warning, so
   license inheritance from the source theory silently never happens.
   `generate()` is annotated `-> None` but returns the project path
   (`project.py:177`, `project.py:220`); `_extract_source_theory_info` is annotated
   `-> Tuple[str, str, str]` but returns a dict (`project.py:544-580`).
5. **`check_formula`/`find_countermodel` validity reporting is inverted** relative to what
   `jupyter/__init__.py:8-10`'s docstring and the demo notebooks imply, due to the stale
   `"model"` settings key in `BuildExample.check_result` (details and citations in
   Section 7).
6. **Epilog example ordering quirk**: `model-checker --save markdown` appears in the help
   epilog without a file path (`__main__.py:54`), which parses (positional is optional)
   but then crashes downstream since `BuildModule` requires `file_path`
   (`module.py:60-61` — `os.path.basename(None)` raises TypeError). Minor, but it is the
   tool's own help text.

## 11. Improvement Opportunities

Concrete, citable weaknesses an engineer re-deriving this system should not replicate:

1. **Configuration by arbitrary code execution.** The input format is an executed Python
   module (`strategies.py:216`, `strategies.py:122`), giving users full expressiveness but
   making the "format" unspecifiable: any module attribute may exist, side effects run at
   load time (example files even shell out to the CLI from `__main__` guards and mutate
   `sys.path` at import, `extensional/examples.py:40-46`), and validation happens
   piecemeal at runtime (`validation.py`). A declarative core (the
   `[premises, conclusions, settings]` triples plus theory references by name) with an
   escape hatch would be strictly easier to port, verify, and sandbox.
2. **Permanent global mutation during loading.** All three import strategies insert into
   `sys.path` permanently and register under bare names in `sys.modules`
   (`strategies.py:75-82`, `strategies.py:190-193`, `importer.py:57`), risking shadowing
   (`loader.py`'s own class docstring admits "changes are permanent",
   `loader.py:23-27`).
3. **Print-based output, stdout capture as an architecture.** Results are produced by
   `print_to(...)` writing ANSI-colored text; saving works by temporarily swapping
   `sys.stdout` and re-printing (`module.py:246-259`), then regex-converting ANSI to
   markdown. There is no structured result object flowing from solve to display —
   `get_result()` exists (`example.py:199-220`) but the display path bypasses it. The
   deferred-completion progress-bar choreography (`runner.py:394-402`, 599-676) exists
   solely to interleave prints correctly. A port should make "model → typed result →
   renderer" the only path.
4. **Circular parent references / God-object coupling.** `ModelRunner`, `ModelComparison`,
   and `BuildExample` all hold `build_module` back-references and reach through it
   (`runner.py:129`, `example.py:163`, `runner.py:383` calling the *private*
   `build_module._capture_and_save_output`). The jupyter layer must fabricate
   `MinimalBuildModule` mocks to reuse `BuildExample` (`builder_utils.py:35-70`), and
   comparison workers fabricate another mock (`comparison.py:43-53`) — evidence the real
   dependency is a small settings/output interface, not the whole module object.
5. **Fragile flag-provenance detection.** Deciding whether a CLI flag was "really given" by
   re-scanning raw argv (`settings/settings.py:202-240`) breaks for clustered short flags
   (documented at `settings/settings.py:213-220`) and requires the parallel
   hand-maintained `_short_to_long` map (`__main__.py:208-223`). Argparse
   `default=SUPPRESS` or a tri-state Optional design eliminates the whole mechanism.
6. **Operator translation by naive string replacement** (`translation.py:29-38`):
   `sentence.replace(old, new)` over raw formula strings, no tokenization — an operator
   name that is a substring of another (or of a proposition letter sequence) would corrupt
   formulas silently. Translation belongs after parsing, on the AST.
7. **Duplicated pipeline assembly.** The Syntax→ModelConstraints→structure sequence is
   built independently in `BuildExample._build_model_structure` (`example.py:170-197`),
   `ModelRunner.try_single_N` (`runner.py:192-207`), `try_single_N_static`
   (`runner.py:74-88`), `utils.run_test` (`utils/testing.py:41-55`), and again in
   `iterate/core.py` (acknowledged at `example.py:184-186`). One constructor function
   should own it.
8. **Dead and inverted code left in place**: the unreachable interactive/sequential branch
   set (Section 10 items 1-2), the inverted `check_result` key (Section 7), the
   `self.source_theory` AttributeError swallowed per-run (Section 10 item 4). Each
   survives because errors are caught broadly and logged (`project.py:541-542`) or the
   code path is never exercised by tests.
9. **Prompts and subprocesses inside library code.** `BuildProject.ask_generate` /
   `_handle_example_script` mix `input()`, `print()`, `subprocess.run(["model-checker",
   ...])` and `sys.path` mutation in one class (`project.py:152-175`, `700-772`),
   making project generation untestable without pty simulation and unusable
   programmatically; version substitution into `__init__.py` is done by regex over source
   text (`project.py:432-499`).
10. **Env-dependent settings behavior**: `MODELCHECKER_VERBOSE` and
    `MODELCHECKER_SUPPRESS_COMPARISON_WARNINGS` env vars silently alter warning behavior
    (`settings/settings.py:30-34`); warnings themselves go to stdout via `print`
    (`settings/settings.py:275`), and `BuildModule` suppresses them during init by
    stdout redirection (`module.py:117-121`) — three layers of workaround for the absence
    of a real diagnostics channel.
11. **Positive notes worth preserving in any port**: per-example C-level solver-context
    isolation (`runner.py:739-752`); registry-driven theory discovery that keeps core free
    of theory-name literals (`loader.py:83-102`, `project.py:116-124`); the
    manifest-based scaffolding allowlist mirrored across `project.py`, `MANIFEST.in`, and
    package-data (`project.py:25-42`, `MANIFEST.in:8-13`); the parser-derived doc-flag
    regression guard (`test_docs_flag_matrix.py`); and the settings priority model
    (defaults < general < example < explicit CLI flags) which is a sound design even if
    its provenance detection is fragile.
