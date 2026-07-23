# Teammate C (Critic) Findings — Task 117 Research

## Key Findings

### 1. CRITICAL — the CLI is not merely "possibly broken", it is currently broken by a verified `ModuleNotFoundError`, and this breaks the literal command CLAUDE.md tells contributors to run

Running the exact commands documented as the project's "Essential Commands" fails:

```
$ PYTHONPATH=code/src python3 -m model_checker --help
ModuleNotFoundError: No module named 'model_checker.builder'

$ python3 code/dev_cli.py --help
Error importing from local source: No module named 'model_checker.builder'

$ PYTHONPATH=code/src pytest code/tests/ -v   # <- the command literally in CLAUDE.md
ERROR code/tests/e2e/test_simple_output_verify.py — No module named 'model_checker.output.manager'
ERROR code/tests/integration/test_model_building_sync.py — No module named 'model_checker.builder'
Interrupted: 2 errors during collection
```

Root cause, found via `git log`: an earlier task ("104: Dead-code cleanup and thin CLI",
completed 2026-06-01, commit chain ending `013a486c task 104 phase 1: remove builder directory
and fix __init__.py`) **deleted `code/src/model_checker/builder/` entirely** (67 files) along
with large parts of `output/` (`output/manager.py`, `output/progress/`, etc.), on the premise
that the project had been narrowed to a bimodal-only oracle package (see Finding 2). That task's
own summary states explicitly: *"No stale imports to deleted modules (except `__main__.py`
builder import, expected)"* — i.e., the breakage was known and accepted **at the time**, on the
assumption `model_checker.__main__` was dead code.

That assumption is no longer true. Multiple tasks after 104 (12, 16, 18, 19, 21, 32, 34, 42, and
now 116/e9734a27) reintroduced and actively maintained `theory_lib/logos` — a full multi-theory
system with subtheories, notebooks, and its own `comparison.py` that still does
`from model_checker.builder import ...`. Nobody reconciled the two facts: **logos came back, but
`builder` did not.** The result is that both the packaged CLI entry point (`model-checker` via
`__main__.py`) and the dev entry point (`dev_cli.py`) have been non-functional for some
number of commits, and neither Teammate A nor B (as far as I can tell without seeing their
in-flight output) may have caught this if they only ran the narrower `pytest` default
(`testpaths = ["src/model_checker/theory_lib/bimodal/tests"]` in `code/pyproject.toml` — see
Finding 2) rather than the full `code/tests/` suite CLAUDE.md documents.

**This should be the #1 fix-before-anything-else item.** There is no point auditing PyPI parity
or building a Nix flake to test a CLI that cannot currently import.

### 2. CRITICAL — the package identity in `code/pyproject.toml` does not match the PyPI package the user wants to release, and the repo has been oscillating between two different products

`code/pyproject.toml` currently declares:
```toml
[project]
name = "bimodal-logic"
version = "0.1.0"
description = "Z3-based bimodal logic oracle: temporal and modal reasoning for the bimodal_harness."
dependencies = ["z3-solver>=4.8.0"]
[tool.pytest.ini_options]
testpaths = ["src/model_checker/theory_lib/bimodal/tests"]
```

The actual PyPI `model-checker` project (queried live) is at **version 1.2.12**, described as
*"A hyperintensional theorem prover for developing and exploring programmatic semantic
theories,"* and lists `requires_dist` including `networkx>=2.0` (core) plus `ipywidgets`,
`matplotlib`, `jupyter`, `ipython` under `jupyter`/`all` extras.

This is not a small drift — it's evidence of **two incompatible project identities layered in
one repo**:
- Task 100 ("Strip Non-Bimodal Code", completed 2026-06-01) deleted `theory_lib/logos`,
  `iterate/`, `jupyter/`, `output/notebook/`, dropped `networkx` and the jupyter/cvc5 extras from
  `pyproject.toml`, and rewrote `AVAILABLE_THEORIES` to `['bimodal']` — explicitly converting the
  project into a bimodal-only oracle.
- Task 104 (above) then renamed the package itself to `bimodal-logic` 0.1.0 and added a second,
  parallel `src/bimodal_logic/` package with its own CLI (`bimodal-logic check`) and its own
  entry point in `pyproject.toml`.
- Later tasks (12+) reintroduced `theory_lib/logos` and multi-theory behavior into
  `model_checker`, but **nobody reverted the package name, version, or dependency list** back
  toward what PyPI's `model-checker` project actually needs.

Consequences for the release task as scoped:
- If someone runs `python -m build` on `code/pyproject.toml` today, the built artifact is named
  **`bimodal_logic-0.1.0`**, not `model_checker`. Uploading it would not update the existing
  `model-checker` PyPI project at all — it would either fail (name mismatch with existing
  project ownership) or create a new, wrong project.
- `README.md` at repo root still instructs `pip install model-checker[jupyter]` and links to
  `code/src/model_checker/jupyter/README.md` — a directory that **does not exist** (deleted in
  task 100, never restored). This is a dead link in the exact quick-start a new user hits first.
- `code/README.md` also documents `cd ModelChecker/Code` (capital `Code`) even though the
  directory has been lowercase `code/` since an earlier renaming task — a smaller but real doc
  drift a fresh PyPI release should fix.
- `model_checker.utils.get_model_checker_version()` currently returns `"0.0.0-dev"` locally,
  vs. PyPI's `1.2.12` — versioning strategy (semver bump, changelog entry, "what's actually
  new since 1.2.12") is entirely unaddressed by the task description and by (as far as I can
  tell) the other two researchers' framing.

Any research report for this task needs a section titled something like "Reconcile package
identity" that decides, explicitly: is this release a continuation of the `model-checker`
1.2.x line (multi-theory, networkx/jupyter deps, restore `builder`), a fork under the new
`bimodal-logic` name, or a dual-package repo publishing both under separate names? The task
description ("audit discrepancies with the model-checker package on PyPI... prepare a
top-quality release to push to PyPI") implicitly assumes the first, but the codebase's actual
trajectory over the last ~15 tasks points toward the second/third. This needs to be a decision
point surfaced to the user, not silently assumed by whichever researcher writes the plan.

### 3. Testing scope is misleadingly narrow

Because `[tool.pytest.ini_options] testpaths` was pinned to
`["src/model_checker/theory_lib/bimodal/tests"]` during the bimodal-only phase, a bare `pytest`
invocation from `code/` silently ignores `code/tests/` (unit/integration/e2e suites for the
non-bimodal parts of `model_checker`) and all of `theory_lib/logos/tests/`. Task 104's own
"624 bimodal tests pass" verification is therefore not evidence the broader CLI/builder/output
breakage was absent — it structurally could not detect it. Any "complete full testing" work item
for task 117 must explicitly widen `testpaths` (or stop relying on bare `pytest` and always use
`PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -v` as CLAUDE.md prescribes)
before claiming a clean baseline.

### 4. First-order removal (e9734a27) looks self-contained, but I did not find independent doc drift beyond one file

Direct grep for `first_order`/`first-order` inside `code/` and `docs/` outside of `specs/archive`
turns up only `docs/usage/SEMANTICS.md`. Whoever is validating that specific commit should check
whether `docs/usage/SEMANTICS.md`'s references describe first-order logic as a still-available
feature (stale) or discuss it historically/comparatively (fine). I did not have time to render
that file's context in detail — flagging as a specific, bounded follow-up rather than a vague
"check docs."  `docs/theory/QUANTIFIER_SOLVERS.md` was deleted by the same commit; confirm
nothing outside `specs/archive/**` still links to it (my grep found only
`specs/archive/state.json` and `code/scripts/README.md` — the latter is **not** an archive path
and should be checked/fixed).

## Recommended Approach

1. **Stop and ask the user the package-identity question in Finding 2 before writing an
   implementation plan.** This single decision (restore `model_checker` as the release target
   vs. formalize `bimodal-logic` as a separate/replacement package) determines almost everything
   else: which CLI to fix, which dependencies belong in `pyproject.toml`, what the PyPI parity
   diff even means, and what a Nix flake needs to provide.
2. Treat "the CLI is currently broken" as a P0 finding independent of that decision — even the
   `bimodal-logic check` CLI path should be smoke-tested directly (I did not verify it in this
   pass; Teammate A/B should confirm `bimodal-logic --help` / `bimodal-logic check` actually
   work, since it's the only entry point not proven broken here).
3. Widen the test baseline (`testpaths`) before any "full testing" claim is made in the plan.
4. Add an explicit versioning/changelog work item — do not let the plan implicitly assume "just
   bump version and upload"; PyPI uploads are irreversible per version (a filename, once
   uploaded, can never be reused even after deletion), so get the package name + version +
   dependency list right *before* the first upload attempt, ideally rehearsed against TestPyPI
   first.

## Evidence/Examples

- `git show --stat e9734a27` — first-order removal commit, 27 files changed, clean.
- `git log --oneline --all -- code/src/model_checker/theory_lib/logos` — shows logos
  reintroduced by tasks 12, 16, 18, 19, 21, 32, 34, 42 *after* task 100 deleted it and *after*
  task 104 deleted `builder/`.
- `specs/archive/100_strip_non_bimodal_code/summaries/02_strip-non-bimodal-summary.md` —
  documents the bimodal-only conversion.
- `specs/archive/104_programmatic_api_cleanup/summaries/01_dead-code-cleanup-summary.md` —
  documents `builder/` deletion and the renamed `bimodal-logic` package, with the line "except
  `__main__.py` builder import, expected."
- Live commands run in this session, all reproducible:
  - `PYTHONPATH=code/src python3 -m model_checker --help` → `ModuleNotFoundError: No module
    named 'model_checker.builder'`
  - `python3 code/dev_cli.py --help` → same error
  - `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` → 2 collection errors,
    `model_checker.builder` and `model_checker.output.manager` missing
  - `curl -s https://pypi.org/pypi/model-checker/json` → version `1.2.12`, deps include
    `networkx`, `jupyter`, `ipywidgets`, `matplotlib` — none present in current
    `code/pyproject.toml`
  - `cat code/pyproject.toml` → `name = "bimodal-logic"`, `version = "0.1.0"`,
    `testpaths = ["src/model_checker/theory_lib/bimodal/tests"]`

## Confidence Level

**High** on all four findings — each is backed by a directly reproduced command output or a
direct file read, not inference. The one explicitly lower-confidence item is Finding 4's claim
about `docs/usage/SEMANTICS.md` content (I confirmed the file references first-order logic but
did not fully read it to judge staleness — flagged as bounded follow-up, not asserted as broken).
