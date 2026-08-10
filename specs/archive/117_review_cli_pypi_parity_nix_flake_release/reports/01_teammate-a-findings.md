# Task 117 Research: CLI/PyPI Parity, Nix Flake, Release Readiness — Teammate A Findings

## Key Findings

### 1. The repo has already pivoted away from being "model-checker" — this is the central fact for scoping task 117

Two prior tasks (archived: `100_strip_non_bimodal_code`, `104_programmatic_api_cleanup`)
deliberately and successfully converted this repository from a general multi-theory
model-checking CLI/PyPI package into a narrow **bimodal-only Z3 oracle backend** for a sibling
project called `BimodalHarness`:

- `code/pyproject.toml` project identity is now `name = "bimodal-logic"`, `version = "0.1.0"`
  (not `model-checker`).
- `theory_lib.AVAILABLE_THEORIES` was reduced to `['bimodal']` only (task 100 deleted
  `logos/`, `exclusion`'s and `imposition`'s infra, `iterate/`, `jupyter/`, `output/notebook/`).
- Task 104 deleted `model_checker/builder/` entirely (67 files) and added a new, working, thin
  CLI: `bimodal-logic check`, backed by `src/bimodal_logic/cli.py` + `Z3OracleProvider`. This new
  CLI **works** (verified below).
- `pyproject.toml` still declares `model-checker = "model_checker.__main__:run"` as a script
  entry point, but `model_checker/__main__.py` still imports `from model_checker.builder import
  (...)` — a module that no longer exists. **This is documented as an accepted/expected outcome
  in the task 104 summary** ("No stale imports to deleted modules (except `__main__.py` builder
  import, expected)"), i.e. the maintainers knowingly left the old CLI entry point broken.

**Implication**: "verify the CLI works" and "audit PyPI parity for `model-checker`" are not one
question. The historic `model-checker` CLI is intentionally dead. The live, working artifact is
`bimodal-logic`, which has never been published anywhere and bears no relationship (name,
scope, dependencies) to what's currently on PyPI as `model-checker`. Before any Nix/PyPI work,
this needs an explicit scope decision from the user: (a) restore/rebuild general-purpose
`model-checker` to match its historic PyPI package, or (b) publish the new, narrower
`bimodal-logic` package (and retire the `model-checker` name/entry point), or (c) something else
entirely. The two are not reconcilable by a version bump.

### 2. Confirmed: the `model-checker` CLI entry point is broken; the new `bimodal-logic` CLI works

```
$ cd code && PYTHONPATH=src python3 dev_cli.py --help
Error importing from local source: No module named 'model_checker.builder'
```

```
$ cd code && PYTHONPATH=src python3 -c "from bimodal_logic.cli import run; run()" --help
usage: bimodal-logic [-h] {check} ...
Z3-based bimodal logic countermodel checker
```

### 3. Confusing git history: a resurrected, half-dead `theory_lib/logos/` directory sits in the current tree

After task 100 deleted `theory_lib/logos/` (June), commit `feff3cbe` ("removed claude", July 18)
— whose stated purpose was to strip `.claude/` config — also **reintroduced ~24,000 lines / 504
files** including the entire `theory_lib/logos/` directory, apparently as an unintended
side-effect (net diff for that commit: `504 files changed, 24043 insertions(+), 107931
deletions(-)`). The most recent commit on the branch (`e9734a27`) further edited this resurrected
`logos/` directory ("Remove first-order subtheory and its infrastructure from logos"), i.e. work
is actively continuing on a directory that:

- Is **not registered** in `AVAILABLE_THEORIES = ['bimodal']` (so it is unreachable through the
  public API), and
- Is **internally broken**: `theory_lib/logos/__init__.py` imports `from .iterate import ...`,
  which imports `from model_checker.iterate.core import BaseModelIterator` — `model_checker.iterate`
  was deleted by task 100 and does not exist. Collecting its test suite fails immediately:
  ```
  ModuleNotFoundError: No module named 'model_checker.iterate'
  ```

This is dead, broken, unregistered code sitting in the package tree. `MANIFEST.in` still does
`recursive-include src *.py`, so a built sdist/wheel would currently bundle this broken directory
verbatim. It should either be finished-deleting (per task 100's original intent) or consciously
restored and repaired — its current half-state serves no one and will confuse anyone browsing
`theory_lib/`.

### 4. The canonical test command from CLAUDE.md does not work

CLAUDE.md documents `PYTHONPATH=code/src pytest code/tests/ -v` as the standard test command.
Running it produces 2 collection errors:
```
ERROR tests/e2e/test_simple_output_verify.py — ModuleNotFoundError: model_checker.output.manager
ERROR tests/integration/test_model_building_sync.py — ModuleNotFoundError: model_checker.builder
```
(`tests/integration/test_system_imports.py` and `tests/utils/helpers.py` also reference
`model_checker.builder` and would likely fail similarly if exercised.) These are stale
top-level test files left over from before the builder/output stripping.

### 5. The one live, current test suite (bimodal) mostly passes but is slow and has real failures

`src/model_checker/theory_lib/bimodal/tests/` is the one test tree that's actually current.
Task 104's own summary reports a clean baseline (624/627 passing, 2 pre-existing flaky `BM_CM_1`
timeouts) as of its completion. Re-running it now:

- It is **very slow** under Z3 — a partial run (`-m "not slow"`, 815 selected tests) reached
  only ~65% after 580 CPU-seconds; extrapolated full runtime is in the 15-20+ minute range on
  this machine. Budget for this explicitly in any release checklist; consider `pytest-xdist`
  for parallelization.
- `unit/test_cross_oracle_differential.py` (Task 109's cross-oracle differential harness,
  comparing the MC oracle against BimodalHarness baselines) shows **at least 2-4 real failures**
  (`F` markers at test indices ~21 and ~34 of 54, consistently reproduced across two independent
  partial runs) that were not fully diagnosed within this research session's time budget — full
  tracebacks require several more minutes of Z3 solving per test and the file did not finish
  even a solo 280s run. This should be investigated before claiming "full testing complete" —
  it's plausibly a regression from the recent logos/first-order work on `master`, or an
  environment-dependent skip/xfail that isn't behaving as such. Flagging as unresolved, not
  as "broken."

### 6. PyPI parity audit: `model-checker` on PyPI is a materially different package than anything currently buildable here

Fetched `https://pypi.org/pypi/model-checker/json`:
- Latest published version: **1.2.12**, `requires_python >= 3.8`.
- Dependencies: `z3-solver>=4.8.0`, **`networkx>=2.0`**, plus `jupyter`/`all` extras
  (`ipywidgets`, `matplotlib`, `networkx`, `jupyter`, `ipython`).
- Local `code/pyproject.toml` (as `bimodal-logic` 0.1.0): only `z3-solver>=4.8.0`, no
  `networkx`, no optional-dependency groups at all (removed in task 100 phase 6).
- `networkx` and `jupyter` are both still referenced inside `model_checker/__main__.py` (the
  broken CLI) but are absent from the dependency list — another sign `__main__.py` is dead code
  nobody has run.
- Description/homepage on PyPI still point at this GitHub repo
  (`https://github.com/benbrastmckie/ModelChecker`), so anyone `pip install model-checker`-ing
  today gets a 1.2.12 snapshot that predates the bimodal-only pivot — current `master` cannot
  build a compatible successor to that package without restoring the deleted general-theory
  infrastructure.

### 7. Documentation (README.md, CLAUDE.md, MANIFEST.in) is stale relative to the actual architecture

`code/README.md` still advertises "Modular Theory Architecture", `pip install model-checker`,
`run_tests.py logos modal`, `./dev_cli.py examples/my_example.py`, and a `builder`/`iterate`
component table — none of which reflects the current bimodal-only + `bimodal_logic` oracle
structure. `MANIFEST.in` still has `recursive-include` lines for
`theory_lib/logos README.md`, `theory_lib/exclusion README.md`, `theory_lib/imposition
README.md`, and the entire `jupyter/` doc tree, several of which point at directories that no
longer exist as registered theories.

### 8. Nix: a flake.nix already exists, but it's scoped to BimodalHarness dev integration, not release testing

- Root `/flake.nix` exists (description: "ModelChecker — Z3-based bimodal logic oracle"). It
  provides only a `devShells.x86_64-linux.default` (hardcoded system, no `x86_64-darwin`/
  `aarch64-*`), using `python312` + `z3-solver` + `pytest`/`pytest-cov` — **no `networkx`**
  (matches the trimmed local pyproject, but diverges from the real PyPI `model-checker`
  package). Its `shellHook` assumes a **sibling checkout** `../BimodalHarness/src`
  (overridable via `BIMODAL_HARNESS_SRC`) and prints a warning if missing — this flake is
  explicitly for oracle-integration development, not for testing/building this repo as a
  standalone release artifact.
- There is also a separate, older, non-flake `code/shell.nix` (`nix-shell`-style, referencing
  `python3Packages.z3`, `setuptools`, `pip`, `networkx`) that is inconsistent with the root
  flake (different Python package set, includes `networkx` that the flake omits) and predates
  the bimodal-only pivot (its help text still mentions the Jupyter notebook workflow).
- **Neither exists as a `packages`/`checks` output** — there is no `nix build` or `nix flake
  check` target, only interactive devShells. For a genuine "test on NixOS without pip" release
  workflow, the flake needs a `packages.default` (built via e.g. `buildPythonPackage` from
  `code/pyproject.toml`) and a `checks.default` wired to the actual current test suite, not just
  a devShell that hopes the right things are on `PYTHONPATH`.

## Recommended Approach

1. **Get an explicit scope decision before doing any more work.** Ask whether "release to PyPI"
   means (a) reviving general-purpose `model-checker` (undoing/rebuilding the builder/iterate/
   multi-theory infra task 100–104 removed) to keep parity with the live 1.2.12 package, or (b)
   formally launching `bimodal-logic` as a new, differently-scoped package and retiring/renaming
   the stale `model-checker` PyPI listing's relationship to this repo. These are different
   engineering efforts (tens of files either way) and the rest of the plan depends on the
   answer.
2. Regardless of direction: **remove the broken `model-checker` entry point** from
   `pyproject.toml` (it currently ships a script that raises `ModuleNotFoundError` on first
   run) or restore what it needs.
3. **Resolve the orphaned `theory_lib/logos/` directory** — either finish deleting it (it's
   unregistered and internally broken via the missing `model_checker.iterate` import) or
   consciously restore it (fix imports, register in `AVAILABLE_THEORIES`, decide if it belongs
   in a "bimodal-only" package at all). Its current half-resurrected state is actively
   accumulating more commits (`e9734a27`) on top of dead code.
4. **Fix or delete the stale top-level `code/tests/` files** that fail collection
   (`test_simple_output_verify.py`, `test_model_building_sync.py`, and likely
   `test_system_imports.py`/`tests/utils/helpers.py`) so `pytest code/tests/` — the command
   CLAUDE.md documents as canonical — actually runs.
5. **Refresh README.md / MANIFEST.in / CLAUDE.md** to describe the architecture that actually
   exists today, whichever direction is chosen in step 1.
6. **Extend the existing root `flake.nix`** rather than writing one from scratch: add
   `packages.default` (buildable Python package) and `checks.default` (wired to whichever test
   tree is canonical) so `nix build`/`nix flake check` give a real release gate on NixOS;
   reconcile it with `code/shell.nix`'s dependency set (decide whether `networkx` belongs, and
   deprecate one of the two shell definitions once they're settled).
7. **Investigate the `test_cross_oracle_differential.py` failures** before signing off on "full
   testing complete" — 2-4 tests failed consistently across two independent partial runs and
   were not root-caused in this session due to per-test Z3 solve time.
8. **Budget real wall-clock time for "complete full testing"** — the bimodal suite alone is
   15-20+ minutes serial on this hardware; plan for `pytest-xdist` parallelization or accept the
   long runtime as part of the release checklist.

## Evidence/Examples (exact commands run and results)

```bash
# CLI: old entry point broken
cd code && PYTHONPATH=src python3 dev_cli.py --help
# -> Error importing from local source: No module named 'model_checker.builder'

# CLI: new entry point works
cd code && PYTHONPATH=src python3 -c "
from bimodal_logic.cli import run
import sys; sys.argv=['bimodal-logic','--help']
run()"
# -> usage: bimodal-logic [-h] {check} ...

# builder module confirmed absent
find code/src/model_checker -maxdepth 1 -type d
# -> models output settings solver syntactic theory_lib utils  (no builder, no iterate)

# top-level test suite: canonical CLAUDE.md command fails to collect
cd code && PYTHONPATH=src pytest tests/ --collect-only -q
# -> ERROR tests/e2e/test_simple_output_verify.py (ModuleNotFoundError: model_checker.output.manager)
# -> ERROR tests/integration/test_model_building_sync.py (ModuleNotFoundError: model_checker.builder)
# -> 269 tests collected, 2 errors

# resurrected logos/ is broken
cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/logos/ --collect-only -q
# -> ModuleNotFoundError: No module named 'model_checker.iterate'

# git history: task 100 deleted logos, feff3cbe unexpectedly restored it
git log --oneline -- code/src/model_checker/theory_lib/logos | head -5
# -> e9734a27 Remove first-order subtheory and its infrastructure from logos
#    feff3cbe removed claude
#    c21b3709 task 100 phase 3: delete non-bimodal module directories
git show feff3cbe --stat | tail -3
# -> 504 files changed, 24043 insertions(+), 107931 deletions(-)

# PyPI comparison
python3 -c "
import urllib.request, json
req = urllib.request.Request('https://pypi.org/pypi/model-checker/json', headers={'User-Agent':'curl/8'})
data = json.load(urllib.request.urlopen(req, timeout=15))
print(data['info']['version'], data['info']['requires_python'])
print(data['info']['requires_dist'])"
# -> 1.2.12, >=3.8
# -> ['z3-solver>=4.8.0', 'networkx>=2.0', 'ipywidgets>=7.0.0; extra == "jupyter"', ...]

# local pyproject.toml identity
grep -A3 "^\[project\]" code/pyproject.toml | head -3
# -> name = "bimodal-logic"
# -> version = "0.1.0"

# bimodal test suite: slow, partial run shows failures
cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -q -m "not slow"
# -> 815 selected; ~580 CPU-seconds reached only ~65% completion
# -> unit/test_cross_oracle_differential.py: multiple F markers (indices ~21, ~34 of 54),
#    reproduced across two independent partial runs; root cause not diagnosed within budget

# Nix
find . -iname flake.nix -o -iname shell.nix   # -> ./flake.nix, ./code/shell.nix
cat flake.nix   # devShells.x86_64-linux.default only, assumes ../BimodalHarness/src sibling,
                # no packages/checks output, python312 + z3-solver + pytest, no networkx
```

## Confidence Level

- **Architecture pivot / broken `model-checker` CLI / resurrected-but-broken `logos/` / stale
  `code/tests/` collection failures**: **High** — all directly reproduced with commands above,
  cross-checked against task 100/104 archived summaries.
- **PyPI dependency/version diff**: **High** — fetched directly from `pypi.org/pypi/model-checker/json`.
- **Existing flake.nix assessment**: **High** — read directly, contents quoted above.
- **Full bimodal test suite pass/fail count**: **Medium** — could not complete a full run within
  this session's time budget (suite estimated at 15-20+ min); partial runs are consistent
  (~65% reached, same failure locations twice) but a definitive pass/fail tally and root cause
  for the `test_cross_oracle_differential.py` failures should be obtained by the implementation
  phase with a longer-running job.
