# Restore-Point SHA Inventory

Read-only verification that each restore-point SHA's parent commit (`<sha>^`) contains the
expected source path, using `git ls-tree <sha>^ -- <path>`. No files under `code/` were modified
by this phase. This inventory is consumed by later restoration tasks (New Task 2, New Task 3);
this task does not execute any `git checkout <sha>^ -- <path>` restore.

## Verification Commands and Results

| Restore Target | SHA | Parent Commit | Path | Status |
|---|---|---|---|---|
| builder/ | `013a486c` | `013a486c^` | `code/src/model_checker/builder/` | Confirmed — 20 entries (README.md, `__init__.py`, comparison.py, detector.py, error_types.py, errors.py, example.py, filesystem.py, importer.py, loader.py, module.py, project.py, protocols.py, runner.py, runner_utils.py, serialize.py, strategies.py, `tests/`, translation.py, types.py) |
| iterate/ | `c21b3709` | `c21b3709^` | `code/src/model_checker/iterate/` | Confirmed — 13 entries (README.md, `__init__.py`, base.py, build_example.py, constraints.py, core.py, errors.py, graph.py, iterator.py, metrics.py, models.py, statistics.py, `tests/`, types.py) |
| jupyter/ | `c21b3709` | `c21b3709^` | `code/src/model_checker/jupyter/` | Confirmed — full package present (NixOS_jupyter.md, README.md, TROUBLESHOOTING.md, `__init__.py`, adapters.py, builder_utils.py, `debug/`, display.py, environment.py, exceptions.py, interactive.py, notebook_helpers.py, `notebooks/`, `tests/`, types.py, ui_builders.py, unicode.py, utils.py). Also confirmed present at this SHA: `code/jupyter_link.py`, `code/run_jupyter.sh`. |
| output/manager.py | `71ef79a1` | `71ef79a1^` | `code/src/model_checker/output/manager.py` | Confirmed — single blob present |
| output/progress/ | `71ef79a1` | `71ef79a1^` | `code/src/model_checker/output/progress/` | Confirmed — 6 entries (README.md, `__init__.py`, animated.py, core.py, display.py, spinner.py) |
| exclusion/ | `abb3bf7d` | `abb3bf7d^` | `code/src/model_checker/theory_lib/exclusion/` | Confirmed — full theory package present (CITATION.md, LICENSE.md, README.md, TODO.md, VERSION, `__init__.py`, `docs/`, examples.py, `history/`, iterate.py, `notebooks/`, operators.py, semantic.py, `semantic/`, semantic_backup.py, semantic_original.py, `tests/`) |
| imposition/ | `abb3bf7d` | `abb3bf7d^` | `code/src/model_checker/theory_lib/imposition/` | Confirmed — full theory package present (CITATION.md, LICENSE.md, README.md, VERSION, `__init__.py`, `docs/`, examples.py, `examples_refactored/`, iterate.py, `notebooks/`, operators.py, `reports/`, semantic.py, `semantic/`, `tests/`) |

## Misses

None. All 6 SHA/path pairs (5 distinct restore-point SHAs, one — `c21b3709`— covering two paths)
resolved successfully via `git ls-tree <sha>^ -- <path>`.

## Commands Used

```bash
git ls-tree 013a486c^ -- code/src/model_checker/builder/
git ls-tree c21b3709^ -- code/src/model_checker/iterate/
git ls-tree c21b3709^ -- code/src/model_checker/jupyter/
git ls-tree c21b3709^ -r --name-only | grep -i jupyter
git ls-tree 71ef79a1^ -- code/src/model_checker/output/manager.py
git ls-tree 71ef79a1^ -- code/src/model_checker/output/progress/
git ls-tree abb3bf7d^ -- code/src/model_checker/theory_lib/exclusion/
git ls-tree abb3bf7d^ -- code/src/model_checker/theory_lib/imposition/
```

This phase performed no writes outside `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/`.
