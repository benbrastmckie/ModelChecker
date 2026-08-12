# Phase 7 Evidence — Regression Sweep and Final VERSION Sweep

## Theory-conformance suite

```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/ -v
```

Result: `67 passed`.

## Builder suite

```
PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v
```

Result: `232 passed, 75 subtests passed`.

## Final repo-wide VERSION sweep (scoped to code/, per plan)

```
grep -rn -w VERSION code/ --exclude-dir={.git,dist,build,__pycache__}
```

Files matched:

| File | Nature of hit |
|---|---|
| `code/scripts/release-verify.sh` | **Deliberately untouched** — task 156's territory (in flight); see handoff note below |
| `code/scripts/README.md` | Unrelated: `--ref VERSION` is `release-verify.sh`'s own CLI flag placeholder (a published `model-checker` version string to diff against), not the theory_lib duplicate-file topic |
| `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` | Our own Phase 2 edit — correctly states there is *no* separate on-disk `VERSION` file |
| `code/src/model_checker/builder/project.py` | Our own Phase 2 edit — comment explaining why `VERSION` is `OPTIONAL_COPY_ITEMS` |

No unexpected hit. `release-verify.sh` is the only remaining site that still encodes the old W002
expectation as fact; it was deliberately not edited (see handoff note in the summary).

## Additional stale-claim site found outside file_scope (reported, not edited)

`.github/RELEASE_SETUP.md` (outside this task's `file_scope`, not `code/`) also documents the old
W002 expectation at lines 197 and 205 ("Deduplicating those files is tracked as a separate, later
change" / "the tree has since grown the W002-triggering duplicate VERSION files"). This is now
stale for the same reason `release-verify.sh` is. It is **not edited** by this task (out of
file_scope) but is flagged in the handoff note below alongside `release-verify.sh` for whichever
task next touches the release rehearsal documentation.

## Git status / no remote-affecting operation

- `git status --short` at Phase 7 close shows no uncommitted changes under this task's file_scope;
  the only entries present are pre-existing, unrelated session/state files
  (`specs/events.jsonl`, `.syncprotect`, `.orchestrator-multi-state*`, `.sessions/`, per-task
  `.lock/` directories) that are not part of this task's `modified_files`.
- `code/dist/` remains git-ignored (confirmed via `git check-ignore -v code/dist` ->
  `code/.gitignore:13:dist/`); `code/build/` does not currently exist on disk.
- No `git push`, `git tag`, or `gh pr create` was run at any point in this dispatch, per
  `.claude/rules/pr-prohibition.md`.
