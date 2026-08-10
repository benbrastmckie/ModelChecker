# Phase 1 Handoff: Restore Core Infrastructure Modules from Git History

**Status**: COMPLETED
**Commit**: 3968bfb9 "task 119 phase 1: restore builder, iterate, jupyter, output infrastructure"

## What was done

Restored five deleted paths from their confirmed pre-deletion git-history restore points using
the non-destructive `git checkout <sha>^ -- <path>` form:
- `code/src/model_checker/builder/` from `013a486c^` (22 entries)
- `code/src/model_checker/iterate/` from `c21b3709^` (14 entries)
- `code/src/model_checker/jupyter/` from `c21b3709^` (full package)
- `code/src/model_checker/output/manager.py` and `output/progress/` from `71ef79a1^` (6 entries)

## Deviation from plan

Task 118's `restore-inventory.md` reported 20 entries for `builder/` and 13 for `iterate/`; the
actual `git ls-tree <sha>^` output (and the resulting working-tree restore) has 22 and 14
respectively. Verified via `git ls-tree 013a486c^ -- code/src/model_checker/builder/` and
`git ls-tree c21b3709^ -- code/src/model_checker/iterate/` — the restore is a byte-for-byte
match of the historical tree; the inventory's prose enumeration simply missed
`validation.py`/`z3_utils.py` (builder) and one additional file (iterate). No action needed;
noted inline in the plan checklist.

## Process note (not a plan deviation)

The working tree had unrelated pre-existing dirty state (from parallel session activity:
`.gitignore`, `specs/state.json`, `specs/TODO.md`, etc.) that triggered
`guard-destructive-git.sh` on the `git checkout <sha>^ -- <path>` restore commands (the hook's
regex does not distinguish the safe revisioned form from the unsafe bare
`git checkout -- <path>` form). Resolved via the sanctioned `git-snapshot.sh` stash-based
snapshot immediately followed by the restore commands, then `git stash pop` to restore the
unrelated dirty state before committing only the five restored paths. No other agent's
in-progress file state was lost (stash pop restored the tree to its pre-snapshot content
exactly).

## Verification

- `git status --short` after restore showed only the five restored paths as new files.
- Entry counts cross-checked against `git ls-tree <sha>^` directly (see deviation note above).
- Commit scoped to only the five restored paths (`git add` explicit paths, not `-A`).

## Next phase

Phase 2: reconcile imports in the restored modules against current HEAD's API and verify both
CLI entry points run cleanly.
