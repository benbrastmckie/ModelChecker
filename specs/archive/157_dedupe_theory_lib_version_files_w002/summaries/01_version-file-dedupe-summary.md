# Implementation Summary: Deduplicate theory_lib VERSION files (W002)

- **Task**: 157 - Deduplicate the four theory_lib VERSION files to clear check-wheel-contents W002
- **Plan**: `specs/157_dedupe_theory_lib_version_files_w002/plans/01_version-file-dedupe.md`
- **Status**: Implementation complete, all 7 phases COMPLETED

## What was done

Adopted the plan's remedy (a) — remove the four `VERSION` files and consolidate on each theory's
`__init__.py` `__version__` as the single source of truth — in place of the research's originally
recommended remedy (b) (keep the files, exclude from wheel), which planning had closed out as a
demonstrated functional regression (`FileNotFoundError` on `model-checker -l <name>` project
generation for pip-installed users).

Work proceeded in the plan's mandated order — relax scaffolding requirements (Phase 2) and
packaging assertions (Phase 3) *before* changing what ships (Phase 4) — so the tree stayed green
at every phase boundary and the ordering that disqualified remedy (b) was never reproduced.

### Phase-by-phase

1. **Baseline and scope widening**: fresh build + `check-wheel-contents` confirmed the pre-existing
   W002 finding (exit 1, four `VERSION` paths); packaging suite baseline was green
   (114 passed, 4 skipped). `state.json`'s `file_scope` for project 157 was already widened to 11
   entries by the time this dispatch started.
2. **Relaxed on-disk contract requirements**: `builder/project.py` moved `'VERSION'` from
   `REQUIRED_COPY_ITEMS` to `OPTIONAL_COPY_ITEMS`; `test_theory_conformance.py` dropped it from
   `REQUIRED_ROOT_ITEMS`; `THEORY_ARCHITECTURE.md`'s Theory Contract bullet was amended to name
   `__init__.py`'s `__version__` as the sole per-theory version source. Files were still on disk
   and still shipped — tree stayed green.
3. **Relaxed packaging contract assertions**: `test_inclusions.py` dropped `"VERSION"` from
   `REQUIRED_ROOT_FILES`; `test_parity.py` dropped it from `_is_data_path()` and its docstring.
   `test_exclusions.py` was left untouched (nothing to exclude while the files still ship).
4. **Stopped shipping and deleted the four files**: dropped `VERSION` from
   `pyproject.toml`'s `[tool.setuptools.package-data]` allowlist and from `MANIFEST.in`'s
   `recursive-include`; `git rm`'d the four
   `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files.
5. **Verified by rebuilding from scratch**: `rm -rf dist build egg-info` then a clean
   `python -m build`; plain `check-wheel-contents dist/*.whl` (no `--ignore`) returned `OK`, exit
   0. Zero `VERSION` members in either the wheel or the sdist.
6. **Full packaging contract suite + generate-then-execute**: 106 passed, 4 skipped (pre-existing
   notebook skips only), zero failures/deselections. `test_generate_then_execute` passed for all
   four registered theories. An independent spot-check unpacked the fresh wheel and ran
   `BuildProject('logos').generate('demo')` against it directly — succeeded, generated project has
   no `VERSION` file.
7. **Regression sweep and handoff**: theory-conformance (67 passed) and builder (232 passed, 75
   subtests) suites green. Final repo-wide sweep confirmed the only remaining `VERSION` hits under
   `code/` are the deliberately-untouched `release-verify.sh`, an unrelated CLI-flag placeholder in
   `code/scripts/README.md`, and this task's own corrected references in
   `THEORY_ARCHITECTURE.md`/`project.py`.

## Downstream handoff (not edited by this task)

Two sites now describe a W002 expectation that no longer holds. Neither was edited — both are
outside this task's territory or `file_scope`:

- **`code/scripts/release-verify.sh`** (task 156's territory, `[IMPLEMENTING]` and in flight
  during this dispatch — explicitly out of scope, per the plan's non-goals):
  - Line 15: step (d1) `check-wheel-contents (bare)`, labelled "expected nonzero (W002)
    [informational]" — should become the **hard gate**.
  - Line 16: step (d2) `--ignore W002` — currently the hard gate; becomes unnecessary.
  - Lines 52-57: the "Reading a nonzero check-wheel-contents (bare) exit" comment block —
    describes the now-superseded W002 expectation.
- **`.github/RELEASE_SETUP.md`** (outside `file_scope`, discovered during the Phase 7 sweep, not
  named by the research or the plan): lines 197 and 205 describe the same now-stale W002
  expectation ("Deduplicating those files is tracked as a separate, later change" /
  "the tree has since grown the W002-triggering duplicate VERSION files").

Both should be updated by task 156 (owner of `release-verify.sh`) and/or task 151 (release
rehearsal), which can now record a **clean** `check-wheel-contents` run rather than an
`--ignore W002` caveat.

## Verification results

- Plain `check-wheel-contents dist/*.whl` on a from-scratch build: `OK`, exit 0, no `--ignore`.
- Freshly built wheel and sdist: zero `VERSION` members in either.
- Full packaging contract suite (`code/tests/packaging/`): 106 passed, 4 skipped (pre-existing,
  unrelated), 0 failures/errors/deselections.
- `test_generate_then_execute.py`: passed for all four registered theories.
- Manual unpacked-wheel `BuildProject.generate()`: succeeded; generated project has no `VERSION`.
- Theory-conformance suite: 67 passed. Builder suite: 232 passed, 75 subtests passed.
- Before/after `check-wheel-contents` evidence recorded under `evidence/`.

## Files modified

- `code/src/model_checker/builder/project.py`
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py`
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md`
- `code/tests/packaging/test_inclusions.py`
- `code/tests/packaging/test_parity.py`
- `code/pyproject.toml`
- `code/MANIFEST.in`
- `code/src/model_checker/theory_lib/bimodal/VERSION` (deleted)
- `code/src/model_checker/theory_lib/exclusion/VERSION` (deleted)
- `code/src/model_checker/theory_lib/imposition/VERSION` (deleted)
- `code/src/model_checker/theory_lib/logos/VERSION` (deleted)
- `specs/state.json` (file_scope widening, status transitions — already present at dispatch start)
- `specs/TODO.md` (regenerated)

## Plan Deviations

- None (implementation followed plan). The plan's Phase 1 file_scope widening had already been
  applied to `specs/state.json` before this dispatch began; this dispatch confirmed it (11
  entries, matching the plan's expectation) rather than re-applying it.
- One addition beyond the plan's explicit instructions: Phase 7's regression sweep additionally
  surfaced `.github/RELEASE_SETUP.md` as a second stale-claim site (not named by the plan, which
  only named `release-verify.sh`). It is reported above, not edited, consistent with the plan's
  non-goals and the pre-edit-gate contract's "record, don't silently skip or force" rule for an
  out-of-scope finding.

## No push, tag, or PR

Confirmed: no `git push`, `git tag`, or `gh pr create` was run at any point in this dispatch, per
`.claude/rules/pr-prohibition.md`.
