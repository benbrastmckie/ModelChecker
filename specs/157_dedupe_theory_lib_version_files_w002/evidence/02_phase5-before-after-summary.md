# Phase 5 Before/After Evidence — check-wheel-contents

## Before (Phase 1 baseline, VERSION files present)

```
$ check-wheel-contents dist/*.whl
dist/model_checker-1.3.0-py3-none-any.whl: W002: Wheel contains duplicate files:
  model_checker/theory_lib/bimodal/VERSION
  model_checker/theory_lib/exclusion/VERSION
  model_checker/theory_lib/imposition/VERSION
  model_checker/theory_lib/logos/VERSION
exit_code=1
```

(full output: `01_baseline-check-wheel-contents.txt`)

## After (this phase, from-scratch rebuild, VERSION files removed)

```
$ rm -rf dist build src/model_checker.egg-info
$ python3 -m build --no-isolation --outdir dist
Successfully built model_checker-1.3.0.tar.gz and model_checker-1.3.0-py3-none-any.whl

$ check-wheel-contents dist/*.whl
dist/model_checker-1.3.0-py3-none-any.whl: OK
exit_code=0
```

(full output: `02_after-check-wheel-contents.txt`)

**No `--ignore W002` flag was used in either run.**

## Zero VERSION members confirmed

- Wheel: `python3 -c "import zipfile,glob; print([n for n in zipfile.ZipFile(glob.glob('dist/*.whl')[0]).namelist() if n.endswith('/VERSION')])"` -> `[]`
- Sdist: equivalent `tarfile` scan for members ending `/VERSION` or named `VERSION` -> `[]`

## Conclusion

The four `VERSION` files were the sole W002 duplicate-content group (as hypothesized during
planning from the content-hash sweep of the 1.3.0 wheel). No new duplicate group appeared after
removal. `code/dist/` and `code/build/` remain gitignored (`.gitignore:13`, `**/dist`); this
rebuild did not perturb the working tree.
