# Wheel Parity Diff: model_checker 1.3.0 vs. published model-checker 1.2.12

**Rehearsal date**: 2026-07-24
**Environment**: `nix develop` (flake devShell) with an isolated venv created in `$TMPDIR`
(`python -m venv`, `pip install --no-user build twine check-wheel-contents`); `flake.nix` was not
modified.

## Artifact Identity

| Artifact | Name | SHA256 |
|----------|------|--------|
| New wheel | `model_checker-1.3.0-py3-none-any.whl` | `f85e6512e44cf3e2f0ad222a7572d22b0c890fa89ab3c935c077397fda8f04ea` |
| New sdist | `model_checker-1.3.0.tar.gz` | `255d2c01cddcf336e8597db533b998dda054fa8662c1a1f443964bb11e5963b4` |
| Reference wheel | `model_checker-1.2.12-py3-none-any.whl` (from `pip download --no-deps model-checker==1.2.12`) | `cebe110c0a599c9ab962b7a4fd88686c3cff5c893099b05002117ef3fb7a6d4e` |

Full hash listing: `sha256sums.txt` in this directory.

- **Built artifact name**: `model_checker-1.3.0-*` — confirmed **not** `bimodal_logic` or any
  other name. Matches `code/pyproject.toml`'s `name = "model-checker"` / `version = "1.3.0"`.
- **`check-wheel-contents dist/*.whl`**: `dist/model_checker-1.3.0-py3-none-any.whl: OK` (clean,
  see `wheel-contents.txt`).
- **`twine check --strict dist/*`**: `PASSED` for both the wheel and the sdist (see
  `twine-check.txt`).
- **Oracle exclusion**: no `oracle`-named path found in either the built wheel or the sdist
  (`grep -i oracle` over both file listings returns no matches; also checked directly against
  the 1.2.12 reference wheel, which likewise has none).

## File Count Summary

| | Files |
|---|---|
| Reference wheel (1.2.12) | 514 |
| New wheel (1.3.0) | 488 |

## Classified Differences

### Top-level dist-info rename (expected, mechanical)

`model_checker-1.2.12.dist-info/*` -> `model_checker-1.3.0.dist-info/*` — pure version-number
rename of the metadata directory; not a content change.

### Intended: new `model_checker/solver/` module

1.3.0 adds a `model_checker/solver/` package (`backend.py`, `compat.py`, `cvc5_adapter.py`,
`expressions.py`, `lifecycle.py`, `protocols.py`, `registry.py`, `type_guards.py`, `types.py`,
`types_runtime.py`, `z3_adapter.py`, plus a `tests/` subpackage and `README.md`) that does not
exist in 1.2.12. This is a solver-backend abstraction layer (Z3/cvc5 adapters) added since the
last publish; `model_checker/__main__.py` now imports `set_cli_backend`/`validate_backend` from
it. **Intended addition**, not a regression.

### Intended: `model_checker/cli.py` removed

1.2.12 ships a top-level `model_checker/cli.py` that is absent from 1.3.0. `git log --oneline --
code/src/model_checker/cli.py` shows it was deleted in a pre-1.3.0 dead-code-removal commit
(`task 104 phase 3: remove remaining dead code`); `model_checker/__main__.py` (present in both
wheels, unchanged filename) remains the CLI entry point and is unaffected. **Intended cleanup**,
not a regression.

### Not observed as deltas (already true of 1.2.12, contrary to the plan's pre-classification)

The plan's Risks & Mitigations table anticipated several deltas relative to 1.2.12 that were
expected but, on inspection, **do not appear as differences** because 1.2.12 already reflects
that state:

- **`builder`/`iterate`/`jupyter`/`output` "restoration"**: all four are present in *both*
  1.2.12 and 1.3.0 at the same `model_checker/<name>/` path. Whatever the parent restoration
  effort recovered, it was recovered relative to a *different* (intermediate, unpublished) broken
  state — not relative to the last real PyPI publish (1.2.12), which never lost these.
- **`exclusion`/`imposition` theory "restoration"**: both subtheories are present under
  `model_checker/theory_lib/` in *both* 1.2.12 and 1.3.0. Same conclusion as above.
- **First-order subtheory "removal"**: no `first_order` (or `quantifier`-named) path exists in
  *either* wheel. 1.2.12 never shipped it, so there is nothing to observe as "removed" in this
  diff.

None of the above invalidates the restoration work — it only means 1.2.12 is not the right
baseline for observing those specific deltas; they were regressions/changes against an
intermediate, never-published state, and this diff only has visibility into the last **published**
artifact. This is documented here so a reviewer does not misread "no delta" as "restoration did
not happen."

## Conclusion

- Artifact identity, naming, and content are as required: `model_checker-1.3.0`, no `oracle/`
  tree, clean `check-wheel-contents`, `twine check --strict` PASSED on both artifacts.
- All observed content deltas versus 1.2.12 (`solver/` addition, `cli.py` removal, dist-info
  rename) are intended and pre-existing in the repository's git history, not artifacts of this
  rehearsal.
- No regression relative to 1.2.12 was found. The release is not gated on byte-identity with
  1.2.12 (per plan Non-Goals) — this diff is evidentiary, not a pass/fail gate.

## Evidence Files (this directory)

- `build.log` — full `python -m build` output plus `dist/` listing.
- `wheel-contents.txt` — `check-wheel-contents` output plus full wheel file/size listing.
- `twine-check.txt` — `twine check --strict dist/*` output.
- `pip-download-1.2.12.log` — `pip download --no-deps model-checker==1.2.12` output.
- `sha256sums.txt` — SHA256 of the new wheel, new sdist, and reference (1.2.12) wheel.
- `new-wheel-files.txt` / `ref-1.2.12-wheel-files.txt` — sorted full file listings of each wheel.
- `top-level-dir-diff.txt` — `diff` of maxdepth-2 directory listings.
- `wheel-files-diff.txt` — full `diff` of the sorted file listings (253 lines; dominated by the
  dist-info rename and the `solver/`/`cli.py` changes classified above).
