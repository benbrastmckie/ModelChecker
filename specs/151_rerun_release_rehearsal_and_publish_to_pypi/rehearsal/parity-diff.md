# Wheel Parity Diff: model_checker 1.3.0 vs. published model-checker 1.2.12

**Run date (UTC)**: 2026-08-12T17:50:40Z
**Environment**: `nix develop` (flake devShell) with an isolated venv created in
`$TMPDIR`, provisioned from `code/scripts/release-tools-requirements.txt`;
`flake.nix` was not modified.

**Pinned tool versions**:
```
build==1.5.0
check-wheel-contents==0.6.3
twine==7.0.0
```

## Artifact Identity

| Artifact | Name | SHA256 |
|----------|------|--------|
| New wheel | `model_checker-1.3.0-py3-none-any.whl` | `5d9d8d5f8895b733fd05b89e0dc3ab65e711ea029105e9d76788e94e39c9aa4c` |
| New sdist | `model_checker-1.3.0.tar.gz` | `bc421583678950f36782cd6004ac1d9d3ca103f1eddc4815fc6a42663d97d3f0` |
| Reference wheel | `model_checker-1.2.12-py3-none-any.whl` (from `pip download --no-deps model-checker==1.2.12`) | `cebe110c0a599c9ab962b7a4fd88686c3cff5c893099b05002117ef3fb7a6d4e` |

Full hash listing: `sha256sums.txt` in this directory.

## File Count Summary

| | Files |
|---|---|
| Reference wheel (1.2.12) | 514 |
| New wheel (1.3.0) | 474 |

## Classified Differences

This script computes the raw file-listing and top-level-directory diffs
(`wheel-files-diff.txt`, `top-level-dir-diff.txt`) but does NOT classify them --
classification of each grouping (intended addition/removal vs. an unexpected
regression) is a **human** step the reviewer performs by reading those two files
against the repository's git history.

## Conclusion

This diff is **evidentiary, not a release gate**. Byte-identity against a prior
published release is never a pass condition -- `twine check --strict` (see
`twine-check.txt`) and bare `check-wheel-contents` (see `wheel-contents.txt`)
are this run's actual hard gates.

## Evidence Files (this directory)

- `build.log` -- full `python -m build` output plus `code/dist/` listing.
- `twine-check.txt` -- `twine check --strict code/dist/*` output.
- `wheel-contents.txt` -- bare `check-wheel-contents` output (hard gate).
- `pip-download-1.2.12.log` -- `pip download --no-deps model-checker==1.2.12` output.
- `sha256sums.txt` -- SHA256 of the new wheel, new sdist, and reference wheel.
- `new-wheel-files.txt` / `ref-1.2.12-wheel-files.txt` -- sorted full file listings.
- `top-level-dir-diff.txt` -- `diff` of maxdepth-2 directory listings.
- `wheel-files-diff.txt` -- full `diff` of the sorted file listings.
- `summary.txt` -- per-step status ledger.
