# Pre-Change Suite Baseline

Recorded before any Phase 2-7 edits (Phase 1, before the `-j`/`--jupyter` pre-check deletion).

| Command | Result |
|---|---|
| `PYTHONPATH=code/src pytest code/tests/ -q` | 283 passed |
| `PYTHONPATH=code/src pytest code/src/model_checker/ -q` | 1910 passed |
| **Total** | **2193 passed** |

Matches the 2193/2193 figure quoted in the 2026-08-11 release review. This is the authoritative
comparison point for the Phase 8 full-suite regression check.
