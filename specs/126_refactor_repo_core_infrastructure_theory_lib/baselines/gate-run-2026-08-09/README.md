# Gate run evidence, 2026-08-09

Raw evidence for the "Second adjudicable run" and "Exhaustive scan: attempted twice" sections of
`../oracle-baseline-STATUS.md`. Promoted out of the run's scratch staging area so the committed
honest record cites files that exist.

| File | What it is |
|---|---|
| `gate-run.txt` | `verify-refactor.sh` full run, Step 6 live. Exit 1, 3 checks FAILED. |
| `step6-gating-oracle-suite.txt` | Step 6's gating-suite output: both passes, tracebacks, summary. |
| `skip-oracle-run.txt` | `verify-refactor.sh --skip-oracle`. Exit 1, 2 checks FAILED. |
| `step4-bimodal-attempt{1,2}.txt` | Step 4's two bimodal attempts from the full run. |
| `machine-{before,during,after}.txt` | Quietness captures bracketing the full run. |
| `contention-watch.log` | Continuous 60 s foreign-contention sampling across all runs. |
| `exhaustive-attempt{1,2}-aborted.txt` | Why each exhaustive-scan attempt is unadjudicable. |
| `exhaustive-attempt{1,2}-machine-before.txt` | Quietness at each exhaustive-scan launch. |
| `exhaustive-attempt{1,2}-machine-contention.txt` | Raw captures of the contention that invalidated each. |

Read the captures raw. An earlier revision of these notes reached a wrong conclusion because a
display filter selected only section labels and hid the CPU-hog lines the captures had correctly
recorded; the captures were right and the reading was not.
