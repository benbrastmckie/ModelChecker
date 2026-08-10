# Gate run evidence, 2026-08-09 (+ exhaustive-scan attempt 3, 2026-08-10)

Raw evidence for the "Second adjudicable run" and "Exhaustive scan" sections of
`../oracle-baseline-STATUS.md`, and for `../exhaustive-scan/STATUS.md`. Promoted out of the run's
scratch staging area so the committed honest record cites files that exist.

| File | What it is |
|---|---|
| `gate-run.txt` | `verify-refactor.sh` full run, Step 6 live. Exit 1, 3 checks FAILED. |
| `step6-gating-oracle-suite.txt` | Step 6's gating-suite output: both passes, tracebacks, summary. |
| `skip-oracle-run.txt` | `verify-refactor.sh --skip-oracle`. Exit 1, 2 checks FAILED. |
| `step4-bimodal-attempt{1,2}.txt` | Step 4's two bimodal attempts from the full run. |
| `machine-{before,during,after}.txt` | Quietness captures bracketing the full run. |
| `contention-watch.log` | Continuous 60 s foreign-contention sampling across all runs. |
| `exhaustive-attempt{1,2}-aborted.txt` | Why each of the first two exhaustive-scan attempts is unadjudicable (neither reached completion). |
| `exhaustive-attempt{1,2}-machine-before.txt` | Quietness at each of the first two exhaustive-scan launches. |
| `exhaustive-attempt{1,2}-machine-contention.txt` | Raw captures of the contention that invalidated each of the first two. |
| `exhaustive-attempt3-machine-before.txt` | Quietness at the third exhaustive-scan launch (2026-08-10T02:20:56Z), the attempt that reached completion. |
| `exhaustive-attempt3-contention-watch.log` | 68-sample, 60s-interval contention watch across attempt 3's full run (58 quiet, 9 contention samples; did not invalidate the run). |

Attempt 3's promoted scan artifacts (`report.json`, `SCAN_COMPLETE`, `exhaustive-run.txt`) and its
full adjudication live in `../exhaustive-scan/`, not here — this directory holds only the raw
quietness/contention captures for that attempt, alongside the earlier gate-run evidence.

Read the captures raw. An earlier revision of these notes reached a wrong conclusion because a
display filter selected only section labels and hid the CPU-hog lines the captures had correctly
recorded; the captures were right and the reading was not.
