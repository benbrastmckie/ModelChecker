"""CI-configuration contract tests: keep .github/workflows/tests.yml and flake.nix in sync,
keep the wall-clock timing-marker taxonomy enforced against source, keep the extracted
unstable-watch classifier unit-tested, and keep every gating pytest invocation deselecting
`unstable`.

See test_workflow_parity.py and test_timing_marker_coverage.py for the first two guards,
test_unstable_watch_classifier.py for the classifier's unit tests (loads
`.github/scripts/unstable_watch_classify.py` by absolute path), and
test_unstable_deselection_wiring.py for the fourth (every gating `-m` expression across
tests.yml, flake.nix, differential-tests.yml, and oracle/run-oracle-suite.sh carries
`not unstable`).
"""
