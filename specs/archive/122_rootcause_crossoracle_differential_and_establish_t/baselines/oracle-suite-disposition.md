# Oracle Suite (Phase 5): Failure Root-Cause and Disposition

Full run: `PYTHONPATH=<pylibs>:oracle:code/src pytest oracle/bimodal_logic/tests -n 6
--junitxml=baselines/junit-oracle.xml -q` -- 550 tests, 12 failed, 5 skipped, 0 errors, 2656s.

This document root-causes each of the 12 failures and records the disposition. All 12 fall into
three categories, none of which is a genuine new semantic regression.

## Category A: xdist cross-file `sys.path` leakage (test collection artifact)

`test_cross_oracle_differential.py`'s `_try_import_bimodal_harness()` does a module-level
`sys.path.insert(0, str(bh_src))` (`test_cross_oracle_differential.py:893-894`) rather than a
scoped/contextual path addition. Under `pytest-xdist`, each worker is a persistent process that
imports many test modules in sequence; once a worker happens to collect
`test_cross_oracle_differential.py` before `test_oracle_interface.py`, the latter's bare
`from bimodal_harness.oracle.protocol import OracleProvider` (`test_oracle_interface.py:37`,
no path manipulation of its own) succeeds only because the *other* file already mutated that
worker's `sys.path`. This is worker-assignment-dependent: confirmed directly -- a serial (`-n 0`)
rerun of the failing `test_oracle_interface.py` tests alone, WITHOUT
`test_cross_oracle_differential.py` also loaded in the same process, raises
`ModuleNotFoundError: No module named 'bimodal_harness'` at collection time instead of running.
This is a pre-existing structural quirk of how the test suite discovers `BimodalHarness`, not a
regression introduced by this task; it only became visible now because task 122 is the first time
the full oracle suite (all files together) has been run to completion rather than just the
differential file in isolation. Not itself a failure category on its own -- it is the *enabling
condition* that let the following genuine-content failures execute rather than collection-error.
No fix applied (out of scope: reworking the differential file's BH-import mechanism is a
structural test-infra change, not part of root-causing the 5 originally-flagged differential
failures or establishing the gate); documented here so a future reader understands why
`test_oracle_interface.py`'s BH-dependent tests exhibit inconsistent behavior test-order-to-test-order.

## Category B: entry-point/packaging tests -- structural, deterministic, out of scope (4 tests)

- `TestEntryPointDiscovery::test_entry_point_registered`
- `TestEntryPointDiscovery::test_entry_point_loads_correct_class`
- `TestEntryPointDiscovery::test_oracle_registry_discover`
- `TestEntryPointDiscovery::test_discovered_provider_is_correct_type`

All four call `importlib.metadata.entry_points(group="bimodal_harness.oracle_providers")`
(directly, or via `bimodal_harness.oracle.registry.OracleRegistry.discover()`, which wraps the
same call) expecting a `z3_base` entry point that loads `Z3OracleProvider`. Root-cause: `oracle/`
has **no packaging metadata at all** -- no `pyproject.toml`, `setup.cfg`, or `setup.py` anywhere
under `oracle/` (confirmed via `find`). It is deliberately unpacked source, consumed only via
`PYTHONPATH`, per task 118's relocation of the oracle out of the shipped package. Since it is
never `pip install`-ed (editable or otherwise), no entry-point metadata is ever registered for
the `bimodal_harness.oracle_providers` group, so `entry_points(group=...)` is unconditionally
empty in this deployment model -- deterministically, on every run, regardless of xdist/worker
scheduling or Z3 timing. This is a pre-existing environment/deployment fact, not a regression
from this task's changes, and not fixable within task 122's scope (adding full packaging +
editable-install machinery to `oracle/` would reverse task 118's explicit relocation-out-of-the-
shipped-package decision and is a packaging-scope change belonging to a separate task, not
"root-cause the differential / establish the gate"). Disposition: `xfail(strict=True)` with a
reason citing this structural gap, OR document as an accepted pre-existing gap if the release
baseline treats "not pip-installable" as an intentional invariant of the oracle's post-118
deployment model (see RELEASE-BASELINE.md).

## Category C (resolved as contention flakes, NOT genuine, NOT xfailed): 7 tests

Initial hypothesis was that these 7 traced to the same untl/snce-timeout-as-UNSAT root cause as
Phase 3 (`some_future`/`some_past`/`next` all unfold through `untl`/`snce`). An isolated (`-n 0`,
BimodalHarness explicitly on path, no concurrent workers) rerun of all 11 non-BM_CM_1 failures
was performed to distinguish genuine solver-timeout reproductions from pure `-n 6` full-suite
CPU-contention artifacts (the same kind of flake independently root-caused for BM_CM_1 in
Category D). Result: **all 7 of the following passed cleanly in isolation** (full log:
`baselines/oracle-failures-serial-rerun-with-bh.txt`, `4 failed, 8 passed in 282.61s`):

- `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement[some_past]` (94.5s contended -> PASSED isolated)
- `TestTernarySerializationAll::test_all_sat_task_relation_ternary` (60.9s contended -> PASSED isolated; this test itself allows up to 60000ms timeout for depth>0 formulas, so even its own generous budget was exceeded only under contention)
- `TestStateIsolationRegression::test_100_calls_mixed_temporal_depths` (5.8s contended -> PASSED isolated)
- `TestGuardedCompositionality::test_nullity_with_temporal_formula_output` (5.6s contended -> PASSED isolated)
- `TestStateIsolationRegression::test_sat_unsat_interleaving_stability` (13.7s contended -> PASSED isolated)
- `TestStateIsolationRegression::test_temporal_propositional_interleaving` (23.7s contended -> PASSED isolated)
- `TestOracleMFormulaBoundarySafe::test_oracle_m_formula_depth1_boundary_safe` (5.3s contended -> PASSED isolated)

Conclusion: none of these 7 are genuine reproductions of the Phase 3 untl/bot solver-timeout
limitation. All are `-n 6` full-suite CPU-contention flakes -- the same mechanism as BM_CM_1
(Category D below), just manifesting in different files because the oracle suite runs many more
concurrent CPU-heavy Z3 solves (differential + soundness + boundary-regression tests all
overlapping across only 6 workers) than the in-package bimodal suite alone. The
`test_soundness_regression.py` tests' own docstrings/assertions *misattribute* the symptom to
"state leakage between calls" (e.g. "Possible state leakage from previous call") -- the isolated
rerun refutes that theory directly: `isolated_z3_context()` correctly resets state between calls
(confirmed by the clean pass with no contention), and the appearance of "leakage" was simply
contention-induced timeout variance across concurrently-running workers, not actual Z3 context
contamination. **Not marked `xfail`** -- these tests are correct as written and pass reliably
once resource contention is removed; no source or test change applied. Consistent with the
`-n 6` (not `-n auto`/12-way) worker-count choice already adopted in Phase 4 for the same reason.

## Category D (informational, not a failure): BM_CM_1 xdist CPU-contention flake (1 test)

`TestExampleRegression::test_regression_all_active_examples[BM_CM_1-example_case7]` (15.2s in
the full `-n 6` run) is the same flake already root-caused and resolved in Phase 4
(`baselines/bimodal-tally.md`): `test_boundary_regression.py`'s `TestExampleRegression` class
duplicates the same 43-example regression set as the in-package `test_bimodal.py`, including the
BM_CM_1 formula whose Z3 solve sits close to the timeout budget and intermittently overruns under
full-suite parallel CPU contention (6 workers here, all with concurrent Z3 solves from the
much-heavier differential/soundness/oracle-interface files running simultaneously). Confirmed:
re-ran in isolation (`-n 0`, with BimodalHarness explicitly on path) and it **passed**
(`oracle-failures-serial-rerun-with-bh.txt`). Not marked `xfail` (a contention-dependent flake
that passes reliably in isolation does not meet the "documented as expected divergence" bar used
for the untl/bot timeout class in `differential-disposition.md`) -- documented here as a known
parallelism-sensitivity, consistent with the Phase 4 finding, not a code change.

## Final disposition summary

| Category | Count | Genuine? | Action |
|---|---|---|---|
| B: `TestEntryPointDiscovery` (packaging/entry-points) | 4 | Yes -- deterministic, reproduces in isolation | `xfail(strict=True)` added to `test_oracle_interface.py`, reason cites this document |
| C: contention flakes (soundness/ternary/enriched-roundtrip) | 7 | No -- all pass in isolation | No test change; documented as `-n 6` contention sensitivity |
| D: BM_CM_1 contention flake | 1 | No -- passes in isolation (Phase 4 finding) | No test change; already documented in Phase 4 |
| **Total accounted** | **12** | | |

Of the original 550-test, `-n 6` full run's 12 failures, only the 4 `TestEntryPointDiscovery`
tests represent a disposition requiring a source change (the `xfail` markers added to
`test_oracle_interface.py`). The remaining 8 are resource-contention artifacts of running many
CPU-heavy Z3 solves across only 6 workers simultaneously and are expected to pass on a clean,
uncontended re-run -- exactly as each did individually above. No new semantic regression was
found anywhere in the oracle suite.
