# Project Roadmap

## Durable Decisions

- **Package identity**: the framework ships as the `model_checker` package (four registered
  theories: `logos`, `exclusion`, `imposition`, `bimodal`) built from `code/` with
  `[tool.setuptools.packages.find] where = ["src"]`. The cross-solver differential oracle is
  kept as a standalone, unpacked top-level `oracle/` tree — outside `code/src/` and excluded
  from the wheel — rather than shipped as part of the installable package.

## Phase 1: Current Priorities (High Priority)

- [ ] **Merge and publish 1.3.0** [USER-ONLY]: land the release-prep branch (`/merge`), tag
  `v1.3.0`, and complete the OIDC-based PyPI publish per
  `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`. No agent performs any
  step in this item — push, tag, `/merge`, and PyPI upload are all user-only per
  `.claude/rules/pr-prohibition.md`.
- [ ] **Add `nix flake check` as a CI gate job**: the flake's `checks.default` derivation
  (in-package bimodal suite, 286/286) currently only runs when invoked locally or as part of
  release-prep review. Add a GitHub Actions workflow (or a job within an existing one) that runs
  `nix flake check` on every push/PR so the hermetic reproducibility gate is continuously
  enforced, not just checked manually before a release.
- [ ] **Oracle differential-suite cadence decision**: `differential-tests.yml` is now correctly
  path-filtered to `oracle/bimodal_logic/**` and `code/src/model_checker/theory_lib/bimodal/**`
  and points at the live `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`. Decide
  whether push/PR-triggered (current behavior) is the right cadence long-term, or whether the
  suite's slower tests (full complexity-5 scans, `TestBimodalHarnessIntegration`) warrant a
  separate scheduled/nightly job instead of blocking every matching push.
- [ ] **Follow-up task for the 28 documented "everything-else" failures**: none of these are
  release-blocking (all pre-existing, none traced to release-prep source edits — see
  `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/rest-suite-disposition.md`
  for the full 8-category root-cause breakdown). Start with Category B/G (12 tests total): the
  malformed `"A[]"` shared test-formula literal in
  `code/tests/utils/helpers.py::create_test_model()` (default `conclusions=['A[]']`, not valid
  formula syntax for the current parser) plus one hardcoded duplicate in
  `test_batch_output_real.py`. Categories A (6, builder-suite drift), C (4, timing/threshold
  authoring defects), D (2, broken scaling-assertion threshold), E (1, `Mock.assert_and_track`
  misuse), F (1, missing fixture module), and H (2, unset `WitnessRegistryError`/
  `WitnessConstraintError.theory`) can be folded into the same follow-up task or split further at
  triage time.

## Success Metrics

- (Define success metrics here)
