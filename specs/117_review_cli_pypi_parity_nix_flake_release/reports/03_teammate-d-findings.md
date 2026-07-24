# Horizons Findings: Task 117 Long-Term Alignment

## Key Findings

1. **ROADMAP.md is nearly empty and task 117 is the natural place to seed it.** `specs/ROADMAP.md`
   contains one durable decision (package identity: `model_checker`, four theories, `oracle/`
   kept standalone) and a Phase 1 section that literally reads `- [ ] (No items yet -- add
   roadmap items here)`. None of tasks 118-125 attached `roadmap_items` in `state.json`
   (verified via `jq '.active_projects[] | select(.project_number>=117)'` — every entry shows
   `roadmap_items=none`). Closing 117 without populating this is a missed opportunity: this is
   the first natural checkpoint since the restoration effort to declare what comes next
   (release cadence, CI hardening, oracle's role) as durable roadmap items rather than letting
   that context evaporate into archived task directories.

2. **The remaining work is almost entirely USER-ONLY — task 117 is closer to done than "systematic
   review" suggests.** `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`
   shows version 1.3.0 confirmed, rehearsal evidence collected, and every substantive remaining
   step marked **USER-ONLY** per `.claude/rules/pr-prohibition.md` (push branch, tag, PyPI/TestPyPI
   OIDC trusted-publisher registration, GitHub Environment setup, tag push, upload verification).
   Per `.claude/rules/pr-prohibition.md`, no agent may push or tag regardless of task framing.
   Strategically, task 117 should close as "restoration + release engineering complete, handed to
   user for publish" rather than accumulate more agent-side polish work that can't move the
   needle on the actual blocker (human action).

3. **CI has a live regression the 118-125 wave never touched: `.github/workflows/differential-tests.yml`
   points at paths and a test file that no longer exist.** Task 118 moved
   `code/src/bimodal_logic/` to `oracle/bimodal_logic/` and relocated
   `test_cross_oracle_differential.py` to `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
   (confirmed: `find` shows the file only at that path now). But
   `.github/workflows/differential-tests.yml` still (a) triggers on the now-nonexistent path
   `code/src/bimodal_logic/**`, and (b) invokes pytest against
   `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py`, a
   path that no longer holds that file. `git log -- .github/workflows/differential-tests.yml`
   shows the file's last commit is `7ae80ece` ("task 109"), well before the restoration branch —
   it was never updated. This workflow will fail (file-not-found) or silently stop triggering on
   the relevant paths the next time it's exercised, and it was outside the scope of every one of
   tasks 118-125 as written. This is a concrete, low-effort candidate for a follow-up task (or
   a 117-scoped fix, if the review phase has budget) — the kind of loose end a "systematic
   review" framing exists to catch.

4. **The branch carries 48 commits and a 379-file, ~78K-insertion diff against `master`, with zero
   commits behind.** (`git rev-list --left-right --count master...HEAD` → `0  48`.) This is a
   large, clean fast-forward-able divergence — good news for merge risk (no rebase conflicts from
   master drift), but it means `master` has been frozen at the pre-restoration state for the
   entire duration of tasks 117-125. The longer this sits un-merged, the more that risk profile
   can change (someone else committing to master, dependency updates, etc.), and the more the
   installed PyPI package (1.2.12) diverges from what's actually in the repository. This argues
   for treating "merge to master" as tightly coupled to task 117's closure, not a separate
   follow-up — the `/merge` command (user-invoked) is the natural next action immediately after
   the PyPI publish checklist, not a deferred nice-to-have.

5. **The Nix flake (task 123) was framed as "build for testing on NixOS" but is well-positioned to
   become the standing CI/test harness rather than a one-off deliverable.** `flake.nix` now
   provides `packages.default` (nixpkgs-native `buildPythonPackage`), `checks.default` (runs the
   full pytest suite), and a devShell — i.e., `nix flake check` is already a real, repeatable gate.
   Nothing in `.github/workflows/` currently invokes Nix (the existing `release.yml` and
   `differential-tests.yml` both use plain `pip`/`actions/setup-python`). Wiring `nix flake check`
   into a GitHub Actions job (via `cachix/install-nix-action` or similar) would let the flake pay
   for itself continuously instead of being a NixOS-only local convenience — a strong "adjacent
   roadmap item" candidate, complementary to but distinct from the differential-tests.yml fix in
   finding 3.

6. **The `oracle/` tree's long-term role is architecturally decided but not operationally decided.**
   The durable decision in ROADMAP.md fixes *where* oracle lives (standalone, excluded from the
   wheel) but says nothing about *how often* or *by what trigger* the cross-oracle differential
   suite should run going forward. Combined with finding 3 (its CI trigger is currently broken),
   the oracle risks becoming a manually-run-only artifact — undermining the differential-testing
   value it was designed to provide. This is worth an explicit roadmap item: e.g. "oracle
   differential suite runs on every PR touching `oracle/` or `theory_lib/bimodal/`" as a named,
   tracked target rather than an implicit assumption.

## Recommended Approach

- **Cut task 117's remaining scope to: (a) confirm the PUBLISH-CHECKLIST.md pre-flight items are
  genuinely green (re-run `nix flake check` / `nix build` once, spot-check the rehearsal
  evidence), (b) fix the `differential-tests.yml` path/test-location bug (finding 3) since it's
  small and squarely "stabilize the repo," (c) seed `specs/ROADMAP.md` Phase 1 with 2-4 concrete
  forward items, then close.** Do not expand review scope into new polish — the release
  engineering task (125) already produced a complete, evidence-backed checklist; task 117's job
  is to sanity-check that work and hand off cleanly, not redo it.
- **Recommend roadmap items to seed** (for the user to bless via the completion workflow's
  `roadmap_items` field): (1) merge `task-117-restore-model-checker` to `master` and publish
  1.3.0 to PyPI [immediate, user-gated]; (2) fix and re-verify `differential-tests.yml` against
  the relocated `oracle/bimodal_logic/` paths; (3) add a `nix flake check` CI job so the flake
  becomes a continuous gate, not a one-off deliverable; (4) decide and document an explicit
  differential-suite run cadence/trigger for `oracle/`.
- **Versioning/cadence**: 1.3.0 (minor bump from 1.2.12) is well-justified — first-order removal
  is a breaking-enough change that some projects would call it a major bump, but given this is a
  research-tooling package with no stated semver contract beyond "notable changes documented,"
  minor is a defensible, low-friction choice already baked into `pyproject.toml` and
  `CHANGELOG.md`. Going forward, tying releases to `v{X.Y.Z}` git tags (already the trigger for
  `release.yml`) plus the `/tag` skill gives a repeatable cadence — recommend documenting "tag
  after each roadmap-item-closing merge to master" as the release rhythm rather than batching
  large multi-task restorations like 118-125 again before the next release.
- **Archive/vault**: no action needed yet — `next_project_number` is 126, far from the 1000
  threshold that triggers vault archival (`.claude/rules/state-management.md`). No urgency to
  archive the 118-125 spec artifacts; they're valuable provenance for the 1.3.0 release notes and
  should stay live at least through the actual PyPI publish, in case publish-time issues require
  reference back to the rehearsal evidence.

## Evidence/Examples

- `specs/ROADMAP.md:11-13` — Phase 1 placeholder, unpopulated.
- `specs/state.json` — `jq` query confirms no `roadmap_items` set on tasks 117-125.
- `specs/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md:16-101` — pre-flight
  checks and ordered release steps, all remaining substantive actions marked **USER-ONLY**.
- `.claude/rules/pr-prohibition.md` — standing prohibition on agent push/tag/PR/publish.
- `.github/workflows/differential-tests.yml:1-11` — stale path triggers (`code/src/bimodal_logic/**`)
  and stale test invocation path (`.../theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py`).
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — actual current location of the
  relocated test (via `find`).
- `git log --oneline -- .github/workflows/differential-tests.yml` → last touched at `7ae80ece`
  ("task 109"), predating the restoration branch entirely.
- `git rev-list --left-right --count master...HEAD` → `0  48` (branch is 48 ahead, 0 behind
  master).
- `git diff --stat master...HEAD` → 379 files changed, ~78,303 insertions.
- `code/CHANGELOG.md:7-9` — `[Unreleased]` section still empty above the populated `[1.3.0]`
  entry, confirming 1.3.0 is the finalized, documented target version.
- `.github/workflows/release.yml:1-10` — tag-triggered (`v[0-9]+.[0-9]+.[0-9]+`) release
  pipeline, consistent with a tag-per-release cadence recommendation.
- `flake.nix` via task 123 summary (`specs/123_.../summaries/01_nix-flake-multisystem-rewrite-summary.md`)
  and `specs/TODO.md:52-64` (task 123 description) — confirms `packages.default` and
  `checks.default` exist but are not yet wired into `.github/workflows/`.

## Confidence Level

**High** on findings 1, 2, 3, 4 (all directly verified by reading `ROADMAP.md`, `state.json`,
`PUBLISH-CHECKLIST.md`, running `git log`/`git diff`/`find` against the actual files). **Medium**
on findings 5 and 6 (the Nix-CI and oracle-cadence recommendations are reasonable strategic
inferences from the artifacts, but I did not exhaustively search for a pre-existing plan or
discussion elsewhere in `specs/` that might already address them — the spawn-analysis report at
`specs/117_.../reports/02_spawn-analysis.md` and the master plan at
`specs/117_.../plans/01_restore-model-checker-release.md` are worth a targeted cross-check by
another researcher/synthesis pass before treating these as novel).
