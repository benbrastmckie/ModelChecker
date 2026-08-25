# Publish Checklist: model-checker 1.3.0

This checklist walks through publishing `model-checker` 1.3.0. It ends in **user-only** actions
per `.claude/rules/pr-prohibition.md`: no agent pushes commits, pushes tags, creates PRs, invokes
`/merge`, or uploads to PyPI/TestPyPI. Steps below are explicitly marked **USER-ONLY** where that
applies; every other step is informational/verification and can be done by either the user or an
agent, but nothing in this checklist authorizes an agent to perform the USER-ONLY steps.

## 0. Blocking Gate — PyPI Trusted Publisher Registration (USER-ONLY, do this FIRST)

**This is the one item standing between the current tree and a safe tag push.** Everything else
in this checklist is already verified (see Section 1).

- [ ] **USER-ONLY**: on [pypi.org](https://pypi.org), go to your account's **Publishing**
      settings (or the `model-checker` project's **Settings → Publishing** if the project already
      exists on PyPI) and confirm a trusted publisher is registered with **exactly**:
      - **Owner**: `benbrastmckie`
      - **Repository name**: `ModelChecker`
      - **Workflow name**: `release.yml`
      - **Environment name**: `pypi`
- [ ] **USER-ONLY, optional but recommended**: register the TestPyPI equivalent (same Owner/
      Repository/Workflow, **Environment name**: `testpypi`) so the rehearsal publish job
      (`publish-testpypi`) also succeeds rather than soft-failing.

**GitHub-side half already confirmed present**: both the `pypi` and `testpypi` GitHub
Environments exist on `benbrastmckie/ModelChecker` (created 2026-08-12, no protection rules
configured on either) — confirmed read-only via `gh api repos/benbrastmckie/ModelChecker/
environments`. This checklist does not re-verify that state; only the PyPI-side trusted-publisher
registration above remains open.

**Consequence of skipping this step**: pushing the `v1.3.0` tag still triggers
`.github/workflows/release.yml`'s `test-and-release` and `build` jobs, which run to completion
regardless (they cost real CI time either way). `publish-testpypi` runs with
`continue-on-error: true`, so a missing TestPyPI trusted publisher fails **softly** and does not
block the pipeline. `publish-pypi`, however, has no such tolerance: it fails at the OIDC token
exchange with PyPI, **after** the `test-and-release` and `build` jobs have already spent their CI
time — i.e. skipping this step does not fail fast, it fails late and wastes the run. Confirm this
gate before tagging, not after a failed run.

## 1. Pre-Flight Checks (already verified this round)

- [x] **Fresh rehearsal evidence, all hard gates green.** `bash code/scripts/release-verify.sh
      --ref 1.2.12 --out specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/` exited
      **0**. Every `gate`-class step in `rehearsal/summary.txt` is `exit=0`, including
      `d1-wheel-contents` — bare `check-wheel-contents` is clean, no `W002` finding (the
      duplicate `theory_lib/*/VERSION` files that previously triggered it are gone).
      `twine-check.txt` shows **PASSED** for both the wheel and the sdist.
  - Fresh sha256sums (`rehearsal/sha256sums.txt`), superseding both the archived task-125 hashes
    (`f85e6512...` / `255d2c01...`) and every prior rehearsal's set:
    - New wheel `model_checker-1.3.0-py3-none-any.whl`:
      `5d9d8d5f8895b733fd05b89e0dc3ab65e711ea029105e9d76788e94e39c9aa4c`
    - New sdist `model_checker-1.3.0.tar.gz`:
      `bc421583678950f36782cd6004ac1d9d3ca103f1eddc4815fc6a42663d97d3f0`
  - Note: wheel/sdist builds are not byte-reproducible on this toolchain — an independent rebuild
    of the identical source tree will very likely produce **different** hashes than the two
    above. That is expected; the hashes above identify this specific evidence run, not a fixed
    target every future build must match.
  - Wheel-vs-1.2.12 parity diff (`rehearsal/parity-diff.md`, `wheel-files-diff.txt`,
    `top-level-dir-diff.txt`): 514 files (1.2.12) vs. 474 files (1.3.0). The diff is large and
    fully explained by the core/theory_lib boundary refactor landed since the 1.2.12 release: a
    new top-level `model_checker/solver` package (with its own tests), relocated modules (e.g.
    `builder/z3_utils.py` -> `iterate/z3_utils.py`), and removed stray `.ipynb_checkpoints/`
    notebook-checkpoint files that had been shipping by accident. No `oracle/`, `specs/`, or other
    unexpected content appears in the new wheel.
- [x] **`nix flake check` verdict: PASS, on a confirmed-quiet host.** Host load average was
      0.76/1.05/1.31 (24-core machine) at run time — well under the 4.84 load average recorded
      for the documented contended baseline. `all checks passed!` — neither known
      contention-sensitive test failed: `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`
      and `test_iteration_via_iterate_api` (today's earlier contended-run failure) both passed
      clean. No `max_time` hardening was needed or applied. See the plan's Phase 5 notes for the
      full verdict record, including a git-dirty-tree caveat (only task-management artifacts
      outside `flake.nix`'s `src = ./code` derivation input were dirty at run time — release-
      irrelevant).
- [x] **Version literals agree at `1.3.0`.** `code/pyproject.toml:9`, `flake.nix:25`,
      `flake.nix:137`, and `code/CHANGELOG.md`'s `## [1.3.0]` heading all agree. No `v1.3.0` git
      tag exists yet (`git tag -l "v1.3.0"` is empty) — this will be the first-ever publish of
      this version number, which is why the CHANGELOG entry was expanded in place rather than
      superseded by a new version bump.
- [x] **`.github/workflows/release.yml` and `.github/RELEASE_SETUP.md` reviewed**: OIDC Trusted
      Publishing job graph (`test-and-release` -> `build` -> `publish-testpypi` ->
      `publish-pypi` -> `github-release`), no stale `PYPI_API_TOKEN` references, no casing bugs.
      `RELEASE_SETUP.md`'s "Local Rehearsal (No Publish)" section now correctly describes bare
      `check-wheel-contents` as the hard gate.

**If any commit has touched `code/src` since this evidence was captured** (commit
`1655b99d8ecfacbb0430812ff7bafb844ea2d3cf`, 2026-08-12), **re-run the rehearsal immediately
before tagging** — this evidence set is not one-and-done:
```bash
bash code/scripts/release-verify.sh --ref 1.2.12
```

## 2. One-Time OIDC Setup (skip if Section 0 is already fully checked)

Full instructions: `.github/RELEASE_SETUP.md` (`Trusted Publishing (OIDC) Setup` section). In
outline, all **USER-ONLY**:

- [ ] Register a PyPI trusted publisher (Section 0 above has the exact values).
- [ ] Register a TestPyPI trusted publisher (optional, for the rehearsal job).
- [x] Create the `pypi` and `testpypi` GitHub Environments — **already done** (confirmed present,
      no protection rules, both created 2026-08-12).

## 3. Ordered Release Steps (all USER-ONLY)

1. [ ] Push any outstanding commits from this task's branch to the remote default branch (or land
       them via `/merge`, itself a user-invoked command):
       ```bash
       git push origin master
       ```
2. [ ] Create and push the annotated version tag:
       ```bash
       git tag -a v1.3.0 -m "Release 1.3.0"
       git push origin v1.3.0
       ```
       Do not invoke `/tag` for this — `/tag` is available but this checklist documents the raw
       commands so the exact tag content is under direct control.
3. [ ] The tag push triggers `.github/workflows/release.yml` automatically. Watch it at
       https://github.com/benbrastmckie/ModelChecker/actions:
       - `test-and-release` (cross-platform test matrix) must pass first.
       - `build` builds the wheel/sdist once and runs `twine check --strict`.
       - `publish-testpypi` publishes to TestPyPI via OIDC (`continue-on-error: true`).
       - `publish-pypi` publishes to production PyPI via OIDC. **This is the point of no return**
         for this version number on the index (`skip-existing: true` makes a re-run safe, but a
         genuinely bad artifact cannot be replaced under the same version — see Rollback below).
       - `github-release` creates the GitHub Release for the tag.
4. [ ] If TestPyPI or PyPI ever require a manual credential-based upload fallback outside the
       automated OIDC workflow, that upload is performed by the user only — no agent runs `twine
       upload` under any circumstance.
5. [ ] Confirm `publish-pypi` succeeded in the Actions run before treating the release as live.

## 4. Post-Publish Verification Runbook (USER, after `publish-pypi` succeeds — not yet executable)

Nothing is published yet, so none of this can be executed by this task. It is written here as a
copy-paste runbook for the user to run once `publish-pypi` has succeeded.

```bash
# 1. Confirm the version is live on PyPI
pip index versions model-checker
# expect: 1.3.0 (and 1.2.12) in the version list

# 2. Install FROM PyPI into a clean venv -- never from local dist/
python3 -m venv testvenv
PIP_USER=0 ./testvenv/bin/pip install model-checker

# 3. NixOS recipe: z3-solver's compiled extension needs libstdc++ on the
#    loader path, which a NixOS system does not expose by default outside a
#    devShell. Export it before running anything that imports z3:
export LD_LIBRARY_PATH="$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib"

# 4. Generate and run a project for EACH of the four registered theories,
#    expecting 4/4 exit 0:
for theory in logos exclusion imposition bimodal; do
  ./testvenv/bin/model-checker -l "$theory" "/tmp/verify-$theory"
  LD_LIBRARY_PATH="$LD_LIBRARY_PATH" ./testvenv/bin/model-checker "/tmp/verify-$theory/examples.py"
  echo "theory=$theory exit=$?"
done
```

**Incidental `z3-solver` note**: `pyproject.toml` floors `z3-solver` at `>=4.8.0` with no upper
pin. `pip` is expected to resolve **`5.0.0.0`** (well beyond the floor) when installing into a
fresh venv today. This was confirmed during research as an incidental finding, not acted on — add
an upper pin **only if** the post-publish verification above actually breaks under `5.0.0.0`.
Confirm, do not pre-emptively pin.

## Summary: What the Agent Never Does

Per `.claude/rules/pr-prohibition.md`, no agent involved in this task performs any of the
following — all of it is exclusively the user's action:

- `git push` (branch or tag, any form)
- `git tag` followed by a push of that tag
- Creating a pull/merge request, or invoking `/merge`
- Uploading to TestPyPI or PyPI via `twine upload` or any other credentialed method
- Configuring PyPI/TestPyPI trusted publishers or GitHub Environments
- Invoking `/tag`

This task's agent work ends at the pre-flight/rehearsal evidence and this checklist. Everything
from "push the branch" onward in Section 3 is performed by the user.

## Rollback / Contingency

- Nothing in this task reaches a remote or a package index, so no rollback of a published
  artifact is ever needed as a result of this task's own work.
- If the user publishes and a defect is found post-publish, PyPI does not permit re-uploading the
  same version number — the remedy is a new patch release (e.g. `1.3.1`), which is outside this
  checklist's scope.

## References

- `.github/RELEASE_SETUP.md` — full OIDC Trusted Publishing setup and workflow overview, and the
  corrected "Local Rehearsal (No Publish)" section.
- `.github/workflows/release.yml` — the release pipeline itself.
- `code/scripts/release-verify.sh` — the pinned local rehearsal runner (corrected gate contract).
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/rehearsal/parity-diff.md` — this round's
  local rehearsal evidence and parity diff against `model-checker==1.2.12`.
- `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` — the structural
  template this checklist is derived from (data superseded; structure reused).
- `.claude/rules/pr-prohibition.md` — the standing prohibition on agent push/PR/publish actions.
