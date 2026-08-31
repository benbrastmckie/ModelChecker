# Implementation Summary: Harden release CI / TestPyPI gate

- **Task**: 158 - Harden release CI / TestPyPI gate
- **Plan**: `specs/158_harden_release_ci_testpypi_gate/plans/01_harden-testpypi-gate.md`
- **Status**: All 8 phases COMPLETED
- **Session**: sess_1788198229_79cf9f

## What Changed

1. **Non-interactive project generation** (`code/src/model_checker/__main__.py`,
   `code/src/model_checker/builder/project.py`): added `-y`/`--project_name` (`nargs='?'`,
   `const=''`) to the parser. Combined with `--load_theory`, it branches directly to
   `builder.generate(name, destination_dir)` -- no `input()` call anywhere on this path -- and
   `sys.exit(1)` with an actionable message when the flag is present but no name was given.
   `_handle_example_script()` gained an `interactive: bool = True` parameter; the non-interactive
   path calls it with `interactive=False`, which prints the "how to run" message and returns
   without ever calling `input()`. The existing positional `file_path` argument, previously bound
   but unused in the `--load_theory` branch, is now read as the destination directory. The
   interactive path (`ask_generate()`) is untouched -- `interactive` defaults to `True`.

   **Design choice recorded** (plan's out-of-scope flag F / Phase 1 task 3): the project name is
   carried directly by `-y`'s value (`-l bimodal -y my_project`), and the destination directory
   is the pre-existing positional argument. This was chosen over adding a second explicit `--name`
   flag because it reuses an argument slot that already existed but was silently discarded,
   keeping the diff smaller.

2. **Hard TestPyPI gate** (`.github/workflows/release.yml`): removed `publish-testpypi`'s
   job-level `continue-on-error: true` (the OIDC diagnostic step's own `continue-on-error` is
   untouched -- correctly scoped to a diagnostic). Added `workflow_dispatch` with a boolean
   `skip_testpypi` input (default `false`) as an escape hatch.

   **Deviation from the plan's literal `if:` text**: the plan named the exact form
   `${{ inputs.skip_testpypi != true }}`. Implemented as `${{ success() && inputs.skip_testpypi
   != true }}` instead, because a job-level `if:` **replaces** GitHub Actions' implicit
   `if: success()` default rather than layering on top of it -- the literal form would let
   `publish-testpypi` attempt to run even after `test-and-release`/`build` failed.

3. **`verify-testpypi` job**: installs the just-published TestPyPI artifact
   (`--index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/
   "model-checker==${VERSION}"`, both indexes, exact-version pin) with a bounded 10-attempt/15s
   retry for index propagation lag, then smoke-tests import + `__version__` equality +
   `model-checker --help`. `publish-pypi`'s `needs:` now points at `verify-testpypi` instead of
   `publish-testpypi` directly.

   `verify-testpypi` carries its own explicit `if:` (see the job comment in `release.yml`) that
   requires `test-and-release`/`build` to have succeeded AND either `publish-testpypi` succeeded
   or was skipped specifically because `skip_testpypi` was set. Each verification step inside the
   job additionally carries `if: ${{ inputs.skip_testpypi != true }}`, so in the escape-hatch case
   the job runs but every step no-ops -- reporting success without attempting to verify an
   artifact that was never uploaded -- which lets `publish-pypi`'s own default `if: success()`
   pass through unmodified. This is the mechanism that makes `skip_testpypi` actually work
   end-to-end; it goes beyond the plan's literal task list (which only names repointing
   `publish-pypi`'s `needs:` edge) but is necessary for the phase's own stated goal.

4. **`preflight` job**: seconds-cheap, no matrix, `fetch-depth: 0` checkout, runs first. Asserts
   (a) tag version == `code/pyproject.toml`'s `version` (confirmed exactly two independent
   literals exist, not three -- `flake.nix` derives its version from the same TOML file and was
   not touched); (b) `code/CHANGELOG.md` has a non-empty `## [X.Y.Z]` entry for the release
   version, with a failure message naming both the file and version; (c) the tag is annotated
   (`git cat-file -t` reports `tag`) and reachable from `origin/master`; (d) the tagged commit's
   `release.yml` matches `origin/master`'s copy (the mechanical backstop for the ordering hazard
   in item 5 below). `test-and-release` now `needs: preflight`.

5. **`.gitignore` / orchestrator loop-guard files**: added `**/.orchestrator-loop-guard`,
   adjacent to the other orchestrator-runtime entries. Untracked the 6 currently-tracked files
   (`git rm --cached`, working-tree copies preserved) -- confirmed count matched the plan's scope
   hypothesis exactly (1 under `specs/161_.../`, 5 under `specs/archive/`). `.gitignore:33`'s
   `**/.return-meta.json` was deliberately left untouched (out-of-scope flag D).

6. **`.github/RELEASE_SETUP.md`**: documented the push-before-tag ordering hazard (citing the
   1.3.0 `pip install build twine` -> `... wheel` incident concretely) and `preflight`'s
   workflow-match assertion as its mechanical backstop; the new 7-job gate topology; the
   `skip_testpypi` escape hatch and when it's legitimate; the CHANGELOG preflight requirement;
   the `pypi` environment protection-rule decision (flag A); and a JSON-API
   (`https://pypi.org/pypi/model-checker/json`) post-publish verification note (in this file
   only -- `PYPI_RELEASE_GUIDE.md:149`'s actual stale `pip index versions` advice was left
   untouched, flag C). Also corrected now-stale `continue-on-error`/five-job-topology references
   elsewhere in the same file for internal consistency.

7. **`code/scripts/release-verify.sh`**: stamped `git rev-parse HEAD` into both `summary.txt`'s
   and `parity-diff.md`'s header blocks. Documented the companion freshness check
   (`git log <evidence-commit>..HEAD -- code/src` must be empty) in `--help` output, and why it's
   manual: the evidence directory lives outside version control, so there's nowhere durable for
   an automated check to read the recorded commit back from.

## Out-of-Scope Flags -- Final Status

| # | Flag | Status |
|---|------|--------|
| A | Required-reviewer protection on the `pypi` GitHub Environment | Not executed (web-UI-only). Documented in `RELEASE_SETUP.md` as an open decision; both `pypi`/`testpypi` still have empty `protection_rules` |
| B | CHANGELOG gate blocks the next release | Confirmed: `code/CHANGELOG.md` has no `## [1.3.7]` entry; `preflight`'s local exercise reproduced the miss (expected, gate working correctly). Documented in `RELEASE_SETUP.md`'s Release Process step 1 |
| C | `PYPI_RELEASE_GUIDE.md:149`'s stale `pip index versions` advice | Not edited (outside file_scope). `RELEASE_SETUP.md` instead documents the JSON-API alternative |
| D | `.gitignore:33`'s `**/.return-meta.json` contradicts the orchestrator-runtime-files standard | Left untouched, as decided in the plan |
| E | Extending `verify-testpypi` to the four-theory golden path | Not implemented; minimum-bar smoke test only (import + version + `--help`) |
| F | Phase 1 test files outside declared file_scope | Proceeded per the plan's stated assumption (tests are a corollary of the in-scope source edit); also touched two further pre-existing CLI-coverage test files (`code/tests/cli/test_flag_matrix.py`, `code/tests/cli/test_parse_file_flags.py`) that hardcode flag-count/coverage assertions and would otherwise fail red on the new flag -- same rationale as flag F |

## Unrehearsable Blind Spots

- **Phase 2/3**: the `skip_testpypi` expression's and `verify-testpypi`'s runtime behavior under
  a real `push: tags:` trigger cannot be exercised by the implementer (`git push`/`git tag` are
  user-only). Verified by static/syntax review, YAML parsing, and job-graph inspection only.
- **Phase 3**: the retry loop's real behavior against TestPyPI's actual index-propagation lag is
  unrehearsable here.
- **Phase 4**: the tag-ancestry and workflow-file-match assertions need CI's real checkout
  context; verified by review only. The version-comparison and CHANGELOG-grep logic *were*
  exercised locally against the current tree (see below).

## Locally Exercised Results

- Tag-vs-`pyproject.toml` comparison (v1.3.7): MATCH.
- CHANGELOG check (v1.3.7): MISS (no `## [1.3.7]` heading) -- expected, this is flag B firing
  correctly, not a defect.
- `release-verify.sh` full run (bypassing the `nix develop` re-exec via
  `RELEASE_VERIFY_IN_SHELL=1` since the pinned tools were already resolvable): exit 0,
  `FAILURES=0`, all hard gates green; `COMMIT=` matched `git rev-parse HEAD` exactly in both
  `summary.txt` and `parity-diff.md`. A second run on the unchanged tree also exited 0.

## Test Results

`PYTHONPATH=code/src pytest code/tests/ -q` -> **566 passed, 5 skipped, 0 failed**.

An initial full-suite run surfaced 3 pre-existing bookkeeping-test failures in `code/tests/cli/`
(`test_every_registered_flag_is_covered_or_excluded`, `test_short_to_long_has_fourteen_entries`,
`test_sweep_partition_covers_every_short_to_long_entry`) caused by Phase 1's new flag -- these
tests exist specifically to fail loudly on an unaccounted-for registered flag. Fixed by updating
their accounting sets/counts and adding dedicated `-y`/`--project_name` dispatch and equivalence
tests, mirroring the existing bespoke-check pattern for `-s`/`-u`.

`actionlint` is not installed in this environment; recorded as absent rather than claimed to have
run clean.

## Confirmed No-Edit Claims

`flake.nix`, `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`,
`.github/workflows/packaging.yml`, `code/pyproject.toml`, `code/CHANGELOG.md`, and
`code/docs/development/PYPI_RELEASE_GUIDE.md` are all absent from this task's commits
(`git diff --name-only` scoped to task-158 commits; the three sibling workflow files were last
touched by unrelated, prior tasks per `git log -- <path>`).

## Confirmed: No Push/Tag/Merge/Twine Operations

No `git push`, `git tag`, `/merge`, `/tag`, or twine upload was performed at any point.

## Plan Deviations

1. **Phase 2's `if:` expression**: implemented `${{ success() && inputs.skip_testpypi != true }}`
   instead of the plan's literal `${{ inputs.skip_testpypi != true }}`. See "What Changed" #2
   above for the rationale (a custom job-level `if:` replaces the implicit `success()` check).
2. **Phase 3's `verify-testpypi`/`publish-pypi` interaction**: the plan's task list only names
   repointing `publish-pypi`'s `needs:` edge. Implementing that literally, without
   `verify-testpypi`'s own explicit `if:` (documented in "What Changed" #3), would have made
   `skip_testpypi` non-functional end-to-end (default skip-propagation would cascade through
   `verify-testpypi` and `publish-pypi` even when `publish-testpypi` was deliberately, not
   erroneously, skipped). Added the necessary `if:` logic; `publish-pypi` itself needed no
   change beyond its `needs:` edge, as the plan states.
3. **Phase 6 scope widened within the single in-scope file**: beyond the "Release Process"
   section the task list names, also corrected the "2. TestPyPI Trusted Publisher", "3. GitHub
   Environments", "Workflow Overview", "Common Issues", and "Test Release Workflow" sections of
   the same `.github/RELEASE_SETUP.md` file, which still described the pre-Phase-2 soft-canary
   behavior and five-job topology. Leaving them unedited would have made the file internally
   contradictory.
4. **Phase 8 test fixes widened beyond Phase 1's declared file_scope**: `code/tests/cli/
   test_flag_matrix.py` and `code/tests/cli/test_parse_file_flags.py` (pre-existing files, not
   named in file_scope) required updates to stay green after Phase 1's new flag. Same rationale
   as out-of-scope flag F -- necessary corollary of the in-scope source change, not scope
   widening in spirit.
