# Research: Harden Release CI / TestPyPI Gate

**Date (UTC)**: 2026-08-31
**Dependency status**: task 161 (`fix_testpypi_trusted_publisher`) is `completed`. Verified live:
`publish-testpypi` job conclusion is `success` (not merely masked by `continue-on-error`) on the
`v1.3.7` tag push (Actions run 32996862484, 2026-08-26T17:55Z), and on `v1.3.4`-`v1.3.6` before it.
Item (2)'s "INPUT NOW SATISFIED" note in the task description is current and confirmed — safe to
land item (1)(a)'s hard gate.

## Scope covered

All eleven numbered items in the task description were re-verified against the current tree
(2026-08-31). Two items are **materially stale** relative to their original framing (see items 3
and 6 below) — plan around the corrected premise, not the original text. Items 9-12 are
out-of-scope here (discharged / superseded by other tasks) and were not re-investigated beyond
confirming the state.json note is accurate.

## (1) Make TestPyPI a real gate

Current `.github/workflows/release.yml` (`publish-testpypi` job, lines 136-196):
- `continue-on-error: true` at line 147, with a comment (lines 143-146) documenting the
  deliberate soft-canary tradeoff.
- `publish-pypi` (line 198) has `needs: [build, publish-testpypi]` — because of
  `continue-on-error`, a failed `publish-testpypi` still reports `success` to `needs:`, so this
  gate is currently a no-op.
- The task 161 OIDC-claims diagnostic step (lines 161-184) is already in place and unrelated to
  this item; do not touch it beyond re-reading around it.

**(a) Drop `continue-on-error`, add `skip_testpypi` escape.** Straightforward: remove line 147;
add a `workflow_dispatch:` input block to the `on:` section (currently only `push: tags:`, lines
4-7) with `skip_testpypi` (boolean, default `false`), and gate the publish-testpypi job's steps
(or the whole job, via `if:`) on `${{ github.event_name != 'workflow_dispatch' || !inputs.skip_testpypi }}`.
Since the trigger is normally a tag push (not workflow_dispatch), `inputs.skip_testpypi` needs a
null-safe read — use `${{ inputs.skip_testpypi != true }}` form, since `inputs` is only populated
under a `workflow_dispatch` trigger and evaluates false/empty otherwise in expression context (GitHub
Actions treats an unset `inputs.x` as empty string, which is falsy in `!=  true` but confirm this
in a syntax-only local render before relying on it — this is the one part of item (1)(a) worth a
dry-run, since a real tag-push trigger is user-only and cannot be rehearsed by an agent).

**(b) Add `verify-testpypi` job.** New job between `publish-testpypi` and `publish-pypi`:
- `needs: [test-and-release, build, publish-testpypi]`, no special permissions needed (only
  installs from an index, no OIDC).
- Install command must supply both indexes since TestPyPI does not mirror dependencies:
  `pip install --index-url https://test.pypi.org/simple/ --extra-index-url https://pypi.org/simple/ "model-checker==${VERSION}"`.
  `VERSION` must come from the same `steps.version.outputs.version` pattern already used in
  `test-and-release` (lines 36-42) — re-derive it via `${GITHUB_REF#refs/tags/v}` in this job
  too (job outputs aren't shared automatically; either add a `version` output to
  `test-and-release` and reference it via `needs.test-and-release.outputs.version`, or
  re-derive locally — the existing code has no precedent for cross-job outputs, so re-deriving
  locally is the lower-diff choice and avoids introducing a new `outputs:` block).
- **Pin to the exact tag version explicitly**, never "latest" — test.pypi.org has a stale `0.1`
  release from a pre-CI manual upload still live (confirmed relevant to any bare
  `pip install model-checker` without `==`).
- Wrap the install in a bounded retry (index propagation lag). No existing retry-loop idiom is
  present anywhere in this repo's workflows or `code/scripts/*.sh` to reuse — this will be a new
  pattern. A plain `for i in $(seq 1 10); do ... && break; sleep 15; done` plus a final
  exit-code check (fail the step if the loop's last attempt also failed) is consistent with this
  repo's existing bash style (`set -uo pipefail`, no external retry actions).
- Smoke test, minimum bar per the task text: import + `__version__` equality check + `model-checker --help`.
  `model-checker --help` currently works non-interactively already (argparse `-h`/`--help` exits
  0 without touching `ask_generate()`), so this part needs no dependency on item (4). Extending
  to the four-theory golden path (mentioned as a stretch goal) DOES depend on item (4) landing
  first — sequence item (4) before extending verify-testpypi's smoke test, or land the minimum
  bar now and treat the golden-path extension as follow-up.
- Change `publish-pypi`'s `needs:` from `[build, publish-testpypi]` to
  `[build, verify-testpypi]` (dropping the direct `publish-testpypi` dependency is fine since
  `verify-testpypi` already transitively depends on it).

**(c) Environment protection rule.** Confirmed via `gh api repos/benbrastmckie/ModelChecker/environments`:
both `pypi` and `testpypi` environments exist with `"protection_rules":[]` (empty) as of this
research. Adding a required-reviewer rule is pure GitHub web-UI configuration — no workflow file
change, not agent-authorable. Surface as a user decision point in the plan; do not attempt to
script it (there is a REST endpoint for environment protection rules, but per
`.claude/rules/pr-prohibition.md` and this task's own "AGENT CONSTRAINT" paragraph, environment
protection changes are explicitly named as user-only web-UI work).

## (2) Prerequisite dependency — confirmed satisfied, no action

Already covered above. No further work needed on the trusted-publisher registration itself.

## (3) Preflight job — CORRECTED SCOPE (flake.nix drift claim is stale)

The task text says three independently-drifting literals need checking: tag vs.
`code/pyproject.toml` version, `flake.nix:25`, `flake.nix:137`. **This is no longer true.**
`flake.nix` line 21 now reads:
```nix
version = (builtins.fromTOML (builtins.readFile ./code/pyproject.toml)).project.version;
```
committed in `8252fe74 build(nix): derive flake version from code/pyproject.toml`, whose own
commit message and in-file comment (`flake.nix:15-20`) state this was fixed specifically because
two hardcoded copies previously drifted (both sat at 1.3.0 across the 1.3.1 release). There is no
longer a second or third independently-editable version literal in `flake.nix` — `version` is
derived, so it cannot drift from `code/pyproject.toml` by construction. `flake.nix:25` and
`flake.nix:137` (the specific lines the task text names) are now unrelated comment lines (Z3
binding note and pytest `-n 4` rationale respectively) — the line numbers have shifted from
whatever revision the task description was written against.

**Corrected preflight scope**: only TWO independent checks remain meaningful for the
tag-vs-source-of-truth comparison:
1. Tag version (from `$GITHUB_REF`) equals `code/pyproject.toml`'s `version =` (line 11,
   currently `1.3.7`). `flake.nix` needs no separate check — it inherits this transitively by
   construction and re-checking it would be redundant, not defense-in-depth (it reads the exact
   same file).
2. `code/CHANGELOG.md` has a non-empty entry for the version being released.

**CHANGELOG check has a live blocker worth flagging to the plan/user**: `code/CHANGELOG.md`'s
newest entry is `## [1.3.2] - 2026-08-12` (line 9); `## [Unreleased]` (line 7) is empty. Current
`code/pyproject.toml` version is `1.3.7`. **Every release from 1.3.3 through 1.3.7 shipped with
zero CHANGELOG entry.** A preflight gate enforcing "non-empty CHANGELOG entry for the version
being released" is correct policy going forward, but implementing it now means the very next
tagged release (whatever version follows 1.3.7) will be BLOCKED by this new gate unless a
CHANGELOG entry is added for it first — this is the gate doing its job, not a bug, but it is a
real, immediate operational consequence the plan and the user should be told about explicitly
rather than discovering at tag time.

3. Annotated-tag-reachable-from-default-branch check: no existing precedent in this repo's
   scripts to reuse (grepped `code/scripts/*.sh` for `git cat-file -t`/`git describe` —
   none found). New code: `git cat-file -t "$GITHUB_REF_NAME"` should report `tag` (not
   `commit`, which would mean a lightweight tag) and
   `git merge-base --is-ancestor "$GITHUB_REF_NAME" origin/master` (or the actual default branch
   name — confirm it's `master`, matches `git branch` output already seen in this session) should
   exit 0.

Placement: a new `preflight` job with `needs: []` (runs first, no matrix, single ubuntu-latest
runner, `actions/checkout@v4` with `fetch-depth: 0` — required for both the CHANGELOG grep and
the tag-ancestry check, since the default shallow checkout won't have full history or all tags).
`test-and-release`'s `needs:` should gain `preflight` so the expensive 9-job matrix never starts
before these seconds-cheap assertions pass.

## (4) Non-interactive project generation

Confirmed exact defect. `code/src/model_checker/__main__.py` `main()` (lines 239-297):
```python
if len(sys.argv) < 2:
    builder = BuildProject()
    builder.ask_generate()
    return
...
if module_flags.load_theory:
    semantic_theory_name = module_flags.load_theory
    builder = BuildProject(semantic_theory_name)
    builder.ask_generate()
    return
```
`_create_parser()` (same file, ~line 60-70) registers only ONE positional argument, `file_path`
(`nargs='?'`), which is used elsewhere for the "run an examples file" mode. When `-l THEORY DIR`
is passed, argparse binds `DIR` to `module_flags.file_path` — but the `if module_flags.load_theory:`
branch never reads `module_flags.file_path` at all before calling `ask_generate()`, confirming
the task's claim that the directory argument is silently discarded.

`ask_generate()` (`code/src/model_checker/builder/project.py:152-172`) calls `input()` twice
(lines 159, 165); `_handle_example_script()` (called from `ask_generate()`'s success path) calls
`input()` a third time (line 706). All three are unconditional — no existing env-var or CLI escape.

**The underlying `generate(name, destination_dir=None)` method (project.py:174-215) is already
fully non-interactive** — it takes the name and an optional destination directly and does no I/O
prompting itself. The fix is additive at the CLI layer, not a rewrite of `BuildProject`:
- Add `-y`/`--yes` (or equivalent) plus reuse `file_path` (already parsed) as the destination
  directory when `--load_theory` is set, and add a project-name argument (new, since today
  nothing carries a name when `-l` is used — `ask_generate()`'s second prompt is the only place
  a name is ever collected). Two viable shapes: (i) a new `--project_name`/`-p NAME` argument, or
  (ii) treat `file_path` as `<name>` when a bare name is given and `-y` is set, defaulting
  `destination_dir` to cwd — pick whichever matches this project's existing flag-naming
  conventions (`code/src/model_checker/__main__.py`'s existing groups use long name + short
  single-letter alias consistently, e.g. `--load_theory/-l`, `--contingent/-c`).
- Call `builder.generate(name, destination_dir)` directly instead of `ask_generate()` when the
  non-interactive flag is set, and `sys.exit(1)` (not merely `return`) if required info (a name)
  is missing under `-y`, per the task's "exit non-zero on any prompt that would block" requirement.
- `_handle_example_script()`'s prompt (project.py:706) should also be skippable under the same
  `-y` flag — either short-circuit it entirely (print the "you can test your project by running"
  message unconditionally) or accept a `run_example: bool = False` parameter threaded from the
  CLI flag.

This is a prerequisite for extending item (1)(b)'s smoke test to the four-theory golden path, and
is independently a real usability fix (confirmed EOFError failure mode is real and matches the
described 1.3.0 verification incident).

## (5) JSON API vs. simple index for post-publish verification

**Scope correction**: `.github/RELEASE_SETUP.md` (this task's actual file_scope) does **not**
currently contain any "pip index versions" recommendation — grepped the full file, zero hits. The
recommendation lives instead in `code/docs/development/PYPI_RELEASE_GUIDE.md:149`
(`pip index versions model-checker`, in a "Check latest version on PyPI" snippet) — **this file is
NOT in task 158's declared file_scope**. Also present in two archived task checklists
(`specs/archive/125_.../PUBLISH-CHECKLIST.md:98`, `specs/archive/151_.../PUBLISH-CHECKLIST.md:137`)
which are historical artifacts, not live documentation, and should not be edited.

Two consequences for planning:
- If any NEW automated post-publish JSON-API verification step is added (e.g. inside
  `verify-testpypi`, or a new post-`publish-pypi` step), write it against
  `https://pypi.org/pypi/model-checker/json` (production) and/or
  `https://test.pypi.org/pypi/model-checker/json` (TestPyPI has an equivalent JSON endpoint at
  the same path shape on its own host) with a bounded retry, matching the pattern chosen for
  item (1)(b).
- The stale "pip index versions" advice's actual live location (`PYPI_RELEASE_GUIDE.md`) is
  outside this task's file_scope. Either flag it to the user as a follow-up/out-of-scope note in
  the plan (recommended — file_scope is a deliberate declared boundary and this file wasn't
  included), or explicitly ask the user whether to widen scope. Do not silently edit a file
  outside file_scope.

## (6) Gitignore orchestrator runtime files — CORRECTED SCOPE, plus one adjacent live discrepancy

Re-verified against `.claude/context/standards/orchestrator-runtime-files.md` (the canonical
policy this item cites) and the current `.gitignore` (34 lines) / tracked-file state:

- `.orchestrator-multi-state*.json` **is** already gitignored (`.gitignore:36-37`). Confirmed
  correct as the task text states — no action.
- `.orchestrator-loop-guard` is **not** gitignored, and the standard's recommended consumer-repo
  block explicitly includes `**/.orchestrator-loop-guard` in the ephemeral (must-ignore) class.
  Confirmed **6 tracked instances** via `git ls-files | grep orchestrator-loop-guard`:
  - `specs/161_fix_testpypi_trusted_publisher/.orchestrator-loop-guard` (active task dir)
  - `specs/archive/096_investigate_perpetuity_validity_alignment/.orchestrator-loop-guard`
  - `specs/archive/097_optimize_build_frame_constraints/.orchestrator-loop-guard`
  - `specs/archive/107_boundary_temporal_depth_mitigation/.orchestrator-loop-guard`
  - `specs/archive/112_fold_unfold_formula_normalization/.orchestrator-loop-guard`
  - `specs/archive/113_enriched_operator_equivalence_tests/.orchestrator-loop-guard`
  Correct remediation per the standard's "Untracking Already-Committed Ephemeral Files" section:
  add `**/.orchestrator-loop-guard` to `.gitignore`, then `git rm --cached` each of the 6 paths
  above (working-tree copies untouched).
- `.return-meta-multi-*.json`: the task's open question ("confirm whether it needs an entry") is
  already answered — `.gitignore:34-35` cover both `**/.return-meta-multi.json` and
  `**/.return-meta-multi-sess_*.json`. No action needed; confirm-and-close in the plan rather than
  re-adding.

**Adjacent discrepancy found, NOT named in the task's item (6), worth flagging explicitly**: the
standard states in two places — "Explicit prohibition: never run this against
`.orchestrator-handoff.json` or `.return-meta.json`... never ignored" and the recommended
consumer-repo `.gitignore` block's own comment ("Deliberately does NOT include
`.orchestrator-handoff.json` or `.return-meta.json`") — that the **bare**
`.return-meta.json` (as opposed to the suffixed `.return-meta-multi*.json` variants) must stay
tracked as durable per-dispatch provenance. This repo's actual `.gitignore:33` currently reads
`**/.return-meta.json`, which **does** ignore the bare form, contradicting the standard.
Confirmed live: `git check-ignore -v specs/158_harden_release_ci_testpypi_gate/.return-meta.json`
returns a match on `.gitignore:33`. This task's file_scope includes `.gitignore`, and this line is
immediately adjacent to the other lines item (6) does ask about, but the task description itself
never raises this specific line — it is a new finding from this research pass, not part of the
original item (6) text. Recommend surfacing it to the user/plan as an explicit decision point
(remove the bare pattern to align with the standard, or leave as-is if there's a reason this repo
deliberately diverges) rather than silently changing it as if it were already in scope, and
definitely without touching the two already-in-scope suffixed patterns.

## (7) Workflow-file ordering hazard documentation

No code change — a documentation addition to `.github/RELEASE_SETUP.md`'s "Release Process"
section (lines 74-90). Current text (steps 1-4) does not mention the tag-vs-push ordering hazard
at all. Add an explicit note: push the branch (or land via `/merge`) BEFORE creating/pushing the
tag, because Actions executes the workflow file as it exists at the tagged commit, and an
unpushed local fix can silently "resolve correctly" only by accident of push-ordering, as observed
during the 1.3.0 release (uncommitted `pip install build twine` → `... wheel` fix). Also cross-
reference item (3)'s preflight job as the mechanical backstop, if the plan lands the "tagged
commit's release.yml matches default branch's" assertion mentioned in the task text — this can
be folded into the same `preflight` job as: fetch `origin/master`'s copy of
`.github/workflows/release.yml` at the tag's parent-branch tip and diff against the tagged
commit's copy (both are available once `fetch-depth: 0` is set for item (3)'s ancestry check, so
this is a low-incremental-cost addition to the same job rather than a new one).

## (8) Rehearsal-evidence freshness check

`code/scripts/release-verify.sh` (full file read, 527 lines) writes an evidence set (`build.log`,
`twine-check.txt`, `wheel-contents.txt`, etc., `summary.txt` ledger) but records **no commit SHA**
anywhere in its output today — `summary.txt`'s header (lines 176-182) writes `started (UTC)`,
`REF`, `OUT_DIR`, nothing else identifying the tree state the evidence was captured against.
Two-part fix per the task text:
1. Have `release-verify.sh` record the commit it ran against — add `git rev-parse HEAD` (or
   `--short HEAD`) to the `summary.txt` header block (around line 176-182, alongside the existing
   `started`/`REF`/`OUT_DIR` lines) and probably also stamp it into `parity-diff.md`'s header
   (lines 443-455) for the same reason the other identity fields live there.
2. Add a companion check — either a manual documented step or (better, matching this task's
   general "make manual checklist steps mechanical" theme) a preflight assertion — that runs
   `git log <evidence-commit>..HEAD -- code/src` and fails/warns if non-empty, meaning
   `code/src` changed since the evidence was captured. This needs the evidence commit to be
   discoverable at preflight time; since `release-verify.sh`'s output isn't committed to the repo
   (it's `/tmp` or a user-chosen `--out DIR`, both outside version control), this can only be a
   **documented manual step** unless the evidence commit SHA is separately recorded somewhere
   version-controlled (e.g. appended to a checklist file at rehearsal time) — flag this
   discoverability gap to the plan: full automation of item (8) requires deciding where the
   evidence-commit record persists past the ephemeral `--out DIR`, which is a design decision,
   not just an implementation detail.

## File-scope cross-check

All eight declared file_scope entries were read and are implicated by at least one item above:
`.github/RELEASE_SETUP.md` (items 1c pointer, 7), `.github/workflows/differential-tests.yml`
(read for `not unstable` marker context per the CONCURRENCY note — no direct edit identified),
`.github/workflows/packaging.yml` (read for context — no direct edit identified),
`.github/workflows/release.yml` (items 1, 3), `.github/workflows/tests.yml` (read for context —
no direct edit identified), `.gitignore` (item 6), `code/pyproject.toml` (item 3, version source
of truth — read only, no edit expected unless CHANGELOG-bump-adjacent), `code/scripts/release-verify.sh`
(item 8), `code/src/model_checker/__main__.py` (item 4), `code/src/model_checker/builder/project.py`
(item 4), `flake.nix` (item 3 — confirmed NO edit needed, see correction above).

`differential-tests.yml`, `packaging.yml`, and `tests.yml` appear in file_scope per the
CONCURRENCY note (shared pytest-selection-expression territory with the `development`-marker
task) but this task's own scope (items 1, 3-8) does not require editing any of the three directly
— no `-m` marker expression change is called for by anything in items 1-8. Plan should either
confirm this (no edit) explicitly or explain what, if anything, in the eventual plan touches them.

## Recommendations for the plan

1. Sequence: (4) non-interactive CLI first (small, self-contained, unblocks smoke-test
   extension) → (1a) drop continue-on-error + skip flag → (1b) verify-testpypi job → (3) preflight
   job (folds in the corrected 2-literal check + CHANGELOG + tag-ancestry + optionally the item-7
   workflow-file-match check) → (6) gitignore + untrack → (7) doc-only addition → (8) evidence
   commit recording. (1c) and the `.return-meta.json` bare-pattern discrepancy from item (6) are
   both user-decision flags, not agent-executed code changes — surface them explicitly rather than
   defaulting either way.
2. The CHANGELOG-gap consequence (item 3) and the file_scope gap for PYPI_RELEASE_GUIDE.md
   (item 5) should both be stated plainly to the user before/alongside the plan, since both affect
   what "done" means for their respective items without requiring new research.
