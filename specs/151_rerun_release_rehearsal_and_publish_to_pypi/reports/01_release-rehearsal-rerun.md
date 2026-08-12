# Research Report: Re-run the release rehearsal against the post-refactor tree and prepare the release to PyPI

- **Task**: 151 - rerun_release_rehearsal_and_publish_to_pypi
- **Started**: 2026-08-12T17:30:00Z
- **Completed**: 2026-08-12T18:35:00Z
- **Effort**: ~1 hour
- **Dependencies**: 147, 149, 150, 156, 157 (all `[COMPLETED]`)
- **Sources/Inputs**: see Appendix
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: task 156 (`release-verify.sh` runner, now the canonical rehearsal
  method), task 157 (deduped the four `theory_lib/*/VERSION` files, clearing W002), task 155
  (fixed real CI failures — missing `wheel` build dep, two timing-gated tests), tasks 147/149/150
  (stale docs, packaging-contract tests, general CI/flake-check gate).
- **Downstream Dependents**: none — this is the terminal task of the release sequence. The next
  step after this task's implementation phase is the user-only publish sequence.
- **Alternative Paths**: none — one release path (`release.yml` triggered by a `vX.Y.Z` tag).
- **Potential Extensions**: none identified.

## Executive Summary

- **Item (1) is superseded, not merely stale**: task 156 built a pinned, checked-in rehearsal
  runner (`code/scripts/release-verify.sh`) that replaces the archived task's hand-rolled
  sequence; task 151's implementation should invoke that runner, not re-derive the steps by hand.
- **A concrete, already-diagnosed defect exists in `release-verify.sh` and `RELEASE_SETUP.md`**:
  both still assert that bare `check-wheel-contents` returns W002 and must be run with
  `--ignore W002` as the hard gate. Task 157 fixed the underlying duplicate-`VERSION`-file cause;
  this research **independently re-confirms**, via a fresh from-scratch `python -m build` +
  `twine check --strict` + bare `check-wheel-contents`, that the bare run now exits **0** with no
  `--ignore` needed. The two files' stale text and gate assignment must be corrected.
- **Even task 156's own archived rehearsal evidence is now stale a second time**: it was captured
  *before* task 157 landed (its `wheel-contents.txt` still shows the W002 finding), so a fresh,
  officially-archived `release-verify.sh` run is still needed for this task — the same
  "any refactor invalidates the rehearsed evidence" problem the task description opens with has
  recurred one task later, for a different reason.
- **Version/CHANGELOG state is unusually clean**: `pyproject.toml`, both `flake.nix` sites, and
  `CHANGELOG.md` all agree on `1.3.0`; no tag `v1.3.0` exists; `v1.2.12` (matching PyPI's current
  live latest) is the last published tag. 64 commits touched `code/src` (300 total commits) since
  the commit that added the `## [1.3.0]` CHANGELOG entry, including the full core/theory_lib
  refactor (task 126, 24 commits) plus, as of today, tasks 155/156/157. `## [Unreleased]` is
  empty. Recommendation: **fold into 1.3.0** (see Decisions).
- **The PyPI/GitHub Environments gate is now partially cleared, not fully unchecked as the task
  description assumed**: `gh api` (read-only, no PyPI credentials) confirms both `pypi` and
  `testpypi` GitHub Environments now exist on the repository (created 2026-08-12T14:47/14:48Z,
  today), each with no protection rules configured. The PyPI/TestPyPI **trusted-publisher**
  registration itself cannot be confirmed without visiting the PyPI web UI, which this research
  did not do per the task's hard constraint — that half of the gate remains unconfirmed and must
  be verified by the user before tagging.
- **A fresh `nix flake check` completed during this research session and FAILED** — but not with
  the documented `BM_CM_1-example_case7` flake. It failed with `1 failed, 1999 passed, 254
  skipped` in 186.28s: `test_example.py::TestBuildExampleIntegration::test_iteration_via_iterate_api
  - AssertionError: False is not true : Should find initial model for A`. This run was contended
  (4 other concurrent Claude Code sessions active, load average 4.84), and pre-existing evidence
  from task 136 shows this exact test's Z3 solve varying from 31.59s to 64.34s across three prior
  runs on this same host against its own explicit `max_time: 30` budget — strong circumstantial
  evidence this is a **second, previously-uncharacterized contention-sensitive Z3-timing flake**,
  not a new correctness regression, but this is not proven and a quiet-host re-run is required to
  confirm before tagging. See Findings item 3.

## Context & Scope

Task 151 is the terminal task of the release sequence (per its description, gated on the CLI
defects, documentation corrections, CLI test suite, and packaging-contract tests). Two more tasks
completed today, after 151 was created, and materially change what its five numbered items mean:

1. Task 156 built `code/scripts/release-verify.sh`, a pinned, portable rehearsal runner that
   replaces the archived task's by-hand sequence.
2. Task 157 fixed the W002 duplicate-`VERSION`-file finding that `release-verify.sh` (and
   `RELEASE_SETUP.md`) still describe as an expected, `--ignore`d nonzero exit.

This report re-verifies the task's five numbered items against the current tree, with concrete
line-number-anchored findings for the one already-diagnosed defect, and produces no code changes
(research only, per the delegation's hard constraints).

## Findings

### Item (1) — Rehearsal evidence and the `release-verify.sh` W002 defect

**The runner exists and works.** `code/scripts/release-verify.sh` (executable, single `nix
develop` re-exec guard, pinned tools from `code/scripts/release-tools-requirements.txt`:
`build==1.5.0`, `twine==7.0.0`, `check-wheel-contents==0.6.3`) implements steps (a) provision,
(b) build, (c) twine check, (d1)/(d2) check-wheel-contents, (e1-e3) reference fetch/listings/
diffs, (f) hashes, writing a 12-file evidence set plus `summary.txt` and `parity-diff.md`.
`.github/RELEASE_SETUP.md`'s "Local Rehearsal (No Publish)" section documents it correctly in
outline (evidence table, exit-code contract, hard-gate/informational split).

**The W002 defect, confirmed with fresh independent evidence.** Task 157's summary
(`specs/157_dedupe_theory_lib_version_files_w002/summaries/01_version-file-dedupe-summary.md`)
already named the exact sites that now assert a false expectation, and named task 151 as the
owner of updating them. This research re-derived and independently re-confirmed both the sites
and the underlying fact:

- `code/scripts/release-verify.sh`:
  - **Line 15**: `#   (d1) check-wheel-contents (bare)      -- expected nonzero (W002)     [informational]`
    — should become the hard gate (W002 no longer fires).
  - **Line 16**: `#   (d2) check-wheel-contents --ignore W002 -- "anything NEW?" signal    [hard gate]`
    — the `--ignore W002` step is now unnecessary; bare `check-wheel-contents` **is** the clean
    signal.
  - **Lines 52-57**: the "Reading a nonzero check-wheel-contents (bare) exit" header comment
    block, describing the now-superseded W002 expectation.
  - Beyond the header comments, the **step bodies themselves** also encode the old contract and
    would need updating alongside the comments: `step_d1_wheel_contents_bare()` (lines 296-320,
    classified `info`, with an appended "A nonzero exit here is EXPECTED today: W002..." note
    baked into `wheel-contents.txt`) and `step_d2_wheel_contents_ignore_w002()` (lines 323-341,
    classified `gate`, running `--ignore W002`). The task description's line-number citations
    (15, 16, 52-57) cover the doc/comment layer exactly as stated; the executable logic living
    later in the file (`~296-341`) is the natural implementation surface for actually flipping
    d1 to a hard gate and either removing d2 or repurposing it, and was not itself named by line
    number in the delegation context — flagged here so the implementation phase does not stop at
    the comments.
- `.github/RELEASE_SETUP.md`:
  - **Line 168**: `wheel-contents.txt` table row — "(W002 expected — see below)".
  - **Lines 195-200**: "**Reading a nonzero bare `check-wheel-contents` exit**..." paragraph,
    including line 197's "Deduplicating those files is tracked as a separate, later change" and
    the "not new beyond W002" framing.
  - **Lines 202-206**: "**Historical context only**" paragraph — line 204-205's "the tree has
    since grown the W002-triggering duplicate `VERSION` files" clause is now backwards (the tree
    has since **lost** them); this paragraph's core point (the archived task-125 evidence is
    non-current) still stands and should be kept, just re-worded.
  - **Line 180-181** also lists `check-wheel-contents --ignore W002` as one of the hard gates —
    this becomes bare `check-wheel-contents` once the runner is updated.
  - `code/scripts/README.md` (NOT in this task's `file_scope`) has the same stale framing in its
    `release-verify.sh` section (mentions "check-wheel-contents (bare and with `--ignore W002`)"
    and lists `wheel-contents-ignore-w002.txt` as an output file) — flagged as an incidental
    finding for the implementer to decide whether to widen `file_scope`, not investigated further.

**Independent verification performed by this research** (ambient shell, not through the pinned
`nix develop`-based runner, to get a fast confirmatory signal without re-provisioning a venv):

```
cd code && rm -rf dist && python -m build --no-isolation   # exit 0
twine check --strict dist/*                                  # PASSED / PASSED
check-wheel-contents dist/*.whl                               # OK, exit 0 (no --ignore)
sha256sum dist/*
  c73ab942a515f767b05bec747f844bd0ce115a2a6f69e863c0f7c275cad3dae4  model_checker-1.3.0-py3-none-any.whl
  75e39776e0057027eeb2caec29c0d1f8b920568301e117469b0306e045b4dd9a  model_checker-1.3.0.tar.gz
```

This is a genuinely independent, from-scratch rebuild (not a reuse of any prior task's `dist/`),
and confirms bare `check-wheel-contents` now exits 0 with **no** `--ignore` flag — the evidentiary
basis for flipping `release-verify.sh`'s d1/d2 gate assignment.

**Task 156's own archived rehearsal evidence is stale, one refactor later.**
`specs/156_portable_pinned_release_verification_runner/rehearsal/summary.txt` and
`wheel-contents.txt` record `d1-wheel-contents info exit=1` with the W002 finding — that official
run happened *before* task 157 deduped the `VERSION` files (task 156 completed 17:30 UTC; task 157
completed later the same day). This means the exact problem the task 151 description opens with
("re-run the rehearsal, the archived evidence is invalid because ~22 commits touched code/src")
has recurred one level down: the newest official rehearsal evidence is *also* now invalid, for
the W002 fix rather than the core refactor. **Implementation must re-run
`release-verify.sh` fresh** (after applying the d1/d2 fix above) and archive new evidence under
`specs/151_.../rehearsal/`, not reuse task 156's evidence directory.

`code/dist/` is confirmed gitignored (`**/dist` at root `.gitignore` line 13); no rehearsal build
artifact should ever be committed.

### Item (2) — Version number and CHANGELOG

**Current agreement, confirmed by direct read:**

| Source | Value |
|--------|-------|
| `code/pyproject.toml:9` | `version = "1.3.0"` |
| `flake.nix:25` (`modelChecker` derivation) | `version = "1.3.0";` |
| `flake.nix:137` (`checks.default` derivation) | `version = "1.3.0";` |
| `code/CHANGELOG.md` | `## [1.3.0] - 2026-07-24` (most recent dated entry) |
| `model_checker.__version__` | derived via `importlib.metadata` — no third literal to drift |
| Latest git tag | `v1.2.12` (no `v1.3.0` tag exists — confirmed via `git tag -l "v1.3.0"`, empty) |
| PyPI live latest (public JSON API, no credentials) | `1.2.12` — confirms `v1.2.12` is genuinely the last published release |

**Commit volume since the CHANGELOG's `1.3.0` entry**: the entry was added by commit `42185381`
("task 124 phase 5: add CHANGELOG release entry and seed ROADMAP", 2026-07-24 08:13:03 -0700).
Since that commit (exclusive) through current `HEAD` (`546373ec`, "task 157: complete
implementation"):

- **64 commits** touched `code/src` (the original task description's "roughly 22" is stale — it
  predates the bulk of task 126, which alone accounts for 24 of the 64).
- **300 commits** total (touching any path, including `specs/`).
- Per-task breakdown of the 64 `code/src`-touching commits (top contributors): task 126 (core/
  theory_lib boundary refactor) 24, task 146 6, task 135 4, tasks 144/139/134/130 3 each, tasks
  157/155/145/141/129/117 2 each, tasks 148/142/140/136/128 1 each.
- Critically, **two of those tasks landed today, after task 151 was created**: task 156 (the
  `release-verify.sh` runner — itself release tooling, arguably changelog-worthy) and task 157
  (the W002 fix — a real behavior change to what ships in the wheel, definitely changelog-worthy).

**`## [Unreleased]` is confirmed empty** — zero bullets between the `## [Unreleased]` heading and
the `## [1.3.0]` heading.

**Note on git topology** (informational only, not release-blocking): `v1.2.12` is **not** an
ancestor of current `HEAD` (`git merge-base --is-ancestor v1.2.12 HEAD` returns false; `git
describe --tags` fails to find any describing tag). This reflects some prior history
rewrite/reorganization in this repository's life, not a live branching concern — PyPI's own
record independently confirms `1.2.12` is the last published version regardless of the local git
graph's shape, so the "last published release" framing used throughout `RELEASE_SETUP.md` and
`release-verify.sh`'s `--ref 1.2.12` default remains correct.

**Fold-into-1.3.0 vs. bump — options and recommendation:**

| Option | What it means | Case for | Case against |
|--------|---------------|----------|---------------|
| **A. Fold into 1.3.0** (recommended) | Keep `version = "1.3.0"` everywhere; expand the existing `## [1.3.0]` CHANGELOG entry (or its date) to also describe the refactor/W002/CI work; publish `v1.3.0` as the first-ever tag for this version. | 1.3.0 was **never published** — there is no consumer-visible "1.3.0" to conflict with or confuse; nothing on PyPI currently claims that number; this matches the archived task's own "either fold in (defensible, since 1.3.0 was never published)" framing verbatim. Avoids a second, purely paperwork version bump for what is still pre-first-publish content. | The CHANGELOG's existing `## [1.3.0] - 2026-07-24` date would either need updating to reflect the actual publish date, or the entry would carry a "written" date far earlier than what it now covers (the refactor landed across roughly three subsequent weeks of commits, as of 2026-08-12). |
| **B. Bump (e.g. 1.3.1 or 1.4.0)** | Update `pyproject.toml`, both `flake.nix` sites, and add a **new** `## [1.3.1]`/`## [1.4.0]` CHANGELOG entry describing only the post-1.3.0-entry work (refactor, W002 fix, CI fixes, release tooling); leave the existing `## [1.3.0]` entry as a discrete historical record. | Cleaner separation: the existing 1.3.0 entry's content and date stay accurate as originally written; a bump signals "this is new work" more legibly to changelog readers than silently expanding an old entry. | Three files must change (`pyproject.toml` + two `flake.nix` sites) purely to reflect that nothing was ever actually published as 1.3.0 — a bump for a version the world never saw. |

**Recommendation: Option A (fold into 1.3.0).** The determining fact is that 1.3.0 has never
been published anywhere (not on PyPI, no git tag) — there is no external consumer who could be
confused by the entry's scope growing before its first release. The CHANGELOG entry's date should
be updated (or a note added) to reflect the actual tag/publish date rather than the original
2026-07-24 draft date, and its body should gain sections for: the core/theory_lib refactor (task
126), the W002 duplicate-`VERSION`-file fix (task 157), the CI fixes (task 155: `wheel` build
dependency, timing-budget raises), and the new `release-verify.sh` rehearsal runner (task 156).
This is a CHANGELOG-content decision for the implementation phase, not something this research
report should draft in full — but the shape (one expanded 1.3.0 entry, not a new version number)
is the recommendation.

### Item (3) — Fresh `nix flake check` on a quiet host

**Run to completion during this research session — FAILED, but the host was contended and the
failure is plausibly (not yet confirmably) a second, previously-uncharacterized timing flake, not
the documented one.** Verbatim tail of the run:

```
> FAILED src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_iteration_via_iterate_api - AssertionError: False is not true : Should find initial model for A
> ===== 1 failed, 1999 passed, 254 skipped, 3 warnings in 186.28s (0:03:06) ======
```

(`nix flake check`, `checks.x86_64-linux.default`, full log at
`/nix/store/9q1vkdkqv9m7d4i4j2ga2l19hxvmgx05-model-checker-checks-1.3.0.drv`.)

This is **not** the task description's documented flake
(`test_bimodal.py::test_example_cases[BM_CM_1-example_case7]`) — that test passed. The failure is
in a different test entirely. The run was contended: the host was simultaneously running **4
other concurrent `claude --dangerously-skip-permissions` sessions** (confirmed via `ps aux`),
load average 4.84 at observation time — precisely the "shared-tenancy contention" condition the
archived checklist and this task's item (3) describe as invalidating a clean confirmation. This
run's result should **not** be read as the required quiet-host confirmation, but the specific
failure is worth flagging rather than dismissing outright:

**Circumstantial evidence this is a timing flake, not a regression**: the failing test
(`test_iteration_via_iterate_api`, `code/src/model_checker/builder/tests/unit/test_example.py:365`)
asserts `result["model_found"]` is `True` (`"Should find initial model for A"`) after a Z3 solve
with an explicit `max_time: 30` budget (the test's own docstring/comment explains this budget was
made explicit specifically because "the real solve is slower than [the bimodal 1s default] and an
inherited default makes model_found depend on machine load rather than on satisfiability" — i.e.
this test's author already anticipated load-sensitivity). Prior evidence from
`specs/archive/136_ground_wallclock_performance_budgets/evidence/unfiltered-run-{1,2,3}.txt`
records this exact test's wall-clock time on **this same host** varying from **31.59s to 64.34s**
across three separate runs — already exceeding its own 30s budget in at least one prior recorded
run, independent of today's contention. This is strong circumstantial evidence the failure
observed today is the same class of Z3-timing/CPU-contention sensitivity as the documented
`BM_CM_1` flake, just in a different test — but it is **not proven**; a quiet-host re-run is
required to confirm before treating it as non-blocking.

**The originally-documented flake, characterized from prior evidence** (not reproduced today,
since it passed in this run): `test_bimodal.py::test_example_cases[BM_CM_1-example_case7]` is a
Z3 solve that normally completes in ~10s but intermittently exceeds its budget under CPU
contention (documented in
`specs/archive/122_rootcause_crossoracle_differential_and_establish_t/baselines/bimodal-tally.md`:
observed 15.16s/15.20s against a budget close to that range, isolated specifically to full-suite
12-way (`-n auto`) parallelism; `flake.nix`'s `checks.default` comment already documents this and
deliberately pins `-n 6` rather than `-n auto` for exactly this reason). Separately, task 155
(completed today) raised the **application-level** `max_time` budget for a different, unrelated
correctness test (`test_iterate_two_produces_distinct_models`, 30s→60s) and the pre-existing
differential-tests CI timeout (300s→900s) — neither of those was `BM_CM_1` or
`test_iteration_via_iterate_api`, but all three are the same recurring class of issue: Z3-solve
wall-clock budgets set too tight for this host's variable load.

**Recommendation**: implementation (or the user, pre-tag) must re-run `nix flake check` on a
demonstrably quiet host — either a period with no other concurrent Claude Code/build sessions on
this machine, or a CI runner — and treat today's contended run as inconclusive rather than as the
pre-flight confirmation. If a quiet re-run passes cleanly, today's failure was contention, not a
regression, and no code change is required (though raising `test_iteration_via_iterate_api`'s
`max_time` past 30s, matching task 155's treatment of the sibling `test_iterate_two_produces_
distinct_models` test, would be a reasonable proactive hardening). If a quiet re-run reproduces
the same failure, treat it as a genuine regression requiring investigation before tagging — do
not assume timing sensitivity without a clean-host reproduction.

### Item (4) — PyPI Trusted Publisher / GitHub Environments (user-only blocking gate)

**Observable without credentials, confirmed via `gh api` (read-only GitHub API, no PyPI
interaction, no web-UI action taken):**

```
gh api repos/benbrastmckie/ModelChecker/environments
```

returns **both** `pypi` and `testpypi` GitHub Environments as already existing:

| Environment | Created (UTC) | Protection rules | Deployment branch policy |
|-------------|----------------|-------------------|----------------------------|
| `pypi` | 2026-08-12T14:47:11Z | none | none (unrestricted) |
| `testpypi` | 2026-08-12T14:48:07Z | none | none (unrestricted) |

Both were created **today**, roughly 2-3 hours before this research session — this is new since
the task description was written (which stated "every box in the archived checklist's
one-time-setup section is unchecked"). **The GitHub Environments half of the one-time setup
appears to be done.** Neither environment currently has protection rules (e.g. required
reviewers) — `RELEASE_SETUP.md` describes this as optional, so absence is not itself a defect,
but it does mean nothing currently gates a push to the `pypi` environment beyond the tag push
itself.

**What remains genuinely unconfirmed, and cannot be checked from here**: whether a **PyPI
trusted publisher** (Owner `benbrastmckie`, Repository `ModelChecker`, Workflow `release.yml`,
Environment `pypi`) has actually been registered on pypi.org, and likewise for the optional
TestPyPI equivalent. There is no read-only API or CLI surface for this that doesn't require
either (a) the account owner's PyPI login (a web-UI action explicitly out of scope per this
task's hard constraint) or (b) actually triggering a publish and observing whether it succeeds
or fails with an OIDC/untrusted-publisher error (which would require pushing a tag — also
user-only and explicitly not to be done here). **This remains the blocking gate; it is now
half-cleared (GitHub Environments exist) rather than fully unchecked.**

**Explicit gate for the user, restated**: before any tag push, confirm on pypi.org (Settings →
Publishing for an existing `model-checker` project, or the pending-publisher flow if this is
effectively a first real publish under Trusted Publishing) that a trusted publisher exists with
exactly Owner `benbrastmckie`, Repository `ModelChecker`, Workflow `release.yml`, Environment
`pypi` — and optionally the TestPyPI equivalent with Environment `testpypi`. Pushing a tag before
this is done runs `test-and-release` and `build` (burning CI time and, per `RELEASE_SETUP.md`,
`publish-testpypi` runs with `continue-on-error: true` so it fails softly), then `publish-pypi`
fails at the OIDC exchange — exactly the "Common Issues" scenario `RELEASE_SETUP.md` already
documents.

### Item (5) — Post-publish verification, including on NixOS

The task description's recipe was taken at face value and cross-checked against
`RELEASE_SETUP.md` and the archived `PUBLISH-CHECKLIST.md` step 5 (`pip index versions
model-checker`) — both are consistent with, and do not contradict, the description's NixOS
`LD_LIBRARY_PATH` workaround:

```
python3 -m venv testvenv
PIP_USER=0 ./testvenv/bin/pip install model-checker
LD_LIBRARY_PATH=$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib \
  ./testvenv/bin/model-checker <project>/examples.py
```

No independent re-verification of this exact recipe was performed in this research session (it
requires a real published PyPI artifact, which does not yet exist for 1.3.0 — this is
correctly scoped as post-publish, not pre-publish, work). Recommendation for the implementation
phase / user: after publish, install **from PyPI** (not local `dist/`), run `pip index versions
model-checker` to confirm the new version is visible, then generate-and-execute a project for
each of the four registered theories (`logos`, `exclusion`, `imposition`, `bimodal`) using the
NixOS `LD_LIBRARY_PATH` workaround above, matching the "4/4 exit 0" golden-path check the review
already performed against the local wheel. The incidental finding about `z3-solver 5.0.0.0`
resolving cleanly with no upper pin is noted as-is in the task description and requires no
independent action unless something breaks during this re-verification.

## Decisions

- **Item (1)**: Implementation should (a) apply the d1/d2 fix to `code/scripts/release-verify.sh`
  (comments at lines 15-16, 52-57, and the step bodies at ~296-341 — flip d1 to the hard gate,
  retire or repurpose d2), (b) apply the corresponding text fix to `.github/RELEASE_SETUP.md`
  (lines 168, 180-181, 195-200, 202-206), and (c) re-run the corrected `release-verify.sh` end to
  end, archiving fresh evidence under `specs/151_.../rehearsal/` rather than reusing task 156's
  now-stale evidence directory.
- **Item (2)**: Recommend Option A (fold the refactor/W002/CI/tooling work into the existing
  `## [1.3.0]` entry, no version bump) — see the options table above for the full reasoning. This
  is a recommendation, not yet applied; the implementation phase should draft the actual CHANGELOG
  prose.
- **Item (3)**: Not resolved by this research — requires a genuinely quiet host. Flagged as a
  pre-tag blocking step, not satisfiable from a shared, multi-agent host during this session.
- **Item (4)**: GitHub Environments are confirmed present; PyPI trusted publisher status remains
  unconfirmed and is explicitly out of this research's reach (would require PyPI web-UI access).
  Surfaced as the user's explicit action item before tagging.
- **Item (5)**: Recipe cross-checked and left unchanged; execution deferred to genuinely
  post-publish verification.

## Recommendations

1. **(High, item 1)** Fix `release-verify.sh`'s d1/d2 classification and comments, and
   `RELEASE_SETUP.md`'s matching prose, then re-run the runner and archive fresh evidence — this
   is the most concrete, fully-specified, low-risk change this task can make.
2. **(High, item 2)** Adopt fold-into-1.3.0; expand the CHANGELOG's `## [1.3.0]` entry to cover
   the refactor, W002 fix, CI fixes, and the new rehearsal runner; leave `pyproject.toml`/
   `flake.nix` version literals unchanged at `1.3.0`.
2a. **(Medium, incidental)** Consider whether `code/scripts/README.md`'s `release-verify.sh`
   section (outside this task's `file_scope`) should also be corrected for the same W002 framing,
   or left as a known follow-up.
3. **(High, item 3)** Before tagging, re-run `nix flake check` on a demonstrably quiet host (no
   concurrent agent sessions) or a CI runner. Today's contended run failed on
   `test_iteration_via_iterate_api` (not the documented `BM_CM_1-example_case7`); confirm on a
   quiet host whether this reproduces. If it does not reproduce cleanly, treat it as contention
   and consider proactively raising its `max_time` (currently 30, observed 31.59-64.34s wall-clock
   on this host in prior evidence) past 30s. If it does reproduce on a quiet host, treat it as a
   genuine regression blocking the release.
4. **(Blocking, item 4, user-only)** Confirm the PyPI (and optionally TestPyPI) trusted publisher
   registration on pypi.org/test.pypi.org before pushing any tag. GitHub Environments are already
   in place and need no further action unless additional protection rules (e.g. required
   reviewers on `pypi`) are desired.
5. **(Low, item 5)** No action needed pre-publish; execute the NixOS-aware post-publish recipe
   once a real tag has been published, verifying all four theories generate-and-execute cleanly
   from the PyPI-installed package.
6. Reuse `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md` as the
   structural template for a new, task-151-scoped checklist reflecting the current state (GitHub
   Environments already done; trusted publisher still open; runner-driven rehearsal instead of
   by-hand steps) — the implementation phase's most direct artifact.

## Risks & Mitigations

- **Risk**: a third rehearsal run also goes stale before publish, if more commits land on
  `code/src` between this task's implementation and the user's tag push. **Mitigation**: the
  `release-verify.sh` evidence set should be re-run one final time immediately before the user
  tags, not treated as a one-and-done artifact from this task's implementation phase.
- **Risk**: the quiet-host `nix flake check` re-run (item 3) still cannot be obtained if this
  remains a persistently shared, multi-agent host. **Mitigation**: explicitly schedule/request a
  window with no other active Claude Code sessions, or run the check via GitHub Actions CI
  (task 150's general CI workflow) as a `quiet-host`-equivalent substitute if a literally idle
  local host is impractical to arrange.
- **Risk**: assuming the PyPI trusted publisher is configured because the GitHub Environments now
  exist. **Mitigation**: these are two independent configuration surfaces (PyPI-side vs.
  GitHub-side); this report explicitly does not claim the PyPI side is done, and the
  recommendation instructs the user to confirm it directly.

## Appendix

### Sources/Inputs

Task/state:
- `specs/state.json` (`active_projects[project_number==151]`, and 147/149/150/155/156/157 status)
- `specs/151_rerun_release_rehearsal_and_publish_to_pypi/` (this task's directory)

Predecessor task artifacts:
- `specs/156_portable_pinned_release_verification_runner/summaries/01_release-verify-runner-summary.md`
- `specs/156_portable_pinned_release_verification_runner/rehearsal/` (summary.txt, wheel-contents.txt)
- `specs/157_dedupe_theory_lib_version_files_w002/summaries/01_version-file-dedupe-summary.md`
- `specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/summaries/01_ci-fixes-summary.md`
- `specs/archive/125_release_engineering_and_pypi_rehearsal/PUBLISH-CHECKLIST.md`
- `specs/archive/122_rootcause_crossoracle_differential_and_establish_t/baselines/bimodal-tally.md`
- `specs/archive/136_ground_wallclock_performance_budgets/evidence/unfiltered-run-{1,2,3}.txt`
- `code/src/model_checker/builder/tests/unit/test_example.py` (lines 365-420,
  `test_iteration_via_iterate_api`)

Code/config read directly:
- `code/scripts/release-verify.sh` (full read, line numbers cited above)
- `code/scripts/release-tools-requirements.txt`
- `code/scripts/README.md` (`release-verify.sh` section)
- `.github/RELEASE_SETUP.md` (full read)
- `.github/workflows/release.yml` (full read)
- `code/pyproject.toml:9`
- `flake.nix:25`, `flake.nix:137`
- `code/CHANGELOG.md`
- `.gitignore` (root, line 13)

Commands run (read-only / evidentiary, no push/tag/PR/publish):
- `git tag`, `git describe`, `git merge-base`, `git log -S"## [1.3.0]"`, `git log --oneline
  <commit>..HEAD -- code/src`
- `gh auth status`, `gh api repos/benbrastmckie/ModelChecker/environments[/pypi|/testpypi]`
- `curl https://pypi.org/pypi/model-checker/json` (public, unauthenticated PyPI API)
- `cd code && rm -rf dist && python -m build --no-isolation && twine check --strict dist/* &&
  check-wheel-contents dist/*.whl && sha256sum dist/*` (independent fresh-build verification)
- `nix flake check` (completed, 186.28s, 1 failed/1999 passed/254 skipped; contended run, not a
  quiet-host confirmation — see Findings item 3)
- `ps aux`, `uptime` (host-contention evidence)

### No push, tag, or PR

Confirmed: no `git push`, `git tag`, `gh pr create`, `/merge`, or `twine upload` was run at any
point in this research session, per `.claude/rules/pr-prohibition.md` and this task's own AGENT
CONSTRAINT. The only write this session performed to the working tree was a scratch
`rm -rf code/dist && python -m build` rebuild (gitignored, never staged or committed) used solely
to independently re-confirm the W002 finding for item (1).
