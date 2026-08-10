# Teammate A Findings: Primary Verification of Task 117's Five Goals

**Angle**: Re-verify (not just re-read) the current, actual state of the repository against
task 117's five goals: CLI works, PyPI parity audit, Nix flake, full testing, release readiness.
Every claim below was independently re-run in this session on branch
`task-117-restore-model-checker`, not taken on faith from prior task summaries.

## Key Findings

### 0. CRITICAL — Uncommitted source change in the working tree

`git status --short` shows `code/src/model_checker/models/structure.py` as **modified and
uncommitted**. `git log -- code/src/model_checker/models/structure.py` shows this file was last
touched by a commit years before task 118 (`e9734a27`) — it is **not part of any task
118-125 commit**, and task 122's "Files Modified" list (which explicitly enumerates every file
its baseline run touched) does not include it. The file's mtime (03:07) predates the current
session's `specs/state.json`/`TODO.md` churn (08:45), so it is leftover uncommitted work from
some earlier, undocumented session — not an artifact of this research dispatch.

The diff is a real, substantive fix to `ModelDefaults`'s Z3 result classification (both
`solve()` and a second checking method): previously, any Z3 `UNKNOWN` result whose
`reason_unknown()` string was *not exactly* `"timeout"` fell through to being treated as a
**definitive UNSAT** (i.e., "formula is valid, no countermodel exists"). Z3 commonly reports
`"canceled"` or other strings for an inconclusive result even when the actual cause is the
timeout set by this same code — so the old code silently misclassified inconclusive runs as
proof of validity, which is unsound. The uncommitted patch fixes this: **any** `UNKNOWN` result
is now treated as inconclusive, regardless of the specific reason string. This is closely related
to (but a different code path from) the `Z3OracleProvider` timeout-conflation bug task 122
root-caused and `xfail`-documented in `oracle/bimodal_logic/provider.py` — this one is in the
**shipped core package**, not the oracle test harness.

I ran the in-package bimodal suite fresh with this uncommitted fix in place: **286/286 passed**
(65.6s, no `-n` — `pytest-xdist` is not installed in this shell's Python), matching task 122's
baseline count exactly, so the fix does not regress anything currently tested. But:
- **This fix is not committed.** If task 117 closes and a release is cut from `HEAD`, this fix
  will **not** be in the release — the wheel will ship the unsound fall-through-to-UNSAT
  behavior.
- No task, plan, or summary I could find documents this change. It needs either (a) attribution
  to a task and a commit, or (b) if it was an experimental/unintended edit, a decision to revert
  it. Either way, task 117 cannot close with this hanging uncommitted.
- Other uncommitted diffs in `git status` (`.orchestrator-handoff.json` files, `specs/state.json`,
  `specs/TODO.md`, a deleted `.lock/holder.json`) are ordinary task-management churn from this
  research session and task 117's status transition to `researching` — not a concern.
  `specs/116_.../email-draft.md`'s uncommitted diff is unrelated personal content, also not a
  task-117 concern. `code/specs/state.json` (deleted) appears to be a stray duplicate/misplaced
  file unrelated to the canonical `specs/state.json`.

### 1. CLI: works, but `--maximize` is broken for the bimodal theory specifically

- `./dev_cli.py --help`, a plain `logos/examples.py` run, and `--save markdown json` all pass
  cleanly (re-verified fresh).
- **New finding, not caught by any prior baseline**: `--maximize` fails on **every single example**
  (22/22) in `bimodal/examples.py`:
  ```
  Error processing Bimodal: No module named 'bimodal_semantic_module'
  ```
  Root cause (traced to source): `bimodal/semantic/__init__.py` loads the sibling `semantic.py`
  file via `importlib.util.spec_from_file_location(..., "bimodal_semantic_module")` and
  `exec_module()` **without registering the module in `sys.modules`** (a long-standing workaround
  for the `semantic.py` file being shadowed by the `semantic/` package directory of the same
  name — last touched at a pre-task-118 commit, so this bug predates the restoration effort
  entirely, but was never caught until now). `--maximize` routes through
  `builder/comparison.py`'s `ProcessPoolExecutor` (`compare_semantics()`), which must pickle
  class references to hand work to worker processes; pickling a class whose `__module__` is
  `"bimodal_semantic_module"` requires that name to be importable/registered in `sys.modules`,
  which it never is. Every worker process fails, the exception is caught and printed by
  `comparison.py:135`, and the CLI silently reports `Maximum N = 0` for every bimodal example
  and **still exits 0** — a real feature (`--maximize` is a documented, headline CLI flag) is
  silently broken specifically for one of the four in-package theories.
  - Confirmed **not** a general `--maximize` regression: `logos/examples.py --maximize` and
    `exclusion/examples.py --maximize` both ran clean with no `"No module named"` errors.
    `exclusion/semantic/__init__.py` uses ordinary relative imports (`from .core import
    WitnessSemantics`, etc.), not the dynamic-loader hack — confirming the bug is specific to
    bimodal's `semantic/__init__.py` implementation.
  - `imposition/examples.py --maximize` hit a separate, unrelated issue (`Error processing
    BernardChampollion: b'max. memory exceeded'` on one example) — likely a memory-hungry
    example under 4-way parallelism, not a module/pickling bug; lower priority but worth a
    follow-up look.
- Why task 122's baseline missed this: `baselines/cli-smoke-maximize.txt` only exercises
  `logos/examples.py --maximize` (verified by reading the file) — it never exercised
  `--maximize` against the bimodal theory.

### 2. Test suite: task 122's baseline holds up under fresh re-verification

- Re-ran `code/src/model_checker/theory_lib/bimodal/tests` fresh (with the uncommitted
  `structure.py` fix in place): **286/286 passed**, matching the documented baseline exactly.
- `specs/122_.../baselines/RELEASE-BASELINE.md` is a well-evidenced, thorough document: 2716
  composed tests across three scopes (286 in-package bimodal, 550 relocated oracle, 1880
  everything-else), with 28 pre-existing failures in the "everything-else" scope fully
  root-caused into 8 categories (none touching task 122's own edits) and 9 justified
  `xfail(strict=True)` markers (5 for the oracle-provider timeout-as-UNSAT bug noted above, 4 for
  `oracle/`'s intentional lack of packaging metadata). I independently spot-checked one of the 8
  categories (`rest-suite-disposition.md`'s Category A/B breakdown) against the actual file
  paths cited and they check out.
- I did complete a fresh full single-threaded re-run of the "everything-else" scope (no
  `pytest-xdist` available in this shell — `ModuleNotFoundError: No module named 'xdist'`,
  matching task 122's own note about the Nix-managed environment's `pip install` constraints; it
  finished in 278s single-threaded). Result: **29 failed, 1780 passed, 1809 collected** — vs. the
  documented baseline's **28 failed, 1852 passed, 1880 collected**. Line-by-line comparison
  against `rest-suite-disposition.md`'s full 28-test enumeration:
  - **All 28 of task 122's documented failures reproduced exactly**, matching every test ID in
    every category (A-H).
  - **One new, previously-undocumented failure**:
    `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py::
    TestTargetLoaderBehavior::test_performance_improvement`. Not in any of task 122's 8
    categories or its 28-test table.
  - **Collection count is 71 tests lower** (1809 vs 1880) despite running the exact same pytest
    invocation task 122 documented, on the same commit plus only the uncommitted `structure.py`
    diff (which doesn't add/remove test files). I spot-checked whether an optional dependency
    (`cvc5`) could explain a large skip/deselect delta — `cvc5` imports fine in this environment
    and `test_solver_comparison.py` alone collects 250 tests including cvc5-parametrized cases,
    so that's not an obvious explanation. I did not have time to root-cause the 71-test gap
    further; it should not be dismissed as noise without a proper diff of collected test IDs
    between the two runs (the committed `junit-rest.xml` from task 122 has the full 1880-test ID
    list to diff against).
  - `test_performance_improvement` is very likely the same class of timing-threshold flake as
    Categories A/C (the file name/class suggest a performance-improvement-ratio assertion), but
    I have not read its source to confirm, and it should not simply be assumed benign given the
    collection-count anomaly above.
- `pytest-xdist` not being available by default in this shell is itself a minor
  release-readiness/DX gap: the `dev` optional-dependency group in `pyproject.toml` lists it, but
  a plain `pytest` invocation in a fresh clone (no scratchpad hacks) cannot reproduce task 122's
  `-n 6` baseline without manually working around the Nix `--user`-forced `pip install`
  conflict documented in both task 122's and 125's summaries.

### 3. Nix flake: genuinely works (re-verified from scratch, not just read)

- `nix flake show`: evaluates cleanly for all 4 default systems (`checks`, `devShells`,
  `packages`), no errors.
- `nix build --no-link --print-out-paths` (`.#default`): **succeeds**, produces a real store path
  (`/nix/store/.../python3.12-model-checker-1.3.0`) containing a working `bin/model-checker`.
  Ran the built binary directly (`$out/bin/model-checker --help` and against
  `logos/examples.py`) — both work, confirming the Nix-packaged CLI entry point is real, not
  just evaluatable.
- `nix flake check`: **passes** — `checking derivation checks.x86_64-linux.default ... all checks
  passed!`. This exercises the flake's `checks.default` derivation (scoped to the known-green
  bimodal suite per the flake's own comment).
- This directly satisfies `PUBLISH-CHECKLIST.md` step 1's two unchecked pre-flight boxes
  (`nix flake check` and `nix build`) — both now confirmed passing in this session, so those
  checkboxes can be marked done once the checklist is next touched.

### 4. Release readiness / PyPI parity: task 125's rehearsal evidence is solid and re-checked

- `code/pyproject.toml`: `name = "model-checker"`, `version = "1.3.0"`. `code/CHANGELOG.md` has
  a real `## [1.3.0] - 2026-07-24` entry (not `[Unreleased]`) — re-verified directly, matches
  `PUBLISH-CHECKLIST.md`'s claim.
- `specs/125_.../rehearsal/parity-diff.md`: local build produced `model_checker-1.3.0-py3-none-
  any.whl`/`.tar.gz`, `twine check --strict` PASSED on both, `check-wheel-contents` clean, no
  `oracle/` path in either artifact. The diff against the last published `model-checker==1.2.12`
  found exactly two real content deltas (`solver/` module addition, `cli.py` removal) and
  correctly flags that several deltas the plan anticipated (restored `builder`/`iterate`/
  `exclusion`/`imposition`) are **not observable** in this diff because 1.2.12 already had them —
  a genuinely careful, non-misleading piece of analysis rather than a rubber-stamped "no
  differences" claim.
- `.github/workflows/release.yml` and `.github/RELEASE_SETUP.md`: read both; the OIDC Trusted
  Publishing job graph (`build` -> `publish-testpypi` -> `publish-pypi` -> `github-release`) is
  coherent, `PYPI_API_TOKEN` references are fully gone, and the `cd Code` casing bug fix is
  present. I did not have GitHub Actions credentials to actually trigger a workflow run, so this
  is a read-verification only (not an execution re-verification like the Nix/CLI/test items
  above).
- `PUBLISH-CHECKLIST.md` correctly gates all push/tag/publish/environment-setup steps as
  **USER-ONLY**, consistent with `.claude/rules/pr-prohibition.md`. No agent in this task chain
  pushed, tagged, or published — confirmed via `git log` (no push-adjacent commits) and the
  absence of any `dist/` upload evidence.

## Recommended Approach — what remains for task 117 to close

1. **Resolve the uncommitted `structure.py` fix first, before anything else.** Determine
   provenance (was this an in-progress fix from an earlier interrupted session, or accidental?),
   then either commit it under a proper task-scoped commit (it is a real soundness fix and
   arguably should ship) or revert it if it's not actually wanted. Shipping a release with this
   silently uncommitted would either (a) omit a real bug fix, or (b) if someone commits it
   without review, ship an unreviewed change with no task attribution.
2. **File/fix the bimodal `--maximize` bug** (`No module named 'bimodal_semantic_module'`) before
   calling the CLI "verified working" — `--maximize` is a first-class, documented CLI flag, and
   it is silently broken (exit 0, wrong output) for one of the four shipped theories. This
   deserves at minimum a follow-up task; given task 117's explicit "verify the CLI works" goal
   and the low cost of the fix (register the dynamically-loaded module in `sys.modules` before
   `exec_module`, or refactor to a plain relative import like exclusion/imposition already do),
   it's plausibly in-scope for task 117 itself rather than a spinoff.
3. **Root-cause the 71-test collection-count gap and the 1 new failure found in my fresh
   full-suite re-run.** All 28 of task 122's documented failures reproduced exactly (good), but
   my fresh run also found a 29th failure not in task 122's baseline
   (`test_refactoring_target_behavior.py::TestTargetLoaderBehavior::test_performance_improvement`)
   and collected 71 fewer tests overall (1809 vs 1880). Diff the collected test-ID list against
   the committed `baselines/junit-rest.xml` to determine whether this is environment-dependent
   (e.g., an optional-dependency-gated skip) or a real regression before treating the
   "everything-else" gate as still fully green.
4. Mark `PUBLISH-CHECKLIST.md`'s `nix flake check` / `nix build` pre-flight checkboxes done —
   both are now confirmed passing.
5. Everything else (release.yml correctness, parity diff, OIDC setup docs) checks out on
   read-verification; no further action needed beyond the user-only steps the checklist already
   correctly gates.

## Evidence/Examples

```
$ git log --oneline -- code/src/model_checker/models/structure.py | head -1
e9734a27 Remove first-order subtheory and its infrastructure from logos   # pre-dates task 118

$ PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q
======================== 286 passed in 65.59s (0:01:05) ========================

$ ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py --maximize 2>&1 | grep -c "No module named 'bimodal_semantic_module'"
22

$ nix build --no-link --print-out-paths
/nix/store/fqbvsrk99k6f5587zc2d8ldgsylx7ghs-python3.12-model-checker-1.3.0
$ /nix/store/.../bin/model-checker --help    # exits 0, correct usage text

$ nix flake check
...
all checks passed!

$ grep -n "1.3.0\|Unreleased" code/CHANGELOG.md
7:## [Unreleased]
9:## [1.3.0] - 2026-07-24
```

## Confidence Level

**High** on the CLI, Nix flake, and structure.py-uncommitted-diff findings — all directly
re-executed/re-read in this session, not inferred. **High** on the overall test-suite disposition for the 28 documented failures (all 28
reproduced exactly in a fresh full re-run), with an open, unresolved **medium-confidence flag**
on the 1 new failure and 71-test collection-count gap found in that same fresh run — worth a
quick root-cause before treating the "everything-else" scope as unchanged. **High** on release-readiness/parity-diff
correctness as a read-verification (the underlying artifacts — wheel hashes, twine output,
workflow YAML — are internally consistent and match what the summaries claim), with the caveat
that I did not execute a live GitHub Actions run.
