# Implementation Plan: Task #157

- **Task**: 157 - Deduplicate the four theory_lib VERSION files to clear check-wheel-contents W002
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: 155 (completed)
- **Research Inputs**: `specs/157_dedupe_theory_lib_version_files_w002/reports/01_version-file-dedupe.md`
- **Artifacts**: plans/01_version-file-dedupe.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The research recommended remedy **(b)** — keep the four `VERSION` files but exclude them from the
wheel. **That remedy is wrong, and this plan does not adopt it.** The risk the research left open
(whether `builder/project.py`'s scaffolding copy reads from the *installed package* or only from a
source checkout) was closed during planning by direct experiment: it reads from the installed
package, and remedy (b) breaks project generation for every pip-installed user. See "Risk closure"
below for the evidence.

This plan instead adopts remedy **(a)**: remove the four `VERSION` files and consolidate on
`__init__.py`'s `__version__` as the single source of truth. This requires a **file_scope
widening** (four files outside the declared scope), which Phase 1 records explicitly rather than
letting it happen silently.

The work is ordered so that **every phase leaves the tree green** — no red intermediate states, no
atomic-batch commit. The ordering is not cosmetic: relaxing the scaffolding requirement *before*
changing what ships is the very constraint that makes remedy (b) unsafe.

### Risk closure: does scaffolding read from the installed package?

**Yes. Conclusively.** `builder/project.py:121` computes the source directory package-relatively:

```python
self.source_dir: str = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'theory_lib', theory)
```

`__file__` is `<site-packages>/model_checker/builder/project.py`, so `source_dir` resolves to
`<site-packages>/model_checker/theory_lib/<theory>` — the installed package. There is no
source-checkout fallback. `project.py:266-271` then fail-fasts with `FileNotFoundError` on any
missing `REQUIRED_COPY_ITEMS` entry, and `VERSION` is on that list (`project.py:52`). The path is
reachable from the CLI: `__main__.py:261`/`:290` instantiate `BuildProject()` for
`model-checker -l <name>`.

Controlled experiment run during planning — the 1.3.0 wheel unpacked twice, identical except for
the presence of the `VERSION` files, then `BuildProject('logos').generate('demo')` run against each:

| Wheel variant | Result |
|---|---|
| `VERSION` present (as shipped today) | generation **succeeded**; `VERSION` copied into `project_demo/` |
| `VERSION` removed (simulating remedy (b)) | `FileNotFoundError: Theory 'logos' is missing required item(s) ['VERSION'] in <...>/theory_lib/logos` |

**Conclusion**: remedy (b) as scoped is a functional regression for every pip-installed user —
strictly worse than the lint warning it fixes. It is rejected. Note also that the existing
packaging test `code/tests/packaging/test_generate_then_execute.py` installs the wheel into a real
venv and generates+executes a project per theory, so remedy (b) would have failed the packaging
contract suite too — additional independent confirmation.

### Weighing (a) against (b) on the merits, not on scope convenience

The research's preference for (b) rested substantially on file_scope containment. That is not a
good reason, and this plan does not treat it as one. Setting containment aside:

**The genuinely technical argument for keeping the files** is real and deserves a straight answer:
`THEORY_ARCHITECTURE.md:44` names `VERSION` as required theory-level metadata, so per-theory
versioning is a documented, intended convention — not copy-paste debris — that simply has never
been exercised. Retiring documented conventions unilaterally is a real cost.

**Why (a) still wins**: the intended convention is *not lost* by deleting the file, because
per-theory versioning is already implemented — through `__version__` in each theory's
`__init__.py`, which is what `get_theory_version()`, `check_theory_compatibility()`, and
`update_all_theory_versions()` actually read and write. The `VERSION` file is a **second, parallel,
never-wired encoding of the same number**. Deleting it removes the redundant encoding and leaves
the exercised one intact. The concept survives; only the duplicate goes.

Keeping both is not cost-neutral. They can silently drift: nothing compares `VERSION` against
`__version__`, so a future `__version__` bump would leave `VERSION` stale with no test catching it.
That the drift has not yet materialized is only because neither has ever been bumped — through two
full theory rewrites (research §2.3).

The one capability genuinely given up is a non-Python consumer reading a theory's version off disk
without importing the package. Nothing does this today, and it is speculative.

**This is a deliberate contract change, and it needs a scope widening** (Phase 1) — that is the
honest cost of the better remedy, recorded rather than avoided.

### Remedies considered and rejected

| Remedy | Verdict |
|---|---|
| (b) keep files, exclude from wheel | **Rejected — demonstrated functional regression** (see risk closure above) |
| (c) keep files, pin `--ignore W002` permanently | Rejected. Formalizes a known finding forever when a genuine fix exists; the task explicitly forbids defaulting to "leave it be"; and it leaves the downstream release rehearsal stuck with an `--ignore W002` caveat |
| symmetric (b): exclude from wheel *and* sdist | Rejected. Same scaffolding breakage as (b) — the wheel is the path that matters — while still leaving four dead files on disk |
| Differentiate file contents (e.g. embed theory name) so they stop being byte-identical | Rejected. Nothing reads the files, so any content change is a purely cosmetic perturbation to silence a lint — precisely the anti-pattern task 155 forbade |
| **(a) remove files, single source of truth = `__version__`** | **Selected** |

### Research Integration

Research findings carried forward: nothing anywhere reads the `VERSION` files' *content* (§1); the
files' *presence* is asserted in three places across two contracts (§1, §4); W002 reproduces on a
fresh build (§5). Two research conclusions are **corrected** by this plan: the recommendation of
(b) (falsified by the risk-closure experiment above), and the claim that under (b)
`builder/project.py` is "unaffected" because scaffolding checks "the source tree / sdist-derived
checkout, not the wheel" (research §Recommendation.3) — it checks the installed package.

One site the research did not surface: `code/scripts/release-verify.sh` encodes the W002
expectation in its step ledger and reading notes. See "Downstream handoff" below — it is **not**
edited by this task.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; `ROADMAP.md` was not consulted. No
roadmap phases are included.

### Downstream handoff (not edited here)

`code/scripts/release-verify.sh` is **task 156's territory** and task 156 is currently
`[IMPLEMENTING]`. This task MUST NOT edit it. Once this task lands, three sites in that script
become stale and should be updated by task 156 (or task 151, the release rehearsal):

- line 15: step (d1) `check-wheel-contents (bare)` — labelled "expected nonzero (W002)
  [informational]"; should become the **hard gate**
- line 16: step (d2) `--ignore W002` — currently the hard gate; becomes unnecessary
- lines 52-57: the "Reading a nonzero check-wheel-contents (bare) exit" comment block

Phase 7 records this as an explicit handoff note. Task 151 (release rehearsal) consumes this
task's result and should then be able to record a **clean** `check-wheel-contents` rather than an
`--ignore W002` caveat.

## Goals & Non-Goals

**Goals**:
- Eliminate the W002 duplicate-file finding genuinely, so a plain `check-wheel-contents` on a
  freshly built wheel exits 0 **without** `--ignore W002`
- Consolidate per-theory versioning onto a single source of truth (`__init__.py`'s `__version__`)
- Keep the full packaging contract suite green, including the generate-then-execute journey
- Keep every phase green and independently committable

**Non-Goals**:
- Editing `code/scripts/release-verify.sh` (task 156's territory, in flight)
- Editing `specs/archive/125_.../PUBLISH-CHECKLIST.md` or other archived rehearsal evidence
- Bumping any theory's `__version__` value
- Adding a test that compares `__version__` across theories, or any new per-theory versioning
  feature
- Any push, tag, or PR (per `.claude/rules/pr-prohibition.md`)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing `VERSION` from the wheel before relaxing `REQUIRED_COPY_ITEMS` breaks project generation | H | H if misordered | Phase ordering is load-bearing: Phase 2 relaxes scaffolding **before** Phase 4 changes what ships. Phase 6 runs `test_generate_then_execute.py` as the catch |
| Another duplicate group surfaces and W002 still fires after removal | M | L | Derisked during planning: a content-hash sweep of the current wheel found **exactly one** non-empty duplicate group — the four `VERSION` files. Phase 5 still verifies empirically rather than assuming |
| Scope widening not recorded, implementer edits out-of-scope files silently | M | M | Phase 1 updates `state.json`'s `file_scope` explicitly and is a hard gate on later phases |
| Territory collision with task 156 on `release-verify.sh` | M | M | Explicit non-goal; Phase 7 produces a handoff note instead of an edit |
| Third-party/user theory still carrying a `VERSION` file triggers a spurious scaffolding warning | L | M | Phase 2 moves `VERSION` to `OPTIONAL_COPY_ITEMS` rather than deleting the entry, so it is tolerated-if-present but never required |
| Stale incremental build masks the result | M | M | Phase 5 removes `dist/`, `build/`, and `src/model_checker.egg-info/` before building (the trap `code/tests/packaging/conftest.py` itself documents) |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint trees
(`code/src/` vs `code/tests/packaging/`) and may run in either order or concurrently.

**Ordering is a correctness constraint, not a preference**: Phase 4 (stop shipping + delete) must
follow both Phase 2 (scaffolding no longer requires `VERSION`) and Phase 3 (packaging tests no
longer assert `VERSION`). Reversing this reproduces exactly the regression that disqualified
remedy (b).

---

### Phase 1: Record baseline and widen file_scope [COMPLETED]

**Goal**: Capture the pre-change evidence and legitimize the out-of-scope edits before making any.

**Tasks**:
- [ ] From `code/`: `rm -rf dist build src/model_checker.egg-info`, then
      `python3 -m build --no-isolation --outdir dist`
- [ ] Run `check-wheel-contents dist/*.whl`; record the W002 output and exit code (expect exit 1,
      four `VERSION` paths) into the task directory as baseline evidence
- [ ] Run the packaging contract suite once to establish a green baseline:
      `PYTHONPATH=code/src pytest code/tests/packaging/ -v`
- [ ] Update `specs/state.json` for project 157: append to `file_scope` the four widening entries
      below (append via `jq` `+=`; do **not** replace the array — see
      `.claude/rules/state-management.md`)
- [ ] Regenerate TODO.md: `bash .claude/scripts/generate-todo.sh`

**Scope widening — the four files added to `file_scope`**:

| File | Why it must change under remedy (a) |
|---|---|
| `code/src/model_checker/builder/project.py` | `REQUIRED_COPY_ITEMS` (line 52) fail-fasts on missing `VERSION` |
| `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` | `REQUIRED_ROOT_ITEMS` (line 44) asserts on-disk presence |
| `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` | line 44 is the contract text being changed |
| `code/MANIFEST.in` | line 17 `recursive-include src VERSION` ships it in the sdist |

**Note on already-in-scope files**: `code/src/model_checker/theory_lib/__init__.py` is in the
declared `file_scope` but requires **no change** — it contains no `VERSION` reference
(`get_theory_version_registry()` reads `__version__`). Do not invent one.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This plan asserts the complete edit set is 8 files (4 in declared scope, 4
added here) plus 4 deletions, and that no fifth out-of-scope site exists. Confirm at
implementation time with a fresh
`grep -rn -w VERSION code/ .github/ docs/ --exclude-dir={.git,oracle,dist,build,__pycache__}`;
any hit outside the enumerated set, `release-verify.sh` (handoff, not edited), or unrelated
shell-variable uses in `.github/workflows/release.yml` must be reported before proceeding.

**Files to modify**:
- `specs/state.json` - append four entries to project 157's `file_scope`
- `specs/TODO.md` - regenerated, not hand-edited

**Verification**:
- Baseline `check-wheel-contents` output recorded, showing exit 1 and the four `VERSION` paths
- `pytest code/tests/packaging/` passes before any source change
- `jq '.active_projects[]|select(.project_number==157).file_scope|length' specs/state.json`
  returns 11
- No prior `file_scope` entry was dropped

---

### Phase 2: Relax the on-disk contract requirements [NOT STARTED]

**Goal**: Stop requiring a `VERSION` file, while the files are still present and still shipped —
so the tree stays green throughout.

**Tasks**:
- [ ] `builder/project.py`: move `'VERSION'` from `REQUIRED_COPY_ITEMS` (line 52) into
      `OPTIONAL_COPY_ITEMS`, with a brief comment noting per-theory versioning is carried by
      `__init__.py`'s `__version__` and that the entry remains only so a third-party theory still
      carrying the file is copied rather than warned about
- [ ] `test_theory_conformance.py`: remove `'VERSION'` from `REQUIRED_ROOT_ITEMS` (line 44)
- [ ] `THEORY_ARCHITECTURE.md`: amend line 44's Theory Contract bullet to drop `VERSION` from the
      required metadata set, and state that per-theory version is `__init__.py`'s `__version__`
- [ ] Update the mirroring comments that name the contract file set where they cite `VERSION`:
      `pyproject.toml:71` and `MANIFEST.in:9-13` prose are handled in Phase 4; do not touch them here

**Rationale for OPTIONAL rather than outright removal**: after Phase 4 no in-tree theory has a
`VERSION` file, so the entry is inert for the four shipped theories. It costs nothing and prevents
`_copy_files`'s "skipped with a warning" path from firing for a user's own theory directory that
still carries one. This is not a backwards-compatibility shim — nothing reads the file either way.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Asserts exactly three files change in this phase and that no per-theory
`tests/` or `docs/` file asserts `VERSION` presence. Confirm with
`grep -rn -w VERSION code/src/model_checker/theory_lib/*/tests/ code/src/model_checker/theory_lib/*/docs/`
(expected: no matches) before closing the phase.

**Files to modify**:
- `code/src/model_checker/builder/project.py` - `VERSION` moved REQUIRED -> OPTIONAL
- `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` - drop from `REQUIRED_ROOT_ITEMS`
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` - amend Theory Contract text

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_theory_conformance.py -v`
  passes (files still on disk; requirement simply relaxed)
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v` passes
- Tree is green and this phase is independently committable

---

### Phase 3: Relax the packaging contract assertions [NOT STARTED]

**Goal**: Stop asserting `VERSION` ships, while it still does — again keeping the tree green.

**Tasks**:
- [ ] `test_inclusions.py`: remove `"VERSION"` from `REQUIRED_ROOT_FILES` (line 25); update the
      "Sourced from THEORY_ARCHITECTURE.md's Theory Contract" comment if it enumerates the set
- [ ] `test_parity.py`: remove `"VERSION"` from `_is_data_path()`'s name set (line 66) and update
      the module docstring at line 25 that names it
- [ ] Leave `test_exclusions.py` untouched — under remedy (a) the files do not exist to be
      excluded, so no `EXCLUSION_CLASSES` entry is warranted

**Note**: with `VERSION` removed from `_is_data_path()` but the files still shipped (until Phase
4), those members are classified as neither py-module nor data-path, so `test_data_path_parity`
simply ignores them. Parity holds throughout — this is why the phase is green in isolation.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Asserts `VERSION` appears in exactly two files under
`code/tests/packaging/` (`test_inclusions.py`, `test_parity.py`) and that removing it from
`REQUIRED_ROOT_FILES` drops 8 parametrized assertions (4 theories x 2 artifacts). Confirm with
`grep -rn -w VERSION code/tests/packaging/` (expected: no matches after the edits) and by
comparing collected test counts before/after.

**Files to modify**:
- `code/tests/packaging/test_inclusions.py` - drop `VERSION` from `REQUIRED_ROOT_FILES`
- `code/tests/packaging/test_parity.py` - drop `VERSION` from `_is_data_path()` + docstring

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/packaging/test_inclusions.py code/tests/packaging/test_parity.py -v`
  passes
- `grep -rn -w VERSION code/tests/packaging/` returns no matches
- Tree is green and this phase is independently committable

---

### Phase 4: Stop shipping and delete the four VERSION files [NOT STARTED]

**Goal**: Remove the duplication at its source. Safe only now that nothing requires or asserts it.

**Tasks**:
- [ ] `code/pyproject.toml`: remove `"VERSION",` from `[tool.setuptools.package-data]`'s `"*"`
      allowlist (line 76) and drop `VERSION` from the mirroring comment at line 71
- [ ] `code/MANIFEST.in`: remove `recursive-include src VERSION` (line 17); keep the
      allowlist-rationale comment block otherwise intact
- [ ] `git rm` the four files:
      `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION`
- [ ] Confirm wheel and sdist declarations remain mutually consistent (the two files' comments
      cross-reference each other; both must stop naming `VERSION`)

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Verification Tier**: interface

**Scope Hypothesis**: Asserts exactly four `VERSION` files exist under `theory_lib/`. Confirm with
`find code/src/model_checker/theory_lib -name VERSION` before deleting (expect 4) and after
(expect 0).

**Files to modify**:
- `code/pyproject.toml` - drop `VERSION` from package-data allowlist + comment
- `code/MANIFEST.in` - drop `recursive-include src VERSION`
- `code/src/model_checker/theory_lib/bimodal/VERSION` - **deleted**
- `code/src/model_checker/theory_lib/exclusion/VERSION` - **deleted**
- `code/src/model_checker/theory_lib/imposition/VERSION` - **deleted**
- `code/src/model_checker/theory_lib/logos/VERSION` - **deleted**

**Verification**:
- `find code/src/model_checker/theory_lib -name VERSION` returns nothing
- `grep -rn -w VERSION code/pyproject.toml code/MANIFEST.in` returns no packaging-rule matches
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_theory_conformance.py -v`
  still passes (contract already relaxed in Phase 2)

---

### Phase 5: Verify by rebuilding — plain check-wheel-contents must exit 0 [NOT STARTED]

**Goal**: Prove the remedy actually eliminated W002, from a from-scratch build, with no `--ignore`.

**Tasks**:
- [ ] From `code/`: `rm -rf dist build src/model_checker.egg-info` (mandatory — avoids the
      incremental-build staleness trap documented in `code/tests/packaging/conftest.py`)
- [ ] `python3 -m build --no-isolation --outdir dist`
- [ ] Run **`check-wheel-contents dist/*.whl`** with no `--ignore` flag; capture stdout and the
      exit code
- [ ] Confirm the wheel contains no `VERSION` members:
      `python3 -c "import zipfile,glob; print([n for n in zipfile.ZipFile(glob.glob('dist/*.whl')[0]).namelist() if n.endswith('/VERSION')])"`
- [ ] Record the before/after evidence pair (Phase 1 baseline vs. this run) in the task directory
- [ ] If any *new* W002 group appears, **stop and report it** — do not add `--ignore`, and do not
      perturb file contents to silence it

**Timing**: 0.5 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: Asserts the four `VERSION` files were the only duplicate-content group in
the wheel, so their removal clears W002 outright. Derisked during planning by a content-hash sweep
of the 1.3.0 wheel (exactly one non-empty duplicate group, the four `VERSION` files); this phase
confirms empirically on the rebuilt wheel rather than relying on that.

**Files to modify**:
- None (verification only). `code/dist/` is gitignored (`.gitignore:13`, `**/dist`), so the local
  build does not perturb the working tree.

**Verification**:
- `check-wheel-contents dist/*.whl` -> `OK`, **exit 0**, with no `--ignore W002`
- No `VERSION` member in the wheel namelist
- The sdist likewise contains no `src/model_checker/theory_lib/*/VERSION` member

---

### Phase 6: Full packaging contract suite, including the generate-then-execute journey [NOT STARTED]

**Goal**: Check the change in what ships against the whole packaging contract, and confirm
end-to-end scaffolding from a real installed wheel still works.

**Tasks**:
- [ ] Run the full suite: `PYTHONPATH=code/src pytest code/tests/packaging/ -v`
      (all of `test_inclusions.py`, `test_exclusions.py`, `test_parity.py`, `test_build_smoke.py`,
      `test_entry_point.py`, `test_cli_console_script.py`, `test_generate_then_execute.py`)
- [ ] Confirm `test_generate_then_execute.py` passes for **every** registered theory — this is the
      end-to-end scaffolding check: it installs the wheel into a real venv, generates a project via
      the `model-checker` console script, and executes it
- [ ] Independently spot-check generation against the freshly built wheel: unpack it to a temp dir,
      run `BuildProject('logos').generate('demo')` with `PYTHONPATH` pointed at the unpacked wheel,
      and confirm it succeeds and the generated project no longer contains a `VERSION` file
- [ ] Confirm no packaging test was skipped or deselected to make the suite pass

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- None (verification only)

**Verification**:
- `pytest code/tests/packaging/` — all tests pass, zero failures, zero unexpected skips
- `test_generate_then_execute` passes for all four theories
- Manual unpacked-wheel generation succeeds; generated project has no `VERSION` file
- Test counts reconcile with Phase 3's expected drop of 8 `VERSION` assertions

---

### Phase 7: Regression sweep, downstream handoff, and wrap-up [NOT STARTED]

**Goal**: Confirm nothing else regressed, and hand the now-stale W002 posture to task 156/151
without editing their files.

**Tasks**:
- [ ] Run the theory-conformance suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/ -v`
- [ ] Run the builder suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v`
- [ ] Final repo-wide sweep: `grep -rn -w VERSION code/ --exclude-dir={.git,dist,build,__pycache__}`
      — the only remaining hits should be `code/scripts/release-verify.sh` (handoff, deliberately
      untouched)
- [ ] Write the handoff note into the task summary: `code/scripts/release-verify.sh` lines 15, 16,
      and 52-57 now describe a W002 expectation that no longer holds; step (d1) (bare
      `check-wheel-contents`) should be promoted to the hard gate and step (d2) (`--ignore W002`)
      retired. Flag for task 156 (owner, currently `[IMPLEMENTING]`) and task 151 (release
      rehearsal, which can now record a clean run)
- [ ] Confirm no push, no tag, no PR was performed (`.claude/rules/pr-prohibition.md`)
- [ ] Confirm `git status` shows only intended files; `code/dist/` and `code/build/` remain
      untracked/ignored

**Timing**: 0.5 hours

**Depends on**: 6

**Verification Tier**: full

**Files to modify**:
- `specs/157_dedupe_theory_lib_version_files_w002/summaries/01_version-file-dedupe-summary.md` - created

**Verification**:
- Theory-conformance and builder suites pass
- Repo-wide `VERSION` sweep shows only the deliberately-untouched `release-verify.sh` hits
- Handoff note present in the summary, naming the three stale sites by line
- No remote-affecting git operation performed

---

## Testing & Validation

- [ ] Plain `check-wheel-contents` on a freshly built wheel exits **0** without `--ignore W002`
- [ ] Freshly built wheel and sdist contain **zero** `VERSION` members
- [ ] Full packaging contract suite (`code/tests/packaging/`) passes with no skips or deselections
- [ ] `test_generate_then_execute.py` passes for every registered theory (end-to-end scaffolding
      from a real installed wheel)
- [ ] Manual unpacked-wheel `BuildProject.generate()` succeeds
- [ ] Theory-conformance suite passes
- [ ] Builder suite passes
- [ ] Before/after `check-wheel-contents` evidence pair recorded

## Artifacts & Outputs

- Four `VERSION` files deleted; `__init__.py`'s `__version__` is the sole per-theory version source
- `code/pyproject.toml` and `code/MANIFEST.in` no longer ship `VERSION`
- `builder/project.py`, `test_theory_conformance.py`, `THEORY_ARCHITECTURE.md` no longer require it
- `code/tests/packaging/test_inclusions.py` and `test_parity.py` no longer assert it
- `specs/state.json` `file_scope` widened by four entries, recorded
- Before/after `check-wheel-contents` evidence
- Implementation summary with the `release-verify.sh` handoff note

## Rollback/Contingency

Each phase is independently committable and leaves the tree green, so rollback is per-phase
`git revert` in reverse order (7 -> 1). Reverting Phase 4 alone restores the four files and the
packaging declarations; the relaxed contracts from Phases 2-3 are harmless with the files present
(they become tolerated-but-not-required), so a partial rollback is safe in either direction.

If Phase 5 reveals a duplicate group other than `VERSION`, stop: do **not** add `--ignore`, and do
**not** alter file contents to silence it. Record the finding and raise it as a separate task — the
posture task 155 established (`check-wheel-contents` is a local verification strengthening, not a
blocking gate) means there is no urgency justifying a cosmetic workaround.

If Phase 6 shows any scaffolding regression, revert Phase 4 immediately — that restores what ships
and unblocks generation while the cause is diagnosed.
