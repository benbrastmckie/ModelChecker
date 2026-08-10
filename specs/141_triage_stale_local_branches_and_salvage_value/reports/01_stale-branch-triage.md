# Research Report: Task #141

**Task**: 141 - Triage the 9 stale local-only branches, salvage anything of value, then retire them
**Started**: 2026-08-10T00:00:00Z
**Completed**: 2026-08-10T00:00:00Z
**Effort**: research-only (read-only git inspection)
**Dependencies**: None
**Sources/Inputs**: git (merge-base, diff, log, ls-tree, rev-list), current working tree at `code/src/model_checker/`
**Artifacts**: - this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- All nine premises in the task description are confirmed by direct command output: the nine
  branches exist only locally, origin's ten branches are a disjoint older set, and every one of
  the nine shares one identical, very old merge-base with `master`
  (`fcf2b95` — "Release... 2024-02-08", tagged `2024-02-08 18:05:44 -0500`). That shared
  merge-base predates the repository restoration by well over a year, which is exactly why raw
  `master..branch` commit counts (1978–2108) are meaningless as a measure of unique work — they
  count almost the entire pre-restoration project history, not branch-specific content.
- Using **pairwise branch-to-branch merge-bases** (not the master merge-base) reveals the real
  structure: three internal ancestor chains exist. `bimodal_witness_backup` → `bimodal_witness`
  (first-generation witness-predicate attempt), `bimodal_refactor` → `witness-falsity-attempt`
  and `bimodal_refactor` → `quantifier-free-witnesses` (second-generation attempt, forked twice),
  and `cvc5-feasibility-test` → `bimodal-cvc5-pilot`. Once these ancestries are followed, the
  *substantive* unique content per branch is a handful of commits and a few hundred lines each,
  not thousands.
- The current tree (`code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`,
  `witness_registry.py`) already contains code ~90% textually identical to `bimodal_refactor`'s
  version, including the `_witness_constraint_for_falsity()` method that `witness-falsity-attempt`
  introduced. The witness-predicate refactor line is **superseded** — its destination already
  exists in `master`, in cleaner form.
- The two cvc5 branches contain a genuinely irreplaceable, un-superseded finding: cvc5 with
  `mbqi`+`enum-inst` solves `BM_CM_1` deterministically in ~6ms where **both** Z3 approaches
  (quantified and quantifier-free) timed out — an ~850× speedup, validated across all 6 critical
  countermodel examples. Separately, current `master` already has a generic, cross-theory solver
  abstraction (`code/src/model_checker/solver/`, added under later, unrelated tasks) offering a
  `cvc5` backend, and `bimodal`'s settings already expose `'solver': 'z3'|'cvc5'` — but nobody has
  verified end-to-end that bimodal actually produces correct countermodels through that path today.
  Both facts belong in a written record.
- `refactor/exclusion`'s stated goals (helper/validation quick wins, standardized error handling,
  caching, expanded docstrings) are already present in current `master`'s `exclusion/` package
  (modular `semantic/core.py`/`model.py`/`registry.py`, a `_predicate_cache`, and later
  normalization work) — superseded.
- `new_claude` modifies only files under `.claude/`, which is **git-ignored at the repository
  root** (`.gitignore:36: /.claude`) in current `master`. Its content (task numbering 1–351, an
  early single-file CLAUDE.md editing workflow) belongs to an architecture this repository no
  longer version-controls at all — superseded/moot, not merely superseded.

**Recommended approach**: (a)/(b) for six branches (delete after bundling — no port needed, code
already superseded), (c) for `feature/cvc5-feasibility-test` and `feature/witness-falsity-attempt`
(write two short findings, then delete after bundling), and (c)-leaning for
`feature/bimodal-cvc5-pilot` (write one short finding about a reproducible cvc5 segfault, then
delete after bundling). No branch merits (d) "unclear" — every one has enough evidence for a
confident, evidence-grounded verdict, none of which is (b) "port code as-is."

## Context & Scope

This is the research phase only. No branches were created, deleted, merged, checked out, or
bundled. No source files were modified. All git commands used were read-only
(`merge-base`, `diff --stat`/`--shortstat`, `log`, `show`, `ls-tree`, `rev-list`, `branch -v`,
`for-each-ref`, `merge-base --is-ancestor`). The working tree remained on
`task-140-fix-bimodal-order-dependence` throughout.

## Findings

### 1. Verification of Premises

**All nine branches are local-only; origin carries a disjoint, older set.**

```
$ git branch -r --no-color
  origin/HEAD -> origin/master
  origin/exclusion_attempt_9
  origin/false_premise
  origin/finean_exclusion
  origin/iterate
  origin/master
  origin/new_defined_operator
  origin/old_jupy
  origin/pre-full-skolem
  origin/reduced_exclusion
  origin/refactor_exclusion_single_strategy
```

This matches the task description's claim exactly (10 remote refs including `HEAD`/`master`,
none of the nine names present). `git for-each-ref refs/remotes` returns the identical list.
Confirmed as stated — no correction needed.

**Last-commit dates and raw `rev-list --count master..branch`** (all measured, not estimated):

| Branch | Last commit date | `master..branch` count | Matches task's stated count |
|---|---|---|---|
| bimodal_refactor | 2025-10-02 | 2046 | yes |
| feature/bimodal-cvc5-pilot | 2025-11-05 | 2066 | yes |
| feature/bimodal_witness | 2025-09-24 | 1992 | yes |
| feature/bimodal_witness_backup | 2025-09-23 | 1978 | yes |
| feature/cvc5-feasibility-test | 2025-10-02 | 2050 | yes |
| feature/quantifier-free-witnesses | 2025-10-02 | 2051 | yes |
| feature/witness-falsity-attempt | 2025-10-02 | 2047 | yes |
| new_claude | 2026-01-10 | 2108 | yes |
| refactor/exclusion | 2025-10-01 | 2049 | yes |

**Merge-base with `master` is identical across all nine branches**:

```
$ git merge-base master <branch>   # identical for all 9
fcf2b95779b0d77ea76514546b345529875f47e4
$ git log -1 --format=%ci fcf2b95779b0d77ea76514546b345529875f47e4
2024-02-08 18:05:44 -0500
```

This is the key mechanical confirmation of the task's inflated-count hypothesis: because every
branch's merge-base with `master` is the *same* single, ancient commit — and `master` itself has
2938 commits since that point (`git rev-list --count <branch>..master`) from the unrelated
restoration effort — the raw `master..branch` count is not "branch work," it is "everything the
branch inherited from before the divergence plus whatever the branch actually added." A
`diff --stat` against that same ancient point is *also* misleading for the same reason (see next
section) — it reflects the entire pre-restoration repository shape, not branch-specific content.
**Correction to the task's own suggested method**: diffing against `$(git merge-base master
<branch>)` does not, by itself, fix the inflation, because master's merge-base predates nearly the
entire current directory structure. The technique that actually isolates real content is
**pairwise branch-to-branch `merge-base --is-ancestor` and `merge-base`** (Section 3), which
reveals several branches are literal git ancestors of each other.

### 2. Per-Branch Real Delta

All nine share `merge-base master <branch> = fcf2b95` (2024-02-08). `diff --stat` against that
point is included per the task's request, but — as explained above — it is dominated by
pre-restoration repository-wide churn (a `Code/` → `code/` case rename alone accounts for
hundreds of "changed" files) and is **not** a reliable delta measure. The pairwise numbers in
Section 3 are the reliable ones.

| Branch | `diff --stat` vs `fcf2b95` | Commits since `fcf2b95` | Commits since *nearest real ancestor* (Section 3) |
|---|---|---|---|
| bimodal_refactor | 712 files, +186648/−548 | 2046 | 70 (since `338f090e`, 2025-09-18) |
| feature/bimodal_witness | 646 files, +167239/−548 | 1992 | 16 (since `338f090e`) |
| feature/bimodal_witness_backup | 631 files, +167069/−548 | 1978 | 2 (since `338f090e`) |
| feature/quantifier-free-witnesses | 718 files, +189632/−548 | 2051 | 6 (since `bimodal_refactor` tip `274fa0e9`) |
| feature/witness-falsity-attempt | 712 files, +189095/−548 | 2047 | 1 (since `bimodal_refactor` tip `274fa0e9`) |
| feature/cvc5-feasibility-test | 727 files, +189875/−548 | 2050 | 4 (since `bimodal_refactor` tip `274fa0e9`) |
| feature/bimodal-cvc5-pilot | 758 files, +200524/−548 | 2066 | 19 (since `feature/cvc5-feasibility-test` tip `26e0a067`) |
| refactor/exclusion | 683 files, +175136/−548 | 2049 | 2049 (no ancestor relation found to any other of the 9) |
| new_claude | 837 files, +225459/−548 | 2108 | 2108 (no ancestor relation found; predates `.claude/` being gitignored) |

Note on `−548 deletions` repeated identically across every row: this is the fixed set of files
deleted between `fcf2b95` and *any* current-era tree (not branch-specific) — further evidence the
master-merge-base diff is measuring the shared pre-restoration→post-restoration gap, not
per-branch content.

**Per-branch prose** (substantive files, ignoring `.gitignore`/lockfile noise):

- **bimodal_refactor** (70 commits since `338f090e`): full second-generation rewrite of bimodal's
  witness-predicate machinery into a `semantic/` subpackage
  (`Code/.../bimodal/semantic/witness_constraints.py`, `witness_registry.py`,
  `Code/.../bimodal/semantic.py`). Ends mid-optimization-and-revert cycle (`fix(bimodal): revert
  all optimizations, restore correctness`).
- **feature/bimodal_witness** (16 commits since `338f090e`, itself built on
  `feature/bimodal_witness_backup`): first-generation witness-predicate attempt using a flat
  `witness.py`/`semantic_backup.py` layout (not the `semantic/` subpackage layout later branches
  and current `master` use). Final commit: "consolidated bimodal theory."
- **feature/bimodal_witness_backup** (2 commits since `338f090e`): a checkpoint commit ("paused
  first refactor to redesign implementation") immediately preceding `feature/bimodal_witness`.
- **feature/quantifier-free-witnesses** (6 commits on top of `bimodal_refactor`'s tip): adds
  `generate_witness_constraints_quantifier_free()` and a `quantifier_free_witnesses` setting,
  enumerating `(world, time)` pairs instead of using `z3.ForAll`, to eliminate observed
  non-determinism; marked "production-ready" in its final commit.
- **feature/witness-falsity-attempt** (1 commit on top of `bimodal_refactor`'s tip): adds
  `_witness_constraint_for_falsity()` (a `ForAll`-based falsity constraint for `Box.false_at()`)
  plus a 2395-line `WITNESS_PREDICATES.md`. Commit message explicitly flags non-deterministic
  behavior and states the branch is being preserved before trying the quantifier-free approach.
- **feature/cvc5-feasibility-test** (4 commits on top of `bimodal_refactor`'s tip): adds
  6 standalone cvc5 test scripts, `specs/reports/011_z3_to_cvc5_api_translation.md`, and
  `specs/reports/012_cvc5_feasibility_results.md`, reporting cvc5 (with `mbqi`+`enum-inst`)
  solving all 6 critical countermodel examples deterministically, ~850× faster than Z3 on the
  hardest case.
- **feature/bimodal-cvc5-pilot** (19 commits on top of `feature/cvc5-feasibility-test`'s tip,
  the rest of its 2066-commit `master..branch` count is inherited pre-restoration history): a
  12-"stage" attempt at migrating the whole bimodal theory to use cvc5 directly, ending in an
  uncommitted-message tip ("in progress working on cvc5") and a `test_segfault_debug.py`
  reproduction script for a `CallableFunction`-related cvc5 segfault. No completion or
  abandonment report exists on the branch.
- **refactor/exclusion** (2049 commits since `fcf2b95`, no ancestor relation to any of the other
  8 branches; nearest common point with `bimodal_refactor` is `7dc84490`, "Release version
  1.2.11," 2025-09-29): four "Phase" commits — quick-win helpers/validation, standardized error
  handling, caching, and expanded docstrings — for the `exclusion` theory's witness-predicate
  code, adding `48` files / `12341` insertions relative to its own merge-base with master when
  restricted to the `exclusion/` subtree.
- **new_claude** (2108 commits since `fcf2b95`, no ancestor relation to the other 8): entirely
  `.claude/`-scoped commits (149 files in that tree on the branch vs. 0 tracked in current
  `master`, since `.claude/` is git-ignored today). Tip commit: "docs: address FIX tags in
  user-installation.md," touching `.claude/docs/guides/user-installation.md`, dated 2026-01-10 —
  the most recent of the nine, but working in a subsystem the repository no longer tracks.

### 3. Thematic Analysis

**Bimodal-witness theme (5 branches) — internal ancestor graph, established via
`git merge-base --is-ancestor`:**

```
feature/bimodal_witness_backup  --(2 commits, Sep 23)-->  feature/bimodal_witness  (Sep 24)
        [abandoned: "paused first refactor to redesign implementation"]

bimodal_refactor (Oct 2, 70 commits since Sep 18 base)
        ├──(1 commit)──> feature/witness-falsity-attempt   (Oct 2, same day)
        └──(6 commits)──> feature/quantifier-free-witnesses (Oct 2, same day)
```

`bimodal_witness`/`bimodal_witness_backup` are **not** ancestors of `bimodal_refactor` (confirmed
via `merge-base --is-ancestor` returning false both directions) — they are a separate,
first-generation line using a different file layout (`witness.py` directly under `bimodal/`, not
a `semantic/` subpackage), abandoned in favor of the `bimodal_refactor` redesign. `bimodal_refactor`
itself forks twice at its own tip into the two remaining branches, which therefore share
`bimodal_refactor`'s content as a strict prefix.

**Comparison against current `master`**: `master`'s
`code/src/model_checker/theory_lib/bimodal/semantic/` already contains `core.py`, `model.py`,
`proposition.py`, `witness_constraints.py`, `witness_registry.py` — the same subpackage shape
`bimodal_refactor` introduced (not the flat `witness.py` shape of the first-generation branches).
`git diff --stat` between `bimodal_refactor:.../witness_constraints.py` and
`master:.../witness_constraints.py` shows only 6 insertions / 77 deletions on a 257→186-line
file — i.e. `master`'s version is a trimmed variant of the same design, not a different one.
`master`'s `_witness_constraint_for_falsity()` is present and `ForAll`-based, matching what
`witness-falsity-attempt` introduced. `master` has **no** `quantifier_free_witnesses` setting and
`witness_constraints.py` still uses `z3.ForAll` (4 occurrences) — the quantifier-free path was
never adopted.

**cvc5 theme (2 branches) — ancestor confirmed:**

```
feature/cvc5-feasibility-test (Oct 2, 4 commits on bimodal_refactor's tip)
        --(19 commits, through Nov 5)--> feature/bimodal-cvc5-pilot
```

Comparison against current `master`: `master` has an entirely separate, generic
`code/src/model_checker/solver/` package (`protocols.py`, `registry.py`, `z3_adapter.py`,
`cvc5_adapter.py`, `expressions.py`, `compat.py`) added under unrelated later tasks, plus a
`model_checker.z3_shim` transitional dispatch shim used by `bimodal`, `exclusion`, `imposition`,
and `logos`. `bimodal`'s `semantic/core.py` DEFAULT_GENERAL_SETTINGS already includes `'solver':
'z3'` with a comment `# Solver backend: 'z3' or 'cvc5'`. This is architecturally a *different,
cleaner* solution to the same underlying goal the pilot branch pursued (enable cvc5 for bimodal)
— generic across all theories rather than a bimodal-specific rewrite — and it post-dates the
stale branches. However, nothing in `master`'s tests or docs demonstrates that setting
`'solver': 'cvc5'` on bimodal actually produces correct countermodels end-to-end today; this is
an open question, not a superseded claim (see Risks, below).

**Exclusion-refactor theme (1 branch):** `refactor/exclusion` has no ancestor relationship to any
of the other 8 branches (nearest shared point with `bimodal_refactor` is `7dc84490`, a plain
release tag commit, not thematically connected). Comparison against current `master`: `master`'s
`exclusion/semantic/` package already has the modular split (`core.py`, `model.py`, `registry.py`,
`constraints.py`) and a working `_predicate_cache` in `registry.py`, plus later normalization
commits (`task 126 phase 17: normalize exclusion`, `task 126 phase 24: documentation
reconciliation`) that post-date and extend past what `refactor/exclusion`'s four "Phase" commits
did.

**Docs/tooling theme (1 branch):** `new_claude` touches only `.claude/`, which
`git check-ignore -v .claude/CLAUDE.md` confirms is excluded via `.gitignore:36: /.claude` in
current `master`. `git log --oneline master -- .claude/CLAUDE.md` shows a commit literally titled
"removed claude" in `master`'s history — `.claude/` was deliberately untracked at the repository
level at some point, and per this repository's own CLAUDE.md ("This file is generated
automatically from loaded extensions"), is now managed by an external sync mechanism, not
per-repo commits. `new_claude`'s content (task numbers 1–351, single-file CLAUDE.md workflow) is
therefore not merely superseded by newer `.claude/` content — it targets a version-control
scheme this repository no longer uses for that directory at all.

### 4. cvc5 and Negative-Result Extraction

**`feature/cvc5-feasibility-test` — the central finding.** Quoting directly from the branch's own
commits (`fb3f58b2`, `edcf5c7f`, `bf082cd5`, `26e0a067`):

> "BREAKTHROUGH RESULT: CVC5 with MBQI+enum-inst solves BM_CM_1 perfectly! ... Average time: 6ms
> (vs Z3's 5s+ timeout) ... 850× faster than Z3 ... CVC5 succeeds where BOTH Z3 approaches fail:
> Z3 quantified witnesses: Timeout / Z3 quantifier-free witnesses: Timeout (Plan 103 failed) /
> CVC5 MBQI+enum-inst: SUCCESS in 6ms ... Configuration critical: Default CVC5: Returns 'unknown'
> immediately / With mbqi+enum-inst: Solves perfectly."

> "Extended CVC5 validation to cover complete functionality requirements... 100% success rate
> (30/30 runs), 100% determinism (all tests identical across 5 runs)... No functionality loss:
> All countermodels found correctly." — covering `BM_CM_1`, `BM_CM_2`, `TN_CM_1`, `TN_CM_2`,
> `MD_CM_1`, `MD_CM_2`.

What it cost: 4 commits, ~3200 inserted lines (mostly standalone test scripts and two reports),
one working day (2025-10-02). Why not kept as-is: the branch's own follow-on
(`feature/bimodal-cvc5-pilot`) attempted the natural next step — a real, non-standalone migration
— and stalled on a reproducible segfault (below) without ever reaching a merge-ready state; the
generic solver-abstraction approach `master` later adopted (Section 3) supersedes the
*implementation* strategy even though it does not, by itself, prove the *feasibility finding*
false or already re-validated.

**`feature/bimodal-cvc5-pilot` — the follow-on and its unresolved defect.** Tip commit message is
literally just `"in progress working on cvc5"` (`222add95`). The branch includes
`test_segfault_debug.py`, a minimal reproduction attempting `adapter.apply_function(is_world,
[world_id])` through the `cvc5` adapter and titled `"Test to reproduce CVC5 segfault with
CallableFunction."` No specs report or commit documents the segfault's resolution or the
project's decision to pause — the pilot simply stops. This is exactly the kind of result that
disappears silently if the branch is deleted without a note: a future attempt to wire cvc5 into
bimodal (which `master`'s own `'solver': 'z3'|'cvc5'` setting comment invites) would otherwise
have to rediscover this failure mode from scratch.

**`feature/witness-falsity-attempt` — negative result, partially superseded.** Quoting its commit
message (`c89f5327`) directly:

> "NOTE: The falsity constraint implementation exhibits non-deterministic behavior (works
> sometimes, fails others) due to Z3's ForAll quantifier instantiation heuristics. This branch is
> being preserved before attempting Option D (quantifier-free encoding) on a new branch."

Cross-referenced against this repository's own `specs/reports/007_box_countermodel_failure_
investigation.md` on the same branch: "**Root Cause**: Missing falsity constraint in witness
predicate generation... The witness constraints ensure witnesses are valid worlds but don't
ensure the argument is false there." The falsity-constraint *fix itself* is confirmed present and
adopted in current `master` (Section 3). But the diagnosed *cause* of the accompanying
non-determinism — "Z3's ForAll quantifier instantiation heuristics" — is worth re-examining
against this same repository's very recent, independent finding on the active working branch
(`task-140-fix-bimodal-order-dependence`, commit `71d437bd`, not part of this task's branch set
but directly relevant): the actual root cause of bimodal order-dependence was a **process-global
`_bound_var_counter` in `operators.py` that leaked its numeric suffix across tests**, not an
inherent property of `ForAll` instantiation. The two investigations describe the same *symptom*
(non-deterministic Box-example results tied to quantifier/bound-variable naming) roughly a year
apart, reaching different root-cause attributions. This convergence — and divergence — is exactly
the kind of fact that is cheap to write down now and expensive to rediscover later.

### 5. Proposed Classification

| Branch | Verdict | Justification |
|---|---|---|
| `bimodal_refactor` | **(a) superseded** | Its `semantic/` subpackage layout and witness-constraint/registry code are ~90% textually present in current `master`, including the falsity constraint; nothing in its 70 commits beyond its own children is absent from `master`. |
| `feature/bimodal_witness` | **(a) superseded** | First-generation attempt with a flat-file layout the project itself abandoned ("paused first refactor to redesign implementation") in favor of the `bimodal_refactor` line that reached `master`. |
| `feature/bimodal_witness_backup` | **(a) superseded** | A 2-commit checkpoint that is a strict git ancestor of `feature/bimodal_witness`, itself superseded; nothing here is not already in its child. |
| `feature/quantifier-free-witnesses` | **(c) finding worth recording** | The quantifier-free encoding was built, tested, and marked "production-ready," but was never adopted in `master` (no `quantifier_free_witnesses` setting exists today) and the underlying non-determinism it was designed to work around now has a different, independently-confirmed root cause (task-140's bound-variable-counter fix). The finding — "a working quantifier-free alternative exists and was abandoned, and a later fix addressed the same symptom by a different, smaller mechanism" — belongs in `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`, so nobody re-derives quantifier-free witnesses from scratch chasing a bug that already has a one-line fix. |
| `feature/witness-falsity-attempt` | **(c) finding worth recording** | The code (falsity constraint) is already in `master`; the diagnostic note ("non-determinism due to ForAll instantiation heuristics") is now supersedable by task-140's more precise root cause. Worth a short cross-reference note in `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` tying report 007's "missing falsity constraint" finding to the later bound-variable-counter finding, so future readers don't re-attribute future non-determinism to "ForAll is inherently non-deterministic" without checking the counter first. |
| `feature/cvc5-feasibility-test` | **(c) finding worth recording** | The single highest-value, wholly un-superseded fact among all nine branches: cvc5 with `mbqi`+`enum-inst` solves the hard bimodal countermodel case Z3 cannot, deterministically, ~850× faster, validated on 6 examples. No code needs to move (it was 6 standalone scripts against an ad hoc setup, not integrated with the current solver abstraction) but the *result* should live in `code/src/model_checker/solver/README.md` or a new `code/docs/development/` note, since `master`'s existing `cvc5_adapter.py`/`'solver': 'cvc5'` setting make this directly actionable today. |
| `feature/bimodal-cvc5-pilot` | **(c) finding worth recording** | No reusable code (mid-flight, mixed with an unresolved segfault, superseded architecturally by `master`'s generic solver abstraction), but the segfault itself (`CallableFunction` via the cvc5 pythonic API) is a concrete, reproducible risk that anyone flipping bimodal's `'solver'` setting to `'cvc5'` today should know about. Worth one paragraph alongside the feasibility-test finding. |
| `refactor/exclusion` | **(a) superseded** | `master`'s `exclusion/semantic/` package already has the modular split, caching, and expanded docs the branch's four "Phase" commits targeted, extended further by later normalization work (task 126) that post-dates the branch. |
| `new_claude` | **(a) superseded** | Targets `.claude/`, which is git-ignored in current `master` and managed by an external sync mechanism per this repository's own CLAUDE.md; the branch's task-numbering scheme (1–351) and file layout no longer correspond to anything version-controlled here. |

No branch was assigned **(b) reusable code as-is**: every piece of code identified as present-in-
spirit is already more cleanly implemented in `master` (bimodal witness/falsity constraints,
exclusion caching/modularity), and the cvc5 pilot's code is both incomplete and architecturally
superseded by the generic solver package. No branch was assigned **(d) unclear** — every branch
has a specific, evidence-grounded classification above; where the evidence was more circumstantial
(e.g., `refactor/exclusion`'s content vs. `master`'s having converged independently rather than
being literally derived from the branch), the report says so explicitly rather than overclaiming
lineage.

## Decisions

- Use pairwise branch-to-branch `merge-base`/`--is-ancestor`, not master-merge-base `diff --stat`,
  as the primary tool for establishing real branch content — the master-merge-base diff is
  dominated by a repository-wide `Code/`→`code/` rename and is not informative on its own.
- Treat `feature/cvc5-feasibility-test` and `feature/witness-falsity-attempt` (and, more weakly,
  `feature/bimodal-cvc5-pilot`) as the three branches meeting the task's own bar for (c): a
  negative or noteworthy result that is cheap to write down and expensive to rediscover.
- Recommend homes for findings: bimodal/ForAll findings → `code/src/model_checker/theory_lib/
  bimodal/docs/ARCHITECTURE.md`; cvc5 feasibility + segfault findings →
  `code/src/model_checker/solver/README.md` (or a new file under `code/docs/development/` if the
  implementer judges `solver/README.md` too narrowly scoped to the abstraction layer itself).

## Risks & Mitigations

- **Open question, not resolved by this research**: whether `bimodal`'s existing `'solver':
  'cvc5'` setting actually produces correct results today. This report only establishes that the
  *generic infrastructure* exists in `master`; it does not run bimodal against cvc5 (out of scope
  for read-only research; would require installing/invoking cvc5, which this phase's constraints
  disallow). The implementation phase, or a follow-up task, should verify this before treating the
  cvc5 feasibility finding as "already actioned."
- **`refactor/exclusion`'s "superseded" verdict rests on structural similarity, not a confirmed
  merge lineage** (no ancestor relationship exists to tie it to `master`'s current exclusion code)
  — it is possible `master`'s exclusion caching/modularity was arrived at independently rather
  than derived from this branch. This does not change the recommended action (retire — nothing in
  the branch is missing from `master`'s functional coverage of the same goals) but the
  implementation phase should not describe `master`'s exclusion code as "ported from"
  `refactor/exclusion` in any doc.
- **Deletion timing**: per the hard constraints, none of the nine branches should be deleted until
  this triage is recorded (this report) — that condition is now satisfied for all nine. The
  remaining precondition (per-branch git bundle written outside the repo, `git bundle verify`d,
  and its location recorded in this task's artifacts) has **not** been executed — bundling and
  `git branch -D` are explicitly out of scope for this read-only research phase and belong to the
  implementation phase.
- **No branch requires premature-deletion caution beyond the standard bundle-first requirement.**
  All nine have a confident verdict; none is flagged (d) unclear.

## Context Extension Recommendations

- **Topic**: bimodal witness-predicate design history and the ForAll-non-determinism episode.
  **Gap**: `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` documents the current
  design but not why the quantifier-free alternative was tried and dropped, nor the connection
  between the original "ForAll instantiation heuristics" diagnosis and the later, more precise
  bound-variable-counter root cause. **Recommendation**: implementation phase adds a short
  "Design History" or "Known Non-Determinism Investigations" subsection there, citing this
  report's Section 4 findings (durably, without referencing branch names or task numbers per
  repository convention).
- **Topic**: cvc5 as an alternative solver backend for bimodal. **Gap**: `code/src/model_checker/
  solver/README.md` documents the abstraction's existence but not the concrete evidence for
  *why* a cvc5 backend is worth having (the 850× speedup finding) or the one known integration
  risk (`CallableFunction` segfault). **Recommendation**: implementation phase adds a short
  "Background" or "Known Issues" note there.

## Appendix

**Key commands used** (representative; full session ran these per-branch for all 9 branches):

```
git branch --list -v --no-color
git branch -r --no-color
git for-each-ref refs/remotes --format='%(refname)'
git merge-base master <branch>
git log -1 --format=%ci <merge-base>
git rev-list --count master..<branch>
git diff --shortstat <merge-base>..<branch>
git merge-base <branchA> <branchB>
git merge-base --is-ancestor <branchA> <branchB>
git log --oneline <ancestor>..<branch>
git log --format='%H %ad ---%n%B' --date=short <rangeA>..<rangeB>
git show --stat <commit>
git show <branch>:<path>            # for file content comparison
git diff --stat <treeA> <treeB> -- <path>
git ls-tree -r --name-only <branch> [-- <path>]
git check-ignore -v .claude/CLAUDE.md
```

**Key commits referenced**:
- `fcf2b95779b0d77ea76514546b345529875f47e4` — shared master-merge-base for all 9 branches (2024-02-08)
- `338f090e3184b49ee7d0977acd921db8968bffa1` — shared base of the bimodal-witness first/second generation split (2025-09-18)
- `274fa0e93478528e690197a535dbb3e053e551ef` — `bimodal_refactor` tip ("ignore metrics"), fork point for `witness-falsity-attempt` and `quantifier-free-witnesses`
- `26e0a067fd58048c89dace1f5784c6f4cbd1f4c7` — `feature/cvc5-feasibility-test` tip, ancestor of `feature/bimodal-cvc5-pilot`
- `c89f53274bf6035f00a28bd3af559f85708ef8d3` — `feature/witness-falsity-attempt` tip
- `01635e4aa26e45f8e9ac436940b17c996aacd7d9` — `feature/quantifier-free-witnesses` tip
- `222add956f4aed777da9baebfe4426dfdce52633` — `feature/bimodal-cvc5-pilot` tip ("in progress")
- `0b9ddd05` — `refactor/exclusion` tip
- `814872a81b78d35d56fbe3d0c2fe3965ad2ab585` — `new_claude` tip
- `71d437bd868b56d7bb28df1e4c0cc017b1fa7bfa` — task-140's bound-variable-counter root-cause fix, on the current working branch, cross-referenced in Section 4/5
