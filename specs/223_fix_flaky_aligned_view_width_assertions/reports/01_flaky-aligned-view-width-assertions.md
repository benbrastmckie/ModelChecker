# Research: Fix flaky 80-column `-a` header width assertions

## Task

Fix the two flaky display tests that assert a hard `<= 80` column bound on the bimodal `-a`
(`align_vertically`) header, which fails nondeterministically depending on which roles Z3's
certificate search assigns. Tests-only scope: no printer, semantics, certificate-search, or
truth-value change.

## Failing tests (confirmed locations)

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py:655` —
  `TestRoleColumnIsBounded::test_aligned_view_header_and_rows_stay_within_80_columns`:
  `assert max(len(line) for line in body_lines) <= 80`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py:245` —
  `TestEndToEndWidthGate::test_aligned_view_header_stays_within_80_columns_for_the_named_case`:
  `assert len(header) <= 80`

Both exercise the same example: premise `\Box (A \vee B)`, conclusions `\Box A`, `\Box B`,
`back=2, mid=1, fwd=2` (`MD_CM_1` shape), with `align_vertically: True`.

## Root cause, reproduced locally

`BimodalStructure._lasso_roles` (`code/src/model_checker/theory_lib/bimodal/semantic/model.py:502-521`)
assigns each lasso index one of exactly three role strings: `"main"` (index 0), `"witness"` (a
lasso the certificate names as a falsifier of some boxed subformula, via `box_guesses()`), or
`"reserved, unused"` otherwise. `"witness"` is 7 characters; `"reserved, unused"` is 16 — a
9-character difference.

`_print_history_table` (`model.py:533-574`) builds one header cell per lasso as
`f"L{index} {roles[index]}"` and pads every column in that lasso's position to the header cell's
own width (`model.py:555-558`). Because the aligned-view cell contents (`[B]`, `B`, etc.) are far
shorter than either role string, **each column's rendered width is dominated by its own header
cell's role string**, not by any position data. So the header's total width is driven directly by
how many lassos the draw resolves to `"reserved, unused"` versus `"witness"`.

Reproduced directly against the named case (`PYTHONPATH=code/src`, `_build` from
`tests/_build_support.py`):

```
roles = {0: 'main', 1: 'witness', 2: 'reserved, unused', 3: 'witness'}
header = '   t  slot     | L0 main | L1 witness | L2 reserved, unused | L3 witness'
len(header) == 72
```

This is the passing draw (8-column margin under 80). Which lassos resolve to `"witness"` versus
`"reserved, unused"` depends on `box_guesses()`'s witness extraction over whichever certificate
Z3's solver returns for this satisfiable encoding — the encoding does not pin
`sat.random_seed`/`smt.random_seed` anywhere in the codebase (confirmed: no occurrence of either
param, or of `z3.Solver()`'s seed, under `theory_lib/bimodal/semantic/`), so distinct equally-valid
models are a legitimate solver outcome, not a bug in the search. Substituting one `"witness"` for
`"reserved, unused"` in the header formula adds exactly 9 columns (72 → 81, matching the CI-observed
`82 <= 80`/`81 <= 80` failures to within rounding of which example build hit the same mechanism);
substituting two adds 18 (→ 90). This is an exact, mechanical consequence of the header-cell-width
formula above, not a coincidence.

**The tests cannot make Z3 reliably return the 4-role draw they were written against.** Pinning a
Z3 seed is not a standing pattern anywhere in this codebase (`grep` for `random_seed`/`set_param`
under `theory_lib/` turns up nothing outside `solver/expressions.py`'s generic passthrough and
`builder/runner.py`'s per-example `z3.reset_params()`/`z3.set_param(verbose=0)`, neither of which
fixes a seed), and `pyproject.toml` pins `z3-solver>=4.8.0` with no upper bound, so even a
newly-added seed pin offers no cross-version guarantee.

## Key finding: the project's own codified 80-column rule does not cover the `-a` view

`code/docs/core/CODE_STANDARDS.md:629-635` ("Printed Output Conventions") states the convention
precisely:

> **No line of a default (non-`-a`) model-output run exceeds 80 columns.** ... Enforced by
> `theory_lib/bimodal/tests/integration/test_output_gate.py::TestEndToEndWidthGate`.

The codified contract is explicitly scoped to the **default (non-`-a`)** view. The two flaky
tests assert the same literal bound against the `-a` view specifically, which is not a contract
the project has actually codified anywhere. The unit test's own docstring
(`test_structure.py:640-645`) already says as much in different words: it calls the residual "a
residual left for the end-to-end width gate to catch," i.e. the test authors knew the `-a` header
could exceed 80 and deferred the problem to a second test that makes the identical, equally
unenforceable assertion.

This means the fix is not merely "tolerate a slightly wider header" — it is bringing the test's
claim back in line with what the codebase actually promises, which none of the printer, semantics,
or CODE_STANDARDS.md text need to change to achieve.

### Confirmed by direct measurement (this research pass)

- Default (non-`-a`) view, the `TestEndToEndWidthGate` five-case representative run: **0** lines
  over 80 columns (measured directly; matches `test_default_view_stays_within_80_columns`'s own
  assertion and the dispatch's claim).
- `-a` view for the named case: **1** line over 80 columns — the `Histories:` legend line itself
  (117 columns: `"Histories:  (rows are representative positions; back repeats leftward, fwd
  rightward; [ ] marks the evaluation point)"`, printed by `model.py:657-661`, part of bimodal's
  own `print_certificate`, not the shared framework's recursive sentence printer). Both of the
  two flaky tests already explicitly exclude this line from their own assertions (the unit test
  filters `not line.startswith("Histories:")`; the integration test singles out the line
  containing `"slot"` instead of scanning every line).

## `code/CHANGELOG.md`'s `## [1.4.1]` wording is wrong on measurement

Two places in the published `## [1.4.1]` entry are inaccurate against the measurements above:

1. The "Changed" bullet (`code/CHANGELOG.md:20-23`): "Over-80-column lines in the default bimodal
   view dropped from 35 to 2." Measured default-view count today is **0**, not 2.
2. The "Known limitation" paragraph (`code/CHANGELOG.md:87-91`): "Two printed lines still exceed
   80 columns, both originating in `models/structure.py`'s framework-shared recursive sentence
   printer... Bringing those within budget requires an independent rework of that printer." This
   is wrong on both count and attribution: measured is **1** over-80 line in the `-a` view only
   (the default view has zero), and it originates in bimodal's own `print_certificate`
   (`model.py:657-661`), not in `models/structure.py`'s shared recursive sentence printer.

The dispatch names two remedies: bring the legend within budget, or correct the changelog wording.
**Bringing the legend within budget would be a printer-text change**, which conflicts with this
task's own "SCOPE - TESTS ONLY" instruction ("No printer behavior ... may change"). The
tests-only-scoped remedy is therefore to **correct the CHANGELOG wording**, not touch the legend
string. This is a documentation fix, not a test fix, so it does not consume any of this task's
test-file `file_scope` but should be included in the same implementation round since it was
"found while diagnosing" per the dispatch's "ALSO IN SCOPE" section.

Separately noted (no action possible/needed this round): the dispatch states the v1.4.1 git tag
annotation carries the same wrong text and can't be edited without delete-and-re-push (a
destructive, user-only operation — out of scope for an agent under `pr-prohibition.md` and the
destructive-git rules regardless); the GitHub Release body, by contrast, can be edited in place
and could carry the corrected wording if the user chooses — that is a user decision, not
something to action from this dispatch.

## Candidate approaches for the two flaky tests (tests-only)

The dispatch names three to weigh:

### Option A — Derive the expected bound from the roles the draw actually returned

Call `structure._lasso_roles(output=...)` in the test (both tests already have access to the
structure, or can get it), and compute an expected header width mechanically from the same
inputs `_print_history_table` uses to build it (time/slot column widths, name width `L{i}`, and
each role string's length — the production code at `model.py:555-558` for the exact formula),
then assert the measured line's length is `<=` that computed value instead of a literal `80`.

**Draw-independence**: trivially demonstrable per the acceptance criterion — monkeypatch
`BimodalStructure._lasso_roles` (`monkeypatch.setattr` or a small subclass) to return a roles dict
with an extra `"reserved, unused"` entry, re-render, and show the *derived* bound (not a literal)
still holds because it recomputes from the same (now-different) roles dict. This directly
satisfies "exercise a draw that assigns an extra `reserved, unused` role and show the assertion
still holds."

**Trade-off**: the test effectively re-implements (a simplified version of) the production width
formula, so it is testing "the printer is internally self-consistent" rather than "the printer
respects an externally meaningful budget" — a legitimate thing to assert, but it is no longer
bounding anything a user would recognize as "80 columns," so the test's own docstring/name should
stop claiming an 80-column bound for the `-a` view (which, per the Key Finding above, was never a
codified contract anyway).

### Option B — Pin the draw for these two cases

Force a specific Z3 outcome (e.g. a `smt.random_seed`/`sat.random_seed` pin, or a monkeypatch of
whichever extraction function picks the witnessing lasso) so the same 4-role, 72-column draw is
produced deterministically.

**Trade-off**: this is the fragile option. No seed-pinning mechanism exists anywhere in this
codebase today (see Root Cause above), there is no guarantee a Z3-version-pinned seed reproduces
the identical model across the `z3-solver>=4.8.0` range this project accepts (CI already showed
the *same* code non-deterministically failing on both 3.10 and 3.12 across two runs — i.e. the
nondeterminism is intrinsic to the solve, not merely a Python-version artifact), and it does not
by itself satisfy the "demonstrably draw-independent" acceptance criterion — a pinned draw proves
exactly one draw passes, not that the assertion is robust to others, unless combined with Option
A's monkeyed-second-draw technique anyway. Not recommended as the primary fix; could be layered
on top of Option A for the main assertion's one deterministic regression case, but adds
cross-version fragility for no incremental coverage Option A doesn't already give for free.

### Option C — Assert a role-vocabulary-independent property in place of the literal 80

Replace the width assertion with something that holds regardless of which three-value role each
lasso draws — e.g. assert the role values are confined to the bounded
`{"main", "witness", "reserved, unused"}` vocabulary (already covered independently by
`test_role_values_are_drawn_from_the_bounded_vocabulary`, `test_structure.py:657-662`) and that
columns stay internally aligned (header length equals every body row's length — already implied
by the shared `widths` list `_print_history_table` computes), rather than asserting any absolute
column count.

**Trade-off**: this is the cleanest match to the Key Finding (there is no codified `-a`-view
budget to defend), but it drops column-count coverage of the `-a` view entirely, leaving only the
default view's budget enforced (by `TestEndToEndWidthGate`'s existing first test and
`test_default_view_stays_within_80_columns`). If the project wants *some* sanity bound on how wide
the `-a` header can plausibly get (so a true printer regression — e.g. a role string tripling in
length — still gets caught), Option C alone offers none; it would need to be paired with Option
A's derived-bound check to retain any width-based regression coverage at all.

### Recommendation

**Option A**, as the primary fix for both failing assertions, with the test/docstring language
changed to stop claiming an "80 columns" contract for the `-a` view (per the Key Finding, replaced
with language describing the derived, role-aware budget). Option C's vocabulary-boundedness
assertion is already present as a separate, passing test and needs no duplication. Option B is not
recommended as a replacement mechanism given the version-range fragility and the lack of any
existing seed-pinning precedent in this codebase; it could optionally supplement Option A later
(e.g. pinning one illustrative draw for a human-readable golden case) but is not necessary to meet
this task's acceptance criteria.

## Reproducing the failing condition first (TDD red step)

Both currently-passing local runs land on the 72-column (within-budget) draw, so the literal
`<= 80` assertion does not fail locally today — matching the dispatch's note that the tests "pass
locally across six `PYTHONHASHSEED` values." To reproduce the *failing condition* deterministically
for the mandatory TDD red step without depending on an unlucky Z3 draw, monkeypatch
`BimodalStructure._lasso_roles` to return a roles dict with two `"reserved, unused"` entries (the
dispatch's own "two substitutions yield 90" case) before asserting the **old** literal-80 logic,
showing it fails at 90 > 80; then implement Option A's derived-bound assertion and show the same
monkeypatched roles dict now passes because the bound is recomputed from the (same) roles dict
rather than fixed at 80. This gives a real RED (old assertion fails against the forced draw) → GREEN
(new assertion passes against the same forced draw) cycle without any reliance on which way Z3
happens to resolve the live solve, and doubles as the "exercise a draw with an extra reserved role"
acceptance check.

## Files relevant to implementation

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — lines 608-684
  (`TestRoleColumnIsBounded` class, including the two tests this phase does not need to touch:
  `test_default_view_stays_within_80_columns`, `test_role_values_are_drawn_from_the_bounded_vocabulary`,
  `test_witness_role_provenance_is_recoverable_from_box_guesses`,
  `test_aligned_header_role_values_are_bounded_too` — only
  `test_aligned_view_header_and_rows_stay_within_80_columns` at line 655 needs its assertion
  changed).
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` — lines
  200-245 (`TestEndToEndWidthGate` class; only
  `test_aligned_view_header_stays_within_80_columns_for_the_named_case` at line 245 needs its
  assertion changed — `test_default_view_stays_within_80_columns_across_representative_examples`
  at line 221 is unaffected, since it only covers the default view).
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` — read-only reference for the
  exact width formula to mirror in the test (`_lasso_roles`: 502-521; `_print_history_table`:
  533-574, especially the `widths`/`headers` computation at 545-558). **Not to be edited** —
  SCOPE is tests only.
- `code/CHANGELOG.md` — lines 20-23 (Changed bullet's "35 to 2" claim) and 87-91 (Known limitation
  paragraph) both need wording corrected to match the measured 0-in-default / 1-in-`-a` counts and
  the correct attribution (bimodal's own `Histories:` legend, not `models/structure.py`).

## Acceptance-criteria mapping

- "Tests workflow passes on 3.10/3.11/3.12 across repeated runs" — satisfied once both assertions
  no longer depend on which specific role draw Z3 returns (Option A removes the dependency
  entirely rather than narrowing its failure window).
- "Demonstrably draw-independent... exercise a draw that assigns an extra reserved, unused role"
  — satisfied by the monkeypatch technique described above, exercised against both the old (red)
  and new (green) assertion logic.
- "Per TDD, the failing condition is reproduced first" — satisfied by writing the monkeypatch-forced
  failing case before changing the assertion.
- "No change to printer output in the default view, and no change to any truth value" — satisfied;
  every candidate fix is confined to the two test files plus the CHANGELOG wording correction;
  `model.py` is read-only reference material only.
