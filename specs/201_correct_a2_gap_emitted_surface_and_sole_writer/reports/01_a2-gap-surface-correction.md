# Research Report: Task #201

**Task**: 201 - Correct A2_GAP.md's emitted-constraint surface and semantic/core.py's sole-writer claim
**Started**: 2026-09-26T22:08:00Z
**Completed**: 2026-09-26T22:20:00Z
**Effort**: Small (documentation/comments only, no behavioral change)
**Dependencies**: None
**Sources/Inputs**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
**Artifacts**: This report (`reports/01_a2-gap-surface-correction.md`)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Verified directly against the current tree (not against any prior report): `iterate.py:266` and
  `iterate.py:280` both execute `semantics.frame_constraints.append(pinned)`, inside
  `_pin_theory_specific_values` (line 190). This is a real, currently-existing eighth path that
  appends to `frame_constraints` outside `finalize_certificate`.
- Verified: `semantic/core.py:164`'s comment reads "D6: frame_constraints starts empty.
  finalize_certificate() is the sole writer, mutating this list in place..." — this is directly
  contradicted by the `iterate.py` appends above, which run later, during model-iteration rebuilds,
  and are not part of `finalize_certificate` itself.
- Verified: `A2_GAP.md` section 4 enumerates exactly seven call sites, (1) through (7), all
  reachable from `ModelConstraints.__init__` through `_setup_solver`'s ordinary single-solve path.
  None of the seven is the iteration-rebuild pinning path in `iterate.py`, so the section's own
  "Net correction" paragraph ("the encoder's actual attack surface is seven call sites") is
  incomplete once model iteration is in scope.
- Verified: `WitnessRegistry.target_window()` (`witness_registry.py:171-183`) delegates directly to
  `certificate._box_window` (`certificate.py:219-221`), and `witness_constraints.py`'s
  `box_faithfulness_constraints` (the encoder side) also imports and calls `_box_window` directly
  (`witness_constraints.py:238`) — the same function `certificate.recheck` (the re-checker, leg
  (i) of the A2-triangle test) uses for box faithfulness. Since `test_certificate_a2_triangle.py`
  compares leg (i) (`certificate.recheck`) against leg (iii) (the real Z3 encoding, which uses
  `target_window()`/`_box_window` for both the selector and box faithfulness), a defect confined
  to `_box_window`'s own formula would now produce **identical** (wrong) values on both legs,
  hence agreement rather than disagreement — invisible to that specific differential by
  construction. `A2_GAP.md` section 6 currently frames the sharing only as removing a drift
  hazard; it does not name this cost.
- Recommended corrections (both documentation/comment-only, no behavioral change) are given below
  with exact insertion points.

## Context & Scope

This task corrects documentation written earlier the same day (`A2_GAP.md`, `semantic/core.py`'s
D6 comment) against the actual, current state of the tree — per the dispatch's own instruction,
every claim below was checked directly at the named file:line rather than trusted from a prior
report. A sibling task (recorded separately, not this one) handles monotonicity claims elsewhere
in `core.py`; this report confines itself to the sole-writer comment at line 164 only.

Three corrections are in scope:

1. Add the `iterate.py` `_pin_theory_specific_values` path to `A2_GAP.md` section 4's
   emission-call-site enumeration, with its clause shape.
2. Fix or properly qualify `semantic/core.py:164`'s "sole writer" comment.
3. Add to `A2_GAP.md` (most naturally section 6, which already discusses the window-sharing
   closure) an explicit statement of the independence cost the sharing introduced for the
   A2-triangle differential.

## Findings

### Codebase Patterns

**Finding 1 — the eighth emission call site (confirmed).**

`iterate.py:190`, `_pin_theory_specific_values(self, temp_solver, z3_model, model_constraints)`,
called from the shared iteration engine's `build_new_model_structure` hook when constructing model
2+ during `iterate_generator`. Sequence:

- Line 231: `semantics.finalize_certificate()` — idempotent, allocates every witness lasso/bit
  needed (the method's own docstring explains this is necessary so every variable that needs
  pinning already exists).
- Lines 232-266: for every `_bits`/`_guesses` variable, evaluates it against the previous model
  (`z3_model`), builds `pinned = var if is_true(value) else z3.Not(var)`, and — per the extensive
  comment at `iterate.py:238-265` — appends it to **both** `temp_solver` (line 235, kept for
  `TestPinTheorySpecificValues`'s existing interface) **and** `semantics.frame_constraints`
  (line 266), because the shared engine's `all_constraints` path (which `temp_solver`'s additions
  would otherwise reach) is never read by `_setup_solver`.
- Lines 268-280: the same pattern for the one-hot target selector `sel(t)` over
  `registry.target_window()` — `temp_solver.add(pinned)` (line 279) and
  `semantics.frame_constraints.append(pinned)` (line 280).

Clause shape for `A2_GAP.md`'s enumeration: a single unit literal per pinned variable — `var` or
`Not(var)` — one per `_bits` entry, one per `_guesses` entry, and one per `sel(t)` for
`t in registry.target_window()`, all against the *previous* iteration's model, not derived from
(C1)-(C4) at all. Unlike call sites (1)-(7), this path runs **after** the ordinary single-solve
path (`finalize_certificate` already having run once), on a **freshly-constructed** semantics
instance, and only when the model iterator requests a next, distinct model — never on the first
solve.

**Finding 2 — the sole-writer comment is false as stated (confirmed).**

`semantic/core.py:164`:

```python
# D6: frame_constraints starts empty. finalize_certificate() is the sole writer,
# mutating this list in place (never reassigning it) so ModelConstraints's
# by-reference copy (models/constraints.py:80) observes the mutation.
```

`finalize_certificate` itself (the method spanning `core.py:279-332`) is indeed the only writer
*within `semantic/core.py`* — its four `self.frame_constraints.extend(...)` calls (lines 321, 324,
328, 332) are exactly and only what it does. But Finding 1 shows a second, external writer:
`iterate.py`'s `_pin_theory_specific_values` calls `.append(...)` directly on the same list object
(via `semantics.frame_constraints`, the identical attribute), from outside `semantic/core.py`
entirely, during iteration. The comment's literal claim ("the sole writer") is therefore false;
what remains true and worth keeping is the **narrower, still-useful** fact the comment was
actually protecting: within the single-solve path, and within `semantic/core.py` itself,
`finalize_certificate` is the only writer, and it mutates in place rather than reassigning (which
is what makes the by-reference alias in `models/constraints.py:80` valid at all).

**Finding 3 — the window-sharing independence cost (confirmed).**

- `witness_registry.py:171-183`, `WitnessRegistry.target_window()`, returns `_box_window(self)`
  directly (line 183), imported at `witness_registry.py:69` from `.certificate`.
- `certificate.py:219-221`, `_box_window(lasso)`, returns `range(-lasso.nb, lasso.nm + lasso.nf)` —
  the single definition both sides now share.
- `witness_constraints.py:238`, `box_faithfulness_constraints`, also calls `_box_window(registry)`
  directly (imported at `witness_constraints.py:73`) for the encoder's own (C3) clause emission.
- `test_certificate_a2_triangle.py`'s own module docstring names the exact comparison: leg (i) is
  `certificate.recheck` (the pure-Python re-checker, which decides (C3) over `_box_window` and
  (C4) over the same window via `target_window()`/`_box_window`'s shared definition), leg (iii) is
  the real Z3 encoding (built via `witness_constraints.py`, which also calls `_box_window`
  directly, and via `target_window()`, which now also resolves to `_box_window`). Both legs the
  test compares therefore evaluate `_box_window` by calling the *same Python function* — not two
  independently written formulas that happen to agree.

Consequence: if `_box_window`'s formula itself were wrong (e.g. an off-by-one in
`range(-lasso.nb, lasso.nm + lasso.nf)`), both leg (i) and leg (iii) would use the identical wrong
window and therefore still **agree** with each other — the differential compares two legs for
disagreement, and a defect common to both inputs produces no disagreement. This is precisely the
class of blind spot `A2_GAP.md` section 7 already documents for a *different*, historical defect
(narrow-vs-wide window confusion caught by a differential); this is a new, structurally different
blind spot the sharing itself introduces, and it is currently undocumented.

`A2_GAP.md` section 6 ("The one remaining independently-defined window") already gives a long,
careful account of the sharing's benefits ("removes the specific latent-drift risk", "the closure
is checked, not merely asserted in prose") and is honest that sharing is "strictly weaker than
proving the shared value correct." What it does not say anywhere is the specific, opposite-facing
point: sharing the definition makes the two *legs of the empirical A2-triangle differential test*
no longer independent samples of "is this window right" for `_box_window`'s value itself — only
for everything built *from* that shared value differently on each side (clause shapes, assembly
order, etc., which section 3(iii) already scopes correctly). Section 3(ii) states the general
principle ("stronger than a proof of agreement, because there is no second definition") but frames
it entirely as a positive ("this is not merely proved absent — it is impossible by construction"),
without naming the corresponding cost to differential-test coverage that this task asks to record.

### External Resources

None consulted — this is a self-contained internal-documentation correction; no external
API/library research was needed.

### Recommendations

**Correction 1 — A2_GAP.md section 4, add an eighth call site.**

Insert after call site (7) (currently ending at line 178, before the "Assembly into what Z3
actually sees" paragraph at line 180), a new item:

> **(8) `IterativeModelSearch._pin_theory_specific_values` (`iterate.py:190`) — model-iteration
> pinning, outside the single-solve path.** Invoked once per requested next model, from the shared
> iteration engine's `build_new_model_structure` hook, on a freshly-constructed semantics instance,
> after that instance's own `finalize_certificate()` has already run once (called defensively at
> `iterate.py:231` to allocate every bit/guess/lasso before pinning). For every `_bits`/`_guesses`
> Z3 variable and every `sel(t)` for `t in registry.target_window()`, evaluates the variable
> against the previous model and appends the resulting unit literal (`var` or `Not(var)`) directly
> to `semantics.frame_constraints` (`iterate.py:266`, `:280`) — bypassing the shared engine's
> `all_constraints` path, which `models/structure.py`'s `_setup_solver` never reads. This path
> emits no (C1)-(C4) content of its own; it pins previously-derived values so a rebuilt structure
> reflects the model the search actually found, rather than an unconstrained re-solve.

Also update the section's "Net correction" paragraph (lines 193-197) and the section's opening
count ("seven emission call sites", line 120) to eight, and note that call site (8) is
iteration-only, never part of the initial single-solve `ModelConstraints.__init__` →
`_setup_solver` path the other seven describe — so "the encoder's actual attack surface" should be
qualified as "seven call sites reachable from a single solve, plus one more (model-iteration
pinning) reachable only when iterating."

**Correction 2 — semantic/core.py:164, narrow the sole-writer claim.**

Replace:

```python
# D6: frame_constraints starts empty. finalize_certificate() is the sole writer,
# mutating this list in place (never reassigning it) so ModelConstraints's
# by-reference copy (models/constraints.py:80) observes the mutation.
```

with a version scoped to what is actually true, e.g.:

```python
# D6: frame_constraints starts empty. Within a single solve, finalize_certificate() is
# the sole writer inside this class, mutating this list in place (never reassigning it)
# so ModelConstraints's by-reference copy (models/constraints.py:80) observes the
# mutation. A second writer exists outside this class: iterate.py's
# _pin_theory_specific_values appends unit-literal pins directly to this same list
# during model iteration (iterate.py:266, :280), after finalize_certificate has already
# run once on that instance -- see docs/A2_GAP.md section 4, call site (8).
```

**Correction 3 — A2_GAP.md section 6, name the independence cost.**

Add a new paragraph to section 6 (after the existing "What this closure is, and is not" paragraph,
lines 283-294), naming the trade explicitly rather than only the gain:

> **The cost this closure also introduced.** Sharing `_box_window` between `target_window()` and
> `certificate._box_window` removes the drift hazard above, but it also removes independence
> between the two legs `tests/integration/test_certificate_a2_triangle.py` compares for the
> box-faithfulness and target windows specifically: leg (i) (`certificate.recheck`) and leg (iii)
> (the real Z3 encoding, via `witness_constraints.py`'s direct `_box_window` import and via
> `target_window()`'s delegation) now both compute this window by calling the identical Python
> function. A defect confined to `_box_window`'s own formula — as opposed to a defect in how
> either side uses the window it returns — would therefore produce the same (wrong) value on both
> legs and could not surface as a leg (i)/leg (iii) disagreement; the differential test is
> powerless against exactly this class of defect for exactly this window, by construction. This is
> not a reason to prefer the earlier, independently-defined pair (section 6's "gap, as it stood"
> paragraph already gives the reasons that outcome was worse), but the sharing should be presented
> as a trade — drift-hazard elimination purchased at the cost of one differential's remaining
> independence — not as a pure gain.

## Decisions

- Scope confirmed as documentation/comments only; no source-code behavior changes are proposed or
  needed, consistent with the dispatch's constraint.
- The sibling task's territory (monotonicity claims elsewhere in `core.py`) is explicitly out of
  scope here; only the sole-writer comment at line 164 is addressed.
- All three corrections above are additive/qualifying edits to existing prose, not restructuring;
  they preserve every existing citation and cross-reference in `A2_GAP.md` and `core.py`.

## Risks & Mitigations

- **Risk**: renumbering call sites (7)→(8) in section 4 could break other documents' references to
  "seven call sites" or to a specific numbered call site. **Mitigation**: a grep across
  `docs/*.md` for "seven emission call sites" / "seven call sites" / cross-references to call site
  numbers is a cheap pre-check before the plan/implementation phase edits section 4; the
  correction as drafted only appends site (8) after (7), not renumbering earlier sites.
- **Risk**: the corrected `core.py:164` comment must not be over-corrected into vagueness that
  loses the by-reference-alias rationale the comment exists to protect (`models/constraints.py:80`
  reads `self.frame_constraints = self.semantics.frame_constraints`, which depends on in-place
  mutation, never reassignment). **Mitigation**: Correction 2's draft preserves that sentence
  verbatim and only adds the scoping/exception.

## Context Extension Recommendations

None — this is a self-contained fix to two existing, well-maintained documents; no gap in
`.claude/context/` was identified during this research.

## Appendix

**Grep/read trail** (exact commands, in order):
- `find . -iname "A2_GAP.md"` → `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md`
- `grep -n "frame_constraints.append" iterate.py` → confirmed lines 266, 280
- `grep -n "sole writer" semantic/core.py` → confirmed line 164
- `grep -n "^#" A2_GAP.md` → section map used to navigate directly to section 4 (line 114) and
  section 6 (line 253)
- `grep -rn "target_window\|_box_window" semantic/*.py` → traced the delegation chain
  (`witness_registry.py:183` → `certificate.py:219`; `witness_constraints.py:238` direct import)
- `find . -iname "test_certificate_a2_triangle.py"` and read its module docstring for the
  leg (i)/(ii)/(iii) definitions this report relies on
- `python3` read of `specs/state.json`'s `active_projects` array to confirm task 201's description
  text matches the dispatch verbatim
