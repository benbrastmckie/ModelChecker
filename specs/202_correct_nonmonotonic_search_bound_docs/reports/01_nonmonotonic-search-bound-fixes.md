# Research Report: Correct Nonmonotonic Search Bound Docs

- **Task**: 202 - correct_nonmonotonic_search_bound_docs
- **Started**: 2026-09-27T00:54:00Z
- **Completed**: 2026-09-27T01:30:00Z
- **Effort**: ~35 minutes agent time
- **Dependencies**: 201 (complete — D6 sole-writer comment and A2_GAP.md section 6; disjoint from
  this task's D4/SETTINGS.md/ADEQUACY.md scope)
- **Sources/Inputs**:
  - Local code: `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`,
    `semantic/core.py`, `tests/integration/test_certificate_a2_triangle.py`
  - Local docs: `docs/SETTINGS.md`, `docs/USER_GUIDE.md`, `docs/API_REFERENCE.md`,
    `docs/ADEQUACY.md`, `README.md`, `docs/ARCHITECTURE.md`
  - Prior artifact: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`
    (already measured and documented this exact defect — findings 8/9/11, Stage 2a)
  - Experiment run for this report: direct reproduction against the live search (see Findings)
- **Artifacts**: `specs/202_correct_nonmonotonic_search_bound_docs/reports/01_nonmonotonic-search-bound-fixes.md`
- **Standards**: report-format.md, subagent-return.md
- **Task Type**: general

## Executive Summary

- **The mechanism is verified, not merely inspected.** `WitnessRegistry.wrap()`
  (`semantic/witness_registry.py:125-132`) folds `back`-segment positions by `t % nb` and
  `fwd`-segment positions by `nb + nm + ((t - nm) % nf)`: both are **exact**-period foldings, not
  ceilings. A back-period-`nb'` (or fwd-period-`nf'`) family is representable at configured length
  `nb` (resp. `nf`) **iff `nb' | nb`** (resp. `nf' | nf`). `mid` is exempt from this: positions
  `0 <= t < mid` are read directly with no modulo, so `mid` "pads freely" and raising it cannot
  discard a previously-representable family. The non-monotonicity is specifically a `back`/`fwd`
  property, not a `back`/`mid`/`fwd` property uniformly — corrected docs should say so precisely,
  not overcorrect onto `mid`.
- **Independently reproduced against the live search, this session** (not just cited from prior
  work): the `alt3` formula from task 195's report is SAT at `(3,1,3)` and `(6,1,6)` but UNSAT at
  `(4,1,4)` and `(5,1,5)`, `timeout=False` at every point, runtimes 0.09-0.20s. This matches the
  divisibility prediction and task 195's own measured numbers (which reported 0.002-0.006s under a
  tighter harness; the difference is import/setup overhead in my ad hoc script, not a different
  result). See Findings section 2 for the exact reproduction.
- **Six files carry the false claim, not the three named in the dispatch.** The dispatch names
  `SETTINGS.md`, `core.py`'s D4 commentary, and `ADEQUACY.md` section 7.1(iii)/A3. The sweep below
  additionally finds the identical "maximum length" / "raise for more search" framing duplicated in
  `README.md`, `USER_GUIDE.md`, and `API_REFERENCE.md` — all of which either quote or paraphrase
  the same `DEFAULT_EXAMPLE_SETTINGS` comment or the same "raise segment lengths" advice.
  `ARCHITECTURE.md` was checked and is clean (it describes the periodic mechanism accurately and
  makes no "raising enlarges" claim).
- **`ADEQUACY.md`'s false claim is not confined to section 7.1(iii) and the A3 table row** — the
  top-level `(ADEQ)` statement itself (section 7, the direction's formal statement) embeds the same
  `back, mid, fwd >= f(|C|)` condition that A3 names, so a correct fix touches the lede, not just
  the two locations the dispatch names. All three are one claim restated three times.
- **This task's scope is exactly task 195 report's "Stage 2a" doc-only recommendation** (that
  report's own Decisions section already flagged this as the deliverable and Stage 2a as the
  work): fix the wording, do not change search semantics, and do not attempt the sweep/regression
  test (that is implementation-scoped, out of this task's "documentation and comments only"
  boundary per the task description).

## Context & Scope

Verify the claimed non-monotonicity mechanism, independently reproduce the reported SAT/UNSAT
pattern, and locate every documentation/comment site in the bimodal theory that promises
monotonic or "maximum length" search-bound behavior for `back`/`mid`/`fwd`. Task 201 (sibling,
already complete) owns `core.py`'s D6 sole-writer comment and `A2_GAP.md` — both are out of scope
here and were left untouched. Changing the search's actual semantics (e.g. adding a length sweep)
is explicitly out of scope; this is a documentation-correction task only.

## Findings

### 1. The mechanism, verified against the actual code

`semantic/witness_registry.py:125-132`:

```python
def wrap(self, t: int) -> int:
    if t < 0:
        return t % self.nb
    if t < self.nm:
        return self.nb + t
    return self.nb + self.nm + ((t - self.nm) % self.nf)
```

- `t < 0` (back segment): `t % self.nb` — Python's `%` on a negative dividend with a positive
  divisor returns a value in `[0, nb)`, i.e. exact period `nb`. A back-period-`nb'` pattern is
  losslessly foldable into `nb` slots iff every position congruent mod `nb'` gets a consistent
  value under mod `nb`, which holds iff `nb' | nb` (a sequence with fundamental period `nb'` also
  has period `nb` iff `nb'` divides `nb` — standard periodicity fact, and exactly what
  `witness_registry.py`'s own module docstring states at "Witness lassos and sharing" one section
  up, describing the identical fold for the `fwd` side).
- `0 <= t < mid` (mid segment): `self.nb + t` — a bijection onto `[nb, nb+mid)`, no modulo, no
  folding. Raising `mid` only ever adds fresh, unshared slots; it cannot make anything that was
  representable at a smaller `mid` stop being representable. This is the `mid` "pads freely"
  characterization already recorded in task 195's report finding 8, and it means the corrected
  docs must distinguish `back`/`fwd` (periodic, non-monotone) from `mid` (direct-read, monotone),
  not lump all three together as equally broken.
- `t >= mid` (fwd segment): `nb + nm + ((t - nm) % nf)` — exact period `nf`, same divisibility
  argument as `back`.

### 2. Independent reproduction against the live search (this session)

Built through the real `Syntax -> ModelConstraints -> BimodalStructure` pipeline (the same
construction `tests/integration/test_certificate_a2_triangle.py`'s `_build` helper uses), using
the `alt3` formula recorded in task 195's report Appendix A.1 (pattern `A, ¬A, ¬A, A, ¬A, ¬A` at
positions `-1` through `-6`, empty conclusions):

```
(back=3,mid=1,fwd=3): status=True  timeout=False runtime=0.0910s
(back=4,mid=1,fwd=4): status=False timeout=False runtime=0.1049s
(back=5,mid=1,fwd=5): status=False timeout=False runtime=0.1325s
(back=6,mid=1,fwd=6): status=True  timeout=False runtime=0.2018s
```

`status=True` is `z3_model_status` (SAT, a certificate found); `status=False` with
`timeout=False` is genuine UNSAT, not a solver timeout — `models/structure.py` only reports
`timeout=True` on solver UNKNOWN, so `False`/`False` is a real "no certificate," matching D8's
never-report-validity contract. This exactly reproduces the dispatch's and task 195's claimed
pattern: SAT at `(3,1,3)` and `(6,1,6)`, UNSAT at `(4,1,4)` and `(5,1,5)`. (My runtimes are
~0.1-0.2s rather than task 195's reported 0.002-0.006s; that is Python import/module-construction
overhead in my one-off script, not a different result — every run here is well under a second and
`timeout=False`, so "genuinely UNSAT" is not in question.)

The slot-sharing mechanism behind this: at `nb=4`, the pattern's period-6 back requirement (`A` at
`-1`, `-4`; `¬A` at `-2`,`-3`,`-5`,`-6`) cannot be folded consistently into 4 slots because
`6 ∤ 4`; at `nb=3` and `nb=6`, `3 | 6` in both directions (`gcd` relationships hold), so a
period-6 pattern folds consistently into either. This is the general mechanism, not a coincidence
of this one formula.

### 3. Every location promising monotonic or "maximum length" behavior

Full sweep of `code/src/model_checker/theory_lib/bimodal/` (`.py` and `.md`) for "maximum
length"/"maximum segment"/"enlarge"/"raise ... larger" framing around `back`/`mid`/`fwd`.
`ARCHITECTURE.md`, `TRUST_PIPELINE.md`, `ITERATE.md`, and `examples.py`'s per-example comments were
checked and are clean (they describe the periodic mechanism neutrally, or make claims about
specific already-measured examples, not a general monotonicity claim).

**`docs/SETTINGS.md`** (the dispatch's named target):
- Lines 20-29: each of `back`/`mid`/`fwd` is documented as "**maximum length** of a lasso's `X`
  segment." True for `mid` (direct read, no ceiling violated by raising it), false for `back`/
  `fwd` (exact period, not a ceiling).
- Lines 31-34: "`back + mid + fwd` is ... raising any of the three enlarges the search, not the
  reported model's size" — the specific sentence the dispatch quotes. False for `back`/`fwd`.
- Lines 129-134 ("Tips and Best Practices" #1-2): "Start with the defaults ... every one of the
  theory's 53 examples ... decides correctly" (fine, factual) and "**Raise segment lengths, not a
  world/time count, if a formula needs a longer period**: a formula whose refutation genuinely
  needs a longer periodic pattern will need larger `back`/`mid`/`fwd`" — same false advice in
  imperative form: "larger" is not sufficient, only a "larger and divisible by the family's
  period" value is.
- Lines 81-90 ("Formula needing a longer periodic segment" usage example, `2,1,2 -> 3,2,3`): not
  itself an assertion, but reinforces the "raise = more search" framing with no caveat; worth a
  one-line footnote pointing at the corrected explanation above it, not a rewrite.

**`code/src/model_checker/theory_lib/bimodal/semantic/core.py`** (the dispatch's named D4 scope
only — D6, lines 164-170, is task 201's and is untouched):
- Lines 35-39 (D4 docstring): "`back`/`mid`/`fwd` (the **maximum segment lengths** of
  `LabelledLasso` ...) replace `N`/`M`." Same "maximum" error `witness_registry.py`'s own module
  docstring avoids (it correctly says "fixed segment lengths," quoted in its "Position slots and
  `wrap`" section).
- Lines 108-113 (the `DEFAULT_EXAMPLE_SETTINGS` dict's inline comment, immediately governed by the
  D4 docstring above it): "`# Maximum back/mid/fwd segment lengths for the searched LabelledLasso
  family ... Small defaults, raised on demand.`" Same error, plus "raised on demand" repeats the
  "raise = safe" framing.

**`README.md`** (not named by the dispatch; duplicates `core.py`'s settings comment verbatim):
- Lines 166-169: identical `DEFAULT_EXAMPLE_SETTINGS` comment block, same text as `core.py`
  lines 108-113 above.
- Lines 187-188: "`back`, `mid`, and `fwd` replace `N`/`M`: they bound the **maximum size** of the
  searched lasso family rather than the size of a fixed finite frame." Same error.

**`docs/USER_GUIDE.md`** (not named by the dispatch):
- Line 70: "`back`/`mid`/`fwd`: the **maximum lengths** of the searched lasso family's three
  segments." Same error.
- Lines 156-162 (`settings = {...}` example): inline comments "`# Maximum back-segment length`" /
  "`# Maximum mid-segment length`" / "`# Maximum fwd-segment length`." Same error (repeated per
  field).
- Lines 165-170 ("Bimodal-Specific Considerations"): "**`back`/`mid`/`fwd`**: **raise these** if a
  formula's refutation genuinely needs a longer periodic pattern." Same false imperative as
  `SETTINGS.md`'s Tips #2.

**`docs/API_REFERENCE.md`** (not named by the dispatch):
- Line 80: "`back`, `mid`, `fwd` (int): **maximum** lasso segment lengths." Same error.
- Line 481 (Debugging Tips #3): "**Raise segment lengths**: some formulas need **larger**
  `back`/`mid`/`fwd`, not a larger `N`/`M`." Same false imperative.

**`docs/ADEQUACY.md`** (the dispatch's named target, but the false claim appears in three
coordinated spots, not two):
- Section 7, the `(ADEQ)` direction's formal statement itself (lines 519-522): "the search, run at
  segment-length settings `back, mid, fwd >= f(|C|)`, returns SAT and emits a certificate..." This
  is the lede the A3 row and 7.1(iii) both restate; fixing A3/7.1(iii) without also touching this
  sentence leaves the headline statement still asserting the false condition.
- The A3 row (line 532): "Bound realization: configured lengths `>= f(|C|)`" — the dispatch's
  named A3 wording. `>=` alone is not sufficient once `f` is known; sufficiency needs the
  configured `back`/`fwd` to be common multiples of (or otherwise compatible with) every candidate
  period up to `f(|C|)`, not merely at-least-as-large.
- Section 7.1, condition (iii) (lines 590-592): "(iii) a demonstration that this repository's
  search enumerates the same family space at a segment length **at least** that bound" — the
  dispatch's named condition (iii). Task 195's report already identifies this exact sentence as
  false as worded and names two honest replacements: "a common multiple of every candidate length
  up to `f(|C|)`" (impractical, `lcm(1..f)` is `e^{O(f)}`), or "sweep `(back, mid, fwd)` over the
  grid `<= f(|C|)`" (cheap, `f^3` solver calls). Either is a documentation-scope rewording; neither
  requires implementing the sweep as part of this task.

## Decisions

- **Scope confirmed as documentation/comments only**, matching the task description's explicit
  exclusion of search-semantics changes. No code in `witness_registry.py`, `core.py`'s constraint
  generation, or elsewhere should change behavior.
- **Fix six files, not three**: `SETTINGS.md`, `core.py` (D4 only), `ADEQUACY.md` (three
  coordinated spots: the `(ADEQ)` lede, the A3 row, and 7.1 condition (iii)), plus `README.md`,
  `USER_GUIDE.md`, and `API_REFERENCE.md`, which duplicate or paraphrase the same claim and were
  not named in the dispatch but carry the identical defect.
- **Preserve the `back`/`fwd` vs. `mid` distinction in the corrected wording.** `mid` genuinely
  pads freely (direct read, no modulo) and should not be described as non-monotone; only `back` and
  `fwd` are period-locked. Corrected text should say "raising `back` or `fwd` to a value not a
  multiple of the family's period" rather than blanket "raising any of the three."
- **State the operative user rule plainly wherever the false claim is corrected**: prefer a
  `back`/`fwd` value that is a multiple of the period(s) of interest (or sweep several candidate
  lengths) rather than assuming any larger value is at least as good as a smaller one.
- **Do not implement task 195's Stage 2a "add the reproducing test as a standing regression" or
  the sweep option** — both are implementation work, outside this documentation-only task. Leave
  them as a forward pointer (see Risks & Mitigations).

## Risks & Mitigations

- **Risk**: correcting only the three dispatch-named locations leaves README.md/USER_GUIDE.md/
  API_REFERENCE.md stating the old, false claim, so a user reading a different doc page still gets
  misled. **Mitigation**: this report's Findings section 3 gives the plan phase every location
  found in the sweep, not just the three named ones, so the fix can be complete in one round.
- **Risk**: overcorrecting to claim all of `back`/`mid`/`fwd` are non-monotone (rather than just
  `back`/`fwd`) introduces a new, different false claim about `mid`. **Mitigation**: the corrected
  wording template in Findings section 1 explicitly carves out `mid`'s direct-read behavior.
- **Risk**: fixing `ADEQUACY.md`'s A3 row without also fixing the `(ADEQ)` lede (section 7) leaves
  the document's own headline statement self-inconsistent with its corrected footnote.
  **Mitigation**: Findings section 3 flags all three `ADEQUACY.md` spots as one coordinated fix.
- **Risk**: a future reader interprets this doc fix as a signal that the search semantics changed.
  **Mitigation**: task 195's report already names this risk and its mitigation (documentation-
  first, corrected wording should make clear this describes pre-existing search behavior being
  documented accurately for the first time, not a change).

## Context Extension Recommendations

- **Topic**: Periodicity and divisibility of the searched certificate space.
  **Gap**: No context file under `.claude/context/project/math/` records that `back`/`fwd` are
  exact periods, that representability across lengths is a divisibility condition, or that `mid`
  is exempt. Confirmed still absent this session (`.claude/context/project/math/` has no
  period/divisibility file, and `index.json`'s `math` subdomain topics do not mention either
  term) — this is the same gap task 195's report already flagged in its own Context Extension
  Recommendations, still open.
  **Recommendation**: add a short domain note under `context/project/math/` (order/periodic
  structure) cross-referenced from the bimodal theory docs, cited from `ADEQUACY.md` section
  7.1/A3. Not created here (research is read-only for context files); flagging for the plan phase
  or a follow-up task.

## Appendix

### Search queries and commands used

- `grep -rn "maximum length\|maximum segment\|max segment\|enlarge\|raising" code/src/model_checker/theory_lib/bimodal/ --include="*.py" --include="*.md"`
- `grep -rn "monoton\|nonmonoton" code/src/model_checker/theory_lib/bimodal/`
- Direct reproduction script built on `test_certificate_a2_triangle.py`'s `_build` helper pattern
  (`Syntax -> ModelConstraints(settings, syntax, BimodalSemantics(settings), BimodalProposition) ->
  BimodalStructure`), run at `PYTHONPATH=code/src` against the `alt3` formula from task 195's
  report Appendix A.1, at `(back,mid,fwd) = (3,1,3), (4,1,4), (5,1,5), (6,1,6)`, `max_time=20`.

### References

- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py:1-59` (module
  docstring, "Position slots and `wrap`" and "Witness lassos and sharing" sections), `:125-132`
  (`wrap`).
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py:35-39` (D4 docstring), `:108-113`
  (`DEFAULT_EXAMPLE_SETTINGS` comment).
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md:20-34,81-90,129-134`.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md:519-522` (`(ADEQ)` lede), `:530-532`
  (A1/A3 table rows), `:585-592` (7.1 conditions (i)-(iii)).
- `code/src/model_checker/theory_lib/bimodal/README.md:166-169,187-188`.
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md:68-74,155-170`.
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md:80,477-482`.
- `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md` findings
  8, 9, 11 and Stage 2a (the prior measurement and recommendation this task implements the
  documentation half of).
