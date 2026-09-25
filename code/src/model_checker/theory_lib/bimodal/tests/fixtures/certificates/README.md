# Certificate fixture corpus

A small, checker-independent corpus of witness-family certificates in the wire format
documented in `~/Projects/BimodalLogic/BimodalTools/README.md`'s "Certificate re-verification
protocol" and restated in `../../../docs/ADEQUACY.md` §6.1. Every fixture's expected verdict was
adjudicated against `lake exe check_certificate` (the decision procedure built directly on the
four `Decidable` instances the proof of (SOUND) cites) at the time this corpus was written; where
that binary is available, `tests/integration/test_certificate_lean_agreement.py` re-adjudicates
the whole corpus and records the commit it was checked against.

**Independence.** `tests/unit/test_certificate_fixtures.py`, which decodes and evaluates these
fixtures, imports nothing from `model_checker.theory_lib.bimodal`. Its decoder and evaluators are
a from-scratch, self-contained re-implementation of the three-segment decoding and the four
conditions (C1)–(C4), so that the fixture corpus tests the *specification*, not any particular
encoder or re-checker.

## Wire format, in brief

```json
{"target": {"premises": [<formula>, ...], "conclusions": [<formula>, ...], "time": 0},
 "bx":     [[<formula>, true], [<formula>, false], ...],
 "lassos": [{"back": [<label>, ...], "mid": [<label>, ...], "fwd": [<label>, ...]}, ...]}
```

`<label>` is a list of `<formula>`. `<formula>` tags: `atom` (`name`), `bot`, `imp` (`left`,
`right`), `box` (`child`), `untl` / `snce` (`event`, `guard`). `target.time` is required with no
default. `lassos[0]` is the main lasso. See `ADEQUACY.md` §6.1 for the full contract and its
rationale.

## Fixtures

| File | Expected verdict | What it demonstrates |
|---|---|---|
| `01_positive_box.json` | `countermodel` | A genuine certificate: `□p` holds, `q` does not, refuting `□p → q`. |
| `02_infinite_postponement.json` | `rejected` / `fulfilling` | Locally coherent (the until fixpoint law is satisfied everywhere) but never fulfilled: `p U q` is carried forward forever with `q` never delivered. This is the canonical "coherence alone admits infinite postponement" example `ADEQUACY.md`'s Lemma 4 remark names. |
| `03_box_unfaithful.json` | `rejected` / `box_faithful` | `bx` guesses `□p` false, but `p` holds at every position of every lasso, so the global-membership side of (C3) disagrees with the guess. |
| `04_window_discriminator_coherence.json` | `rejected` / `local_coherent`, position `-2` | **The window-discriminating fixture.** See below. |

## The window-discriminating fixture, and how it was built

`ADEQUACY.md` §5.2 records that local coherence and fulfilment collapse to the *wider*,
two-period window `[-2·nb, nm + 2·nf)`, while box faithfulness collapses to the *narrower*,
one-period window `[-nb, nm + nf)`. A re-checker that mistakenly used the narrow window for local
coherence or fulfilment would silently accept a certificate whose violation lies in the outer
band `[-2·nb, -nb) ∪ [nm+nf, nm+2·nf)`. `04_window_discriminator_coherence.json` exhibits exactly
such a violation, sited by construction rather than by search.

**Construction (the back-segment seam).** With `nb = 1`, `nm = 0`, `nf = 1`:

- `back = [{g U e}]` — the until formula `g U e` (wire: `untl(event=e, guard=g)`) is asserted at
  every negative position, with neither `g` nor `e` present.
- `fwd = [{e, g U e}]` — from position `0` onward the label is the constant `{e, g U e}`.

The decoding is exactly periodic (`Periodic.unrollOf`'s `cyc`, using Lean's non-negative integer
`%`): every `t < 0` reads `back[0]`, and every `t ≥ 0` reads `fwd[0]`.

- **At `t = -1`** (inside the narrow window `[-1, 1)`), local coherence checks `g U e ∈ L(-1)`
  against the *real* neighbour `L(0) = fwd[0] = {e, g U e}`: `e ∈ L(0)` is true, so the
  fixpoint's right-hand side is true, matching the left-hand side. **Coherent.**
- **At `t = -2`** (in the outer band `[-2, -1)`, outside the narrow window but inside the wide
  one `[-2, 2)`), the *same* periodic decoding gives `L(-2) = back[0] = {g U e}` — identical
  content to `L(-1)`, since `nb = 1`. But the neighbour used to check coherence at `t = -2` is
  `L(-1) = back[0] = {g U e}` (the periodic *image*, not the real boundary): `e ∉ L(-1)` and
  `g ∉ L(-1)`, so the right-hand side is false while the left-hand side (`g U e ∈ L(-2)`) is
  true. **Incoherent.**

This is precisely the seam the plan's construction sketch names: the position just left of the
first repeated back period (`t = -1`) has the real `mid`/`fwd` boundary as its neighbour, while
its periodic image one period further back (`t = -2`) has only the repeated `back` content as its
neighbour, and the two disagree. A checker that evaluates only `t = -1` (the narrow window) finds
no violation and would wrongly accept the certificate; a checker that also evaluates `t = -2` (the
wide window) correctly rejects it. `test_certificate_fixtures.py` asserts both halves of this
claim mechanically, including that the assertion genuinely fails if the window parameter is
narrowed to one period.

## The fulfilment-side seam: attempted, found to be non-discriminating, recorded per the plan's Scope Hypothesis

The plan's Scope Hypothesis asks for the same construction "once for local coherence and once for
fulfilment," with an explicit escape hatch: *"If the fulfilment-side seam proves impossible
(fulfilment violations may be genuinely period-invariant, in which case only the coherence-side
seam discriminates), record that finding in the fixture README.md with the evidence and ship the
coherence-side fixture alone."* That is the case here, and this is the evidence.

**Why the back-segment seam does not discriminate for fulfilment.** Unlike local coherence,
fulfilment is a genuine existential — *some* later position delivers the event with the guard
holding throughout. Attempting the same one-period back cycle (`nb = 1`) construction shows that
whenever local coherence holds throughout an *unboundedly long* back stretch with `g U e`
asserted true and `e` withheld, the only way to sustain that fixpoint (via the "carry forward"
branch `g ∧ (g U e)` at every subsequent position) is for `g` itself to be present at *every*
back position. But once `g` is present throughout the whole back region, it is available as a
witness-guard from *any* back position all the way to the boundary, so a witness at `s = 0` (or
wherever `e` is first delivered forward) succeeds regardless of how far back the query position
is — fulfilment holds uniformly, with no discriminating position in the outer band. Concretely:
taking `back = [{g U e, g}]` (needed for self-consistency once `e` is withheld throughout `back`)
makes every back position fulfilled via the same forward witness, by an argument that does not
depend on distance from the origin.

This is not merely an artifact of the one-period example: `Decide.lean`'s own module commentary
(the `Fulfilment, position by position` section immediately preceding the window collapse)
describes the reduction as resting on *two* separate facts — a **bounded witness**
(`untlObl_iff_bounded`) and **periodicity** — and calls it "the harder reduction, not a matter of
shifting a window," in contrast to local coherence and box faithfulness, whose window collapses
are pure periodicity arguments. The attempted construction here is consistent with that
description: breaking the "carry forward" fixpoint at any single back position, without also
breaking local coherence there, was not achievable, because breaking it forces `e` to be
delivered at that very position (undermining "never delivered" rather than exhibiting a
period-dependent fulfilment gap).

**Disposition.** Per the plan's Scope Hypothesis, the coherence-side fixture
(`04_window_discriminator_coherence.json`) ships alone. `ADEQUACY.md`'s window correction and
§4.1's D7 amendment (`specs/184_.../plans/01_witness-family-certificate-redesign.md`'s D7) rest
on the Lean collapse lemmas (`coherent_iff_window`, `fulfil_iff_window`,
`Metalogic/Decidability/WitnessFamily/Decide.lean:335, 743`), not on this fixture corpus, so this
finding does not weaken the window correction — it only means the *mechanical demonstration* of
the fulfilment window's necessity is not carried by a hand-built fixture in this corpus.
