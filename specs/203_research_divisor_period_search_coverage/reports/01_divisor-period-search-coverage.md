# Research Report: Divisor-period search coverage — should the bimodal search cover all divisor-periods up to each bound?

- **Task**: 203 - Research divisor period search coverage
- **Started**: 2026-09-27T05:30:00Z
- **Completed**: 2026-09-27T06:30:00Z
- **Effort**: ~2 hours
- **Dependencies**: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md` (established the non-monotonicity fact and named the two candidate routes this report evaluates in depth; that task is documenting the fact honestly in `ADEQUACY.md`/`SETTINGS.md` — this report is scoped to whether the underlying search should be *fixed* rather than merely documented)
- **Sources/Inputs**:
  - Code: `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`, `semantic/witness_constraints.py`, `semantic/certificate.py`, `semantic/core.py`, `iterate.py`
  - Docs: `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 6.1, 7, 7.1), `docs/SETTINGS.md`, `docs/A2_GAP.md`
  - Prior research: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md` (items 8–11)
  - Tests: `tests/unit/test_witness_registry.py`, `tests/unit/test_witness_constraints.py`, `tests/integration/test_certificate_a2_triangle.py` (grepped for existing divisor-non-monotonicity coverage; found none)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- `WitnessRegistry.wrap()` folds `back`/`fwd` positions by exact modulus, so a single search at
  configured `(back, fwd) = (nb, nf)` represents exactly the families whose true back/fwd periods
  **divide** `nb`/`nf` — never more. Raising `nb` is therefore not monotone: a family SAT at
  `nb=3` can be genuinely UNSAT at `nb=4` or `nb=5` and SAT again at `nb=6`. This is already
  measured and documented (task 195's report, `ADEQUACY.md` §7.1); this report's job is to decide
  whether to fix the underlying search, not to re-document the fact.
- Three routes were compared. **Recommended: a bounded sweep over `back' ∈ [1,back]` and
  `fwd' ∈ [1,fwd]` (mid fixed), reusing today's `WitnessRegistry`/`WitnessConstraintGenerator`/
  `certificate.py` completely unchanged, one independent Z3 call per `(back', fwd')` pair, first
  SAT wins.** This is the practical content of the dispatch's route (b), refined below (the literal
  reading of "union over divisors of the bound" is already the status quo, not a change — see
  Finding F1).
- **Recommend against** re-encoding the search itself to represent "period ≤ n" inside a single Z3
  call (dispatch's route (c)) at this time. It costs the same asymptotic work as the sweep but
  concentrated in one larger, harder-to-solve instance, requires new constraint-generation code in
  three modules, and reopens the encoding-completeness argument (`ADEQUACY.md` §7.3/`A2_GAP.md`)
  for the new clause shapes — none of which the sweep needs. This is disproportionate given A1 is
  still `[NOT STARTED]` and A0 permanently caps the achievable claim at "ℤ-time valid," so no
  amount of search-side completeness work changes the headline result until A1 lands.
- **Correction to the dispatch's framing**: neither route touches the certificate wire format or
  the Lean-side re-checker. `LabelledLasso.nb`/`nf` are derived from the *exported* label array's
  length (`certificate.py:86,94`), and the re-checker's windows are computed from that exported
  length, not from the search's configured settings — see Finding F4.
- Route (a) (leave exact-period semantics, document the divisibility rule) remains necessary
  regardless of the outcome here and is already task 195's in-flight work on the same files; this
  report's finding is that documentation alone leaves `ADEQUACY.md` §7.1 condition (iii)
  undischarged, not that it is wrong to do.
- The one real cost risk of the recommended sweep is asymmetric: a formula expected to have **no**
  certificate (`expectation: False`, a theorem) must exhaust the *entire* `back × fwd` grid before
  reporting UNSAT (no early exit on the negative side), so theorem-style examples pay the full
  multiplicative cost while countermodel-style examples usually exit early. This should be
  benchmarked against the existing 53-example suite before any default-behavior change ships.

## Context & Scope

The dispatch asks for a recommendation, not an implementation, comparing:

- (a) leave exact-period semantics, document the divisibility rule (handled elsewhere, task 195);
- (b) "search the union over all divisors of each bound," costing slot/variable/solve-time blow-up
  and whether `sel`/(C1)–(C4) survive unchanged;
- (c) reformulate the encoding so a bound means "period at most n" directly, costing the wire
  format and Lean re-checker.

This report treats (a) as already in progress elsewhere and focuses on comparing genuine fixes —
(b) and a corrected reading of (b), against (c) — under the proportionality constraint
`ADEQUACY.md` §7 establishes: A0 (the frame-class gap, §7.2) permanently caps the strongest honest
claim at "ℤ-time valid," and A1 (compression, §7.1) is `[NOT STARTED]`, so A3 (bound realization,
of which condition (iii) is part) is "vacuous until A1 supplies `f`." Investing disproportionately
in the search-completeness side of A3 while A1 remains open does not move the headline result.

## Findings

**F1 — the literal "union over divisors of the bound" is already the status quo, not a change.**
A single search at configured `back = n` already represents every family whose true back-period
divides `n`: nothing in `WitnessConstraintGenerator` prevents Z3 from choosing a repeating
sub-pattern inside the `n`-slot table (a period-`p` pattern with `p | n` is just a special case of
an assignment to the `n` slots). This is exactly what `ADEQUACY.md` §7.1 and `SETTINGS.md` already
state: "representable at configured length `n` iff `p` divides `n`." So route (b) as literally
worded adds nothing over today's behavior at a single bound. The load-bearing version of route (b)
— the one that actually restores monotonicity in the configured bound — is a **sweep over every
candidate length from 1 up to the bound**, not merely the divisors of the bound itself: the union
`⋃_{d=1}^{n} {periods dividing d}` is exactly `{1, ..., n}` (every `p ≤ n` divides itself), which is
what "period at most `n`" needs. This report evaluates that corrected version.

**F2 — `mid` never needs sweeping.** `mid` is read directly (no modulus; `SETTINGS.md`,
`core.py:41-45`), so it is already a genuine maximum and monotonic on its own. Only `back` and
`fwd` need the sweep. This narrows task 195's report's grid-sweep proposal (stated generally as
"`(back, mid, fwd)` over the grid `≤ f(|C|)`, at most `f^3` solver calls") to **`back_max × fwd_max`
calls with `mid` held fixed at its configured value** — quadratic in the bound, not cubic.

**F3 — the sweep needs zero changes to `WitnessRegistry`, `WitnessConstraintGenerator`, or
`certificate.py`.** Each `(back', fwd')` call in the sweep constructs an independent
`WitnessRegistry(back', mid, fwd', ...)` and `WitnessConstraintGenerator` exactly as
`BimodalSemantics.__init__` (`core.py:165-170`) already does for the single configured triple. The
`sel` one-hot target selector (`witness_constraints.py:138-174`) and (C1)–(C4)
(`certificate.py:269-436`) are untouched line-for-line — they already operate purely in terms of
whatever `nb`/`nm`/`nf` the registry passed to them carries. The only new code is an orchestration
loop (in `core.py`/`model.py`, or a new small driver module) that tries a list of `(back', fwd')`
pairs and returns the first (or best) SAT — no change to the per-call encoding's variable count,
clause shapes, or completeness argument.

**F4 — neither route touches the certificate wire format or the Lean re-checker (corrects the
dispatch's framing).** `ADEQUACY.md` §6.1's wire contract exports each lasso's `back`/`mid`/`fwd`
as concrete **label arrays**, not as the search's configured integer settings, and
`LabelledLasso.nb`/`nf`/`nm` (`certificate.py:86-95`) are `len(self.back)`/`len(self.fwd)`/
`len(self.mid)` — derived from the exported array itself. `recheck`'s windows
(`_coherence_window`, `_box_window`, `certificate.py:213-231`) are computed from that same
derived length, independent of whatever settings produced the winning assignment. So:
- Route (b)'s sweep exports exactly one concrete, already-materialized lasso from whichever call
  won — indistinguishable on the wire from a lasso produced by today's single-call search.
- Route (c)'s single-call re-encoding, even if it internally selects among candidate periods
  `p ≤ n`, still ultimately exports one concrete lasso of whatever length that selection produced.

Both routes are wire-format- and Lean-re-checker-transparent. The dispatch's premise that route
(c) specifically "costs" the wire format and Lean side does not hold once the export contract is
read closely; this is worth recording so a future task does not re-open that cost line
unnecessarily.

**F5 — route (c)'s real cost is a new proof-obligation surface, not the wire format.** To
represent "period ≤ n" inside one Z3 call (rather than one call per candidate period), `wrap()`'s
modulus-`n` folding must be replaced by something that lets the *effective* period be any value
`p ≤ n`, not just divisors of `n` (the same math fact as F1: a flat `n`-slot table under modulo-`n`
folding only ever yields divisors of `n`). The natural construction is an existential
period-selector — a one-hot choice among `p = 1..n`, each with its own `p`-slot sub-table and
guarded equality constraints — which costs `O(Σ_{p=1}^{n} p · |closure|) = O(n²·|closure|)`
additional boolean variables per lasso segment, concentrated in a **single**, larger Z3 instance.
That is the same asymptotic order as the sweep's `O(back_max·fwd_max)` separate calls (each
`O(back'+fwd'|·|closure|)`-sized), but:
- it requires new constraint-generation code in `WitnessRegistry`, `WitnessConstraintGenerator`,
  and `certificate.py` (new clause shapes for the period-selector's guarded equalities), which
  `ADEQUACY.md` §7.3/`A2_GAP.md`'s encoding-completeness argument does not yet cover and would need
  to be re-established for;
- one large combined instance typically solves worse than many small independent instances of
  equivalent total size, since clause interaction and backtracking scale worse than linearly —
  the opposite of what the sweep gets "for free" by keeping every call as small and simple as
  today's single search.

**F6 — proportionality: the cheap route discharges exactly what is needed, no more.**
`ADEQUACY.md` §7.1 lists three things a genuine A1-reduction needs; (iii) is "a demonstration that
this repository's search represents the compressed family at the configured `back`/`fwd`/`mid` —
not merely that `back, mid, fwd` are 'at least' the bound." Once A1 supplies a concrete `f(|C|)`,
setting the sweep's bound to `f(|C|)` makes representable-periods-at-bound exactly `{1,...,f(|C|)}`
— which is exactly what (iii) needs, and the sweep discharges it exactly as well as the expensive
re-encoding does. Since A0 permanently caps the achievable claim regardless (§7.2) and A1 is
independently `[NOT STARTED]` (§7.1), investing in route (c) now buys nothing route (b) does not
already buy, at materially higher engineering and proof cost.

**F7 — no regression test currently pins the non-monotonicity fact.** A grep of
`tests/unit/test_witness_registry.py`, `tests/unit/test_witness_constraints.py`, and
`tests/integration/test_certificate_a2_triangle.py` for the `(3,1,3)`/`(6,1,6)` vs. `(4,1,4)`/
`(5,1,5)` example (task 195's report, item 9 and its Appendix A) found no match — the fact is
recorded only in prose (`ADEQUACY.md` §7.1, `SETTINGS.md`, the 195 report). Whichever route is
adopted, a machine-checked pin of this fact belongs in the suite so a future refactor of `wrap()`
cannot silently regress it.

## Decisions

- **D1**: Recommend the bounded sweep (route (b), corrected per F1/F2: sweep `back' ∈ [1,back]` ×
  `fwd' ∈ [1,fwd]`, `mid` fixed) as the concrete fix to build, staged below — not built by this
  research task.
- **D2**: Recommend against building route (c) now, on proportionality (F6) and unnecessary-proof-
  surface (F5) grounds. Revisit only if A1 lands and the sweep's call count is empirically
  prohibitive for the family sizes A1 actually specifies — and even then, prefer optimizing the
  sweep (parallelism, ordering, early exit) before re-encoding.
- **D3**: Route (a) (documentation, task 195) remains necessary independent of this recommendation
  — this report's finding is that documentation alone leaves condition (iii) undischarged, not
  that documenting the current behavior is the wrong thing to do now.
- **D4**: The dispatch's "union over all divisors of each bound" is, read literally at a single
  bound, already today's behavior (F1); the load-bearing route is the `1..n` sweep, which subsumes
  that literal reading as a per-triple special case.

## Recommendations

Staged path, cheapest and lowest-risk first:

1. **Stage 0 (now, ~1-2 hrs) — pin the fact.** Add a regression test capturing the SAT-at-`(3,1,3)`/
   `(6,1,6)` vs. UNSAT-at-`(4,1,4)`/`(5,1,5)` measurement directly in this repo's suite (natural
   home: `tests/unit/test_witness_registry.py` or `tests/integration/test_certificate_a2_triangle.py`),
   since F7 found no existing pin. Independent of, and useful regardless of, the routes below.
2. **Stage 1 (small, ~0.5-1 day) — build the sweep driver.** A new orchestration function (e.g. in
   `semantic/core.py` or a small new module) iterating `back' ∈ [1,back]`, `fwd' ∈ [1,fwd]` in
   increasing order (so the common case — most of the 53 examples already decide at
   `back=fwd=2`, `SETTINGS.md`'s tip #1 — pays only a small constant multiplier), constructing an
   independent `WitnessRegistry`/`WitnessConstraintGenerator`/solver per pair exactly as today's
   single-shot path does (F3), returning the first SAT or reporting UNSAT only after exhausting the
   grid. Zero changes to `WitnessRegistry`, `WitnessConstraintGenerator`, or `certificate.py`.
3. **Stage 2 (opt-in first, then benchmark) — expose as a new setting, do not flip the default
   yet.** Add e.g. `search_mode: 'exact' | 'sweep'` (default `'exact'`, unchanged) rather than
   replacing the current behavior outright. Benchmark the sweep against the full 53-example suite,
   with particular attention to `expectation: False` (theorem) examples: unlike a
   countermodel-search, a theorem must exhaust the *entire* `back_max × fwd_max` grid with every
   call UNSAT before the sweep can report UNSAT — there is no early exit on the negative side, so
   theorem-style examples pay the full multiplicative cost every time, not just the pathological
   large-period cases. Only after this is measured and found acceptable should a follow-on task
   consider flipping the default (consistent with this project's fail-fast/no-compatibility-shim
   principle, but only once the cost is known rather than assumed).
4. **Stage 3 — coordinate documentation.** If/when Stage 2 changes the default, `SETTINGS.md`/
   `ADEQUACY.md`/`core.py`'s D4 need a follow-on edit describing the new semantics. This is a
   sequencing dependency on task 195's in-flight edits to the same files, not a conflict: task 195
   fixes the wording of *today's* exact-period semantics; a later task would need to re-edit those
   same sections if and when the default changes.
5. **Stage 4 (only if A1 ever lands)** — re-derive `ADEQUACY.md` §7.1 condition (iii) as discharged
   by Stages 1-2's sweep at bound `f(|C|)` (F6), closing A3 without further search-side work.
6. **Do not build route (c) now** (D2). Note it only as a future optimization path if empirical
   sweep costs at A1's eventual family sizes prove prohibitive, and prefer optimizing the sweep
   itself first (see Risks).

## Risks & Mitigations

- **Asymmetric cost on theorem-style (`expectation: False`) examples**: the sweep's UNSAT side has
  no early exit, so these examples cost the full `back_max × fwd_max` multiplier, not a small
  constant one. *Mitigation*: benchmark before any default change (Stage 2); if unacceptable,
  keep the sweep opt-in indefinitely, or bound its grid more tightly than the raw configured
  `back`/`fwd` (e.g. sweep only up to a separately-configured `max_sweep` rather than the full
  configured bound).
- **Wall-clock cost at large configured bounds**: `back_max × fwd_max` calls is quadratic in the
  bound. *Mitigation*: the existing `maximize`-mode multiprocessing infrastructure
  (`builder/serialize.py`) already parallelizes independent Z3 invocations in this codebase and
  could be reused to run sweep calls concurrently rather than sequentially, before considering
  route (c)'s single-instance re-encoding.
- **Driver must respect `finalize_certificate`'s idempotency guard (D6)**: `core.py`'s two-phase
  constraint emission (`_certificate_finalized`) is written for one registry per
  `BimodalSemantics` instance; a sweep driver constructing multiple registries per solve needs to
  either instantiate a fresh `BimodalSemantics`-like object per candidate pair or otherwise avoid
  reusing a single instance's `_certificate_finalized` state across pairs. This is an
  implementation detail for Stage 1, not a blocker, but should be scoped explicitly in that
  stage's plan.

## Appendix

- References:
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py:125-132` (`wrap()`),
    `:120-123` (`slots_per_lasso`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py:138-174` (`sel`,
    `target_constraints`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py:86-95` (`LabelledLasso.nb`/
    `nm`/`nf`), `:213-231` (window helpers), `:269-436` (C1–C4, `recheck`)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py:35-45` (D4), `:165-170`
    (registry/generator construction)
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md:517-608` (§7, §7.1)
  - `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md:18-45,145-155` (segment-length
    settings, tips)
  - `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md:193-257`
    (items 8-11: the original measurement and the two routes this report refines)
