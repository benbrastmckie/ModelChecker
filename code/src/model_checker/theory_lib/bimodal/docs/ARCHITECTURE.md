# Bimodal Logic Architecture

## Overview

The bimodal theory searches for **witness-family certificates** over discrete (ℤ) time — a
quantifier-free Z3 search whose result, when satisfiable, is a finite, independently checkable
object that denotes an infinite **certified `ShiftSet` model** by construction. This document
describes the real architecture that implements that search: the module layout, the two-phase
constraint emission, the certificate/model relationship, and the soundness guarantee. It replaces
an earlier version of this document describing a window-and-abundance Z3 encoding (`ForAll`
frame axioms, an "abundance" constraint, world-array extraction); that encoding is retired
outright, not repaired — see `semantic/core.py`'s own module docstring for the decisive evidence
(it refutes the paper's own MF axiom) and `../README.md`'s "The Certificate Search" for a
higher-level summary.

## Table of Contents

- [Core Components](#core-components)
- [The Certificate Search](#the-certificate-search)
- [The Two-Phase Constraint Emission](#the-two-phase-constraint-emission)
- [The Independent Re-Check (Obligation S3)](#the-independent-re-check-obligation-s3)
- [The (SOUND) Theorem](#the-sound-theorem)
- [Operator Implementation](#operator-implementation)
- [Model Iteration](#model-iteration)
- [Never Reporting Validity (D8)](#never-reporting-validity-d8)
- [Why ℤ-Time Only](#why-z-time-only)
- [Extension Points](#extension-points)
- [Retired Designs](#retired-designs)
- [Testing Architecture](#testing-architecture)

## Core Components

### Theory Structure

```
bimodal/
├── __init__.py               # Public API and theory configuration
├── semantic/                 # Package (not a bare semantic.py module)
│   ├── formula.py            # Lean-mirroring Formula ADT, closure, translation, JSON codec
│   ├── certificate.py        # LabelledLasso/WitnessFamily, JSON writer, pure-Python re-checker
│   ├── witness_registry.py   # The Z3 variable layer (label bits, box guesses, lasso allocation)
│   ├── witness_constraints.py # Quantifier-free constraint generators for (C1)-(C4)
│   ├── symmetry.py            # Rotation/permutation group, its actions, orbit-invariant key
│   ├── core.py                # BimodalSemantics: settings, variable layer, two-phase emission
│   ├── model.py                # BimodalStructure: extraction, re-check, printing
│   └── proposition.py          # BimodalProposition: label-membership truth lookups
├── operators.py               # Operators as label-lookup / translate-mirroring generators
├── iterate.py                 # BimodalModelIterator: blocking clauses on labels/guesses
├── examples.py                # 53 example formulas
├── docs/                      # Documentation (this file and others)
└── tests/                     # Unit and integration tests
```

Bimodal does not ship a `notebooks/` directory (logos and exclusion do); this is a recorded,
deliberate gap, not an oversight in this listing.

### Class Hierarchy

```
BimodalSemantics(SemanticDefaults)
├── settings: back, mid, fwd, max_witnesses, max_time, expectation, iterate, solver
├── owns a WitnessRegistry (the Z3 variable layer)
├── owns a WitnessConstraintGenerator (the (C1)-(C4) constraint builders)
└── true_at/false_at: label-membership lookups, no quantifiers

BimodalStructure(ModelDefaults)
├── on __init__: extracts a WitnessFamily from a satisfying Z3 model (if any)
├── immediately re-checks it with the pure-Python `certificate.recheck` (obligation S3)
└── prints the certificate, the box-guess table, and each false box's witness

BimodalProposition(PropositionDefaults)
└── computes {lasso_index: (true_positions, false_positions)} directly from labels

bimodal_operators: OperatorCollection
├── Extensional: NegationOperator, AndOperator, OrOperator, BotOperator
├── Modal: NecessityOperator (primitive), DefPossibilityOperator (defined)
├── Temporal: FutureOperator, PastOperator, UntilOperator, SinceOperator (primitive);
│             DefFutureOperator, DefPastOperator, DefNextOperator, DefPrevOperator (defined)
└── Defined extensional: ConditionalOperator, BiconditionalOperator, TopOperator
```

## The Certificate Search

A certificate is searched over the subformula closure `C` of an inference's premises and
conclusions (`semantic/formula.py`'s `closure_of`), itself built from a `Formula` ADT with exactly
six constructors (`atom | bot | imp | box | untl | snce`) structurally identical to BimodalLogic's
own `FormalSystem.Syntax.Formula` — the label domain is exactly the Lean closure, by design, so
the search and the Lean-formalized conditions it satisfies talk about the same objects.

The searched object (`semantic/certificate.py`):

- **`LabelledLasso`**: a `(back, mid, fwd)` triple of label lists, decoded to a bi-infinite
  function `ℤ → 𝒫(C)` by `LabelledLasso.label`: strictly negative positions repeat `back`
  cyclically, `[0, len(mid))` reads `mid` directly, and positions at or past `len(mid)` repeat
  `fwd` cyclically — mirroring `Periodic.unrollOf` in the Lean development.
- **`WitnessFamily`**: a box guess `bx : Formula → Bool` plus a non-empty tuple of `LabelledLasso`s,
  `lassos[0]` the **main lasso** where the target condition is read.

A certificate must satisfy the four conditions (C1)-(C4) stated in full, with proofs, in
`ADEQUACY.md` section 1; `../README.md`'s "The Certificate Search" gives the informal shape.

The Z3 variable layer (`semantic/witness_registry.py`'s `WitnessRegistry`) makes the search
quantifier-free: `back`, `mid`, `fwd`, and the closure are fixed at construction, so the variable
set — one Boolean per `(lasso, position slot, closure formula)` label bit, one Boolean box guess
per boxed closure member, and a lasso-index allocation per boxed subformula's witness lasso — is a
finite, statically-known table. A lasso's label is periodic by construction, so a single Boolean
suffices per *slot* (`back + mid + fwd` of them per lasso), not per position; `WitnessRegistry.wrap`
maps any integer position to its slot with the same arithmetic `LabelledLasso.label` decodes with.
No `ForAll`/`Exists`, no MBQI, no E-matching pattern appears anywhere in this layer.

## The Two-Phase Constraint Emission

`ModelConstraints.__init__` (`models/constraints.py:80`) reads `semantics.frame_constraints` *by
reference* and calls `semantics.premise_behavior`/`conclusion_behavior` for every premise and
conclusion **before** a `BimodalStructure` (and therefore its `_setup_solver` override) is ever
constructed. `BimodalSemantics` uses this ordering deliberately, in two phases:

1. **Phase 1 (per premise/conclusion, during translation)**: `premise_behavior`/
   `conclusion_behavior` build the guarded windowed implication `And(Implies(sel[t], bit(0, t,
   tr(p))) for t in target_window())` (and negated for conclusions) directly against the registry
   and a one-hot target selector `sel` — not by calling `true_at` at a fixed origin the way the
   retired encoding did. Every closure member these calls touch is registered into a running
   `_known_closure` set.
2. **Phase 2 (`finalize_certificate()`, called once from `BimodalStructure._setup_solver`)**: by
   the time this runs, `_known_closure` already contains every formula premise/conclusion
   translation could contribute, so box faithfulness (C3), the exactly-one selector constraint
   over `sel`, and every lasso's local-coherence (C1) and fulfilment (C2) constraints — which need
   to know every witness lasso a boxed subformula might allocate — are built here, appended to
   `self.frame_constraints` **in place** (never reassigned), so `ModelConstraints`'s aliased
   reference sees the mutation. `finalize_certificate()` is idempotent, guarded by
   `self._certificate_finalized`, so a second call (the iterator's `re_solve()`) is a no-op.

This ordering is why the certificate encoding can be quantifier-free at all: rather than asking
Z3 to reason about a variable set whose size depends on formulas not yet seen, the variable set is
grown incrementally and only closed off once every possible contributor has registered.

## The Independent Re-Check (Obligation S3)

`BimodalStructure.__init__` (`semantic/model.py`) is the mechanism that discharges (SOUND)'s
obligation S3 (`ADEQUACY.md` sections 2 and 6.2): *whatever the search reports actually satisfies
(C1)-(C4)* is decided here, on every satisfying Z3 model, by extracting a `WitnessFamily`
(`BimodalSemantics.extract_certificate`) and immediately re-checking it with the pure-Python
`certificate.recheck` — independent of the Z3 model object entirely. This is not a defensive test
bolted on after the fact; it is the thing standing between a Z3-encoder bug and a false
countermodel report. A verdict other than `"countermodel"` raises `ModelConstructionError`
immediately: nothing downstream (printing, `extract_propositions`, iteration) ever sees an
unverified certificate.

`certificate.recheck` scans a **wide window** — two periods of each lasso's periodic segments, not
one representative position per slot — because a single representative position is provably not
enough for the two slots adjacent to `mid` (see `semantic/witness_constraints.py`'s own module
docstring for the exact counterexample this design fixes). The window width mirrors the Lean
development's proved `coherent_iff_window` collapse bound (`ADEQUACY.md` section 5), so the
re-checker is not a heuristic scan but a check against a proved sufficient window.

Every found model in the example suite and the differential-oracle suite passes this re-checker;
`tests/integration/test_certificate_lean_agreement.py` additionally round-trips fixture
certificates through BimodalLogic's own `lake exe check_certificate` executable when it is
available, skipping cleanly when it is not.

## The (SOUND) Theorem

The certificate denotes a specific model, `WitnessFamily.std` (`ADEQUACY.md` section 3):

- `𝔇 := ⟨ℤ, +, 0, ≤⟩` (discrete duration domain);
- `W := {0, …, k} × ℤ` (the disjoint union of the lassos' `(index, position)` points);
- `(i, t) ⇒_x (j, u)` iff `i = j` and `u = t + x`, for every `x ∈ ℤ` (the shift relation);
- `|p| := {(i, t) ∈ W : atom p ∈ Lᵢ(t)}` (the valuation, read straight from labels);
- `τᵢ(t) := (i, t)` (the lasso's own history function).

**Theorem ((SOUND)).** *Under (C1)-(C4), the constructed model `M` refutes `Γ ⊨ σ` for every
conclusion `σ`, with `τ₀` (the main lasso's history) and `t₀` (the target position) witnessing the
countermodel.*

The proof runs through four lemmas, each with a landed, `sorry`-free Lean counterpart
(`ADEQUACY.md` sections 3-4 give the full proofs and every citation; this table is the
quick-reference index that replaces the retired frame-axiom ledger):

| Lemma | Statement (informal) | Lean name | File:line |
|---|---|---|---|
| 1 (Frame) | The constructed `F = ⟨W, 𝔇, ⇒⟩` is a task frame — compositionality, seriality, Limit, and Saturation all hold **by construction**, with Limit from `ShiftSet.sep_of_succOrder` (via `ShiftSet.ofIntAction`, kernel-checked from discreteness) and Saturation from every fibre being a *singleton* (determinism) | `ShiftSet.shRel_comp`/`shRel_serial`/`frame_isRegular` etc. | `Semantics/ShiftSet.lean:157,172,180,209,234` |
| 2 (Histories) | Each `τᵢ` is a world history, and `H_F` is exactly the `k+1` lassos and their integer translates — so `\Box` ranges over exactly the certified histories | `ShiftSet.total_eq_orbit` | `Semantics/ShiftSet.lean:252` |
| 3 (Time-shift preservation) | Truth in `M` at `(σ, t)` depends only on the carrier point `σ(t)` | `ShiftSet.forward_repr`, `WitnessFamily.sh_surj` | `Semantics/ShiftSet.lean:293`; `.../Std.lean:98` |
| 4 (Truth lemma) | For every `ψ ∈ C`: `M, τᵢ, t ⊨ ψ` iff `ψ ∈ Lᵢ(t)` — proved by induction, using (C1) for the atom/⊥/→/□ cases and (C2) for the `U`/`S` fixpoint-postponement cases | `WitnessFamily.shiftTruth_iff_mem`, `truth_iff_mem` | `.../Agreement.lean:109,193` |
| **Theorem** | Combining the above at `i=0, t=t₀` | `WitnessFamily.joint_countermodel` | `.../Agreement.lean:232` |

**Why the design is deterministic, and what that costs.** Lemma 1's Saturation step is discharged
by every fibre being a singleton, which is exactly what having lassos never share positions
buys — see `semantic/certificate.py`'s "Extension point" note. This is *not* a simplification made
for convenience: `ADEQUACY.md`'s "Why the design is deterministic" section shows it is what makes
`ShiftSet.total_eq_orbit` (Lemma 2) true, which is what makes `\Box`'s range exactly the certified
histories, which is what the Truth lemma's `□` case needs. The cost is named honestly in
`../README.md`'s Known Limitations: certified frames cannot branch at a shared state, which is
without loss for the current language but rules out a stability-modal extension without further
(open) research.

**What (SOUND) does not claim.** Completeness — that every ℤ-refutable inference has a certificate
within some length bound — is the open "compression lemma" of a separate Lean development
(`ADEQUACY.md` section 7.1), and this package's own soundness does not depend on it. See
[Never Reporting Validity](#never-reporting-validity-d8).

## Operator Implementation

Every primitive operator's `true_at`/`false_at` mirrors its own case in `semantic/formula.py`'s
`translate` dispatch: it reconstructs the `Formula` its combinator produces from its
already-translated arguments, then looks up
`self.semantics.witness_registry.bit(eval_point["lasso"], eval_point["position"], formula)`. This
is one rule per operator, stated in exactly two places (the translation table and the operator's
own `true_at`), never two independently-evolving encodings of the same rule.

`NegationOperator`/`AndOperator`/`OrOperator` needed no change when the redesign landed: their
`true_at`/`false_at` already delegate recursively to `self.semantics.true_at`/`false_at`, which is
the translate-then-lookup contract already, and their `find_truth_condition` already only
manipulates the generic `{key: (true_positions, false_positions)}` shape
`BimodalProposition.extension` still uses. `BotOperator`, `NecessityOperator`, `FutureOperator`,
`PastOperator`, `UntilOperator`, and `SinceOperator` were rewritten: they used to build quantified
Z3 formulas or read `eval_point["world"]`/`eval_point["time"]` directly, both retired.
`find_truth_condition` is deleted from every primitive operator — nothing calls it any more;
`BimodalProposition.find_extension` computes truth values directly from certificate labels.

`\\Until`/`\\Since` are guard-first (`(guard, event)`), matching the Lean `untl`/`snce`
constructors exactly — ModelChecker's own `UntilOperator`/`SinceOperator` are guard-first too, so
`translate` is positional identity, not a swap; see `semantic/formula.py`'s module docstring.
(ModelChecker was previously event-first, citing the Burgess convention; that citation is
deliberately dropped in favor of one argument order across ModelChecker, the oracle, and Lean.)

## Model Iteration

`BimodalModelIterator` (`iterate.py`) rewrites difference detection around the certificate
encoding's own variables — label bits (`WitnessRegistry._bits`) and box guesses
(`WitnessRegistry._guesses`) — rather than world histories or truth conditions, and overrides all
three of the shared iterate framework's theory-specific extension points on `BaseModelIterator`
(`model_checker/iterate/core.py`):

1. **`_pin_theory_specific_values`**: pins every certificate variable of a newly found model into
   the fresh solve that builds its `ModelStructure`. The generic pinning
   `iterate/models.py`'s `build_new_model_structure` performs (world states, `verify`/`falsify`)
   cannot reach this theory's model content at all — D3/D4 deliberately have no state-existence
   predicate; the certified carrier is `{0,...,k} x Z`, not a set of enumerated states.
2. **`_build_exclusion_constraints`** (by way of `_create_difference_constraint`): a blocking
   clause requiring difference, in at least one label bit or box guess, from every
   previously-found model. Deliberately still exact-bit/guess difference (`_bits` + `_guesses`
   only, never the target selector) -- the fallback constraint used when the shared framework's
   generic escape path is composed in, not this theory's primary distinctness mechanism.
3. **`_check_model_isomorphism`**: opts out of the shared graph-based isomorphism check
   (`iterate/graph.py`) permanently -- it is built from `z3_world_states`, which the certificate
   encoding never populates, so two bimodal models would otherwise always produce two empty
   graphs and be falsely reported isomorphic (confirmed live, not merely a theoretical concern,
   by a regression test in `iterate/tests/`) -- while performing its own real detection: an
   orbit-invariant canonical key (`semantic/symmetry.py`'s `certificate_orbit_key`) over the
   certificate's rotation/permutation symmetry group. When a match is found,
   `_create_non_isomorphic_constraint` excludes every recheck-valid element of that whole orbit,
   not just the exact bit pattern that was found -- see "Rotation/permutation-invariant
   isomorphism rejection" below.

See `ITERATE.md`'s
[How Model Diversity Is Actually Enforced](ITERATE.md#how-model-diversity-is-actually-enforced)
section and `iterate.py`'s own module docstring for the full account, and
`model_checker/iterate/README.md`'s Extension Guide for the three-hook contract shared across all
four theories.

## Never Reporting Validity (D8)

No method in `semantic/core.py`, `semantic/model.py`, or anywhere else in this theory decides "no
certificate" one way or the other as a validity claim. An unsatisfiable solve leaves
`BimodalStructure.certificate = None` and `self.target_time = None`; every print path renders this
case as "no certificate found within the configured bounds (back=…, mid=…, fwd=…). This is not a
validity claim," never as a proof. This is structural, not a wording choice: nothing this theory
builds — the constraints, the extraction, the printer — can be read as asserting validity, because
completeness (the converse of (SOUND)) is an open theorem this package's own correctness never
assumes. Deciding validity is the tableau's and the proof system's job, not this search's; see
`ADEQUACY.md` section 7.4 for the full statement of this rule and section 7 for what the open
(ADEQ) direction would and would not change about it.

## Why ℤ-Time Only

This design covers discrete (ℤ) time only; dense and continuous time are explicitly future work,
for a structural reason recorded here rather than assumed: over a dense Archimedean order, a
finite carrier forces the cones to stabilize, Limit then collapses every small-duration fibre to a
singleton, and compositionality propagates identity to every duration, so the frame would be
static and every possible world constant. Dense-time countermodel search needs finite
presentations of infinite carriers (mosaic- or region-style techniques), which this design does
not attempt. `ADEQUACY.md`'s Lemma 4 proof also uses discreteness directly: the `Until`/`Since`
truth-lemma direction is a downward induction on the coherence fixpoint law, and that descent only
terminates over `ℤ` — over a dense order it would not.

## Extension Points

- **Lasso state sharing** (not implemented): `WitnessFamily.lassos` is a plain tuple of
  independent lassos today. `semantic/certificate.py`'s "Extension point" note records that
  sharing is compatible with the certificate datatype in principle but would require re-proving
  the histories correspondence (Lemma 2) and redesigning box faithfulness around it — deliberately
  not attempted here.
- **Rotation/permutation-invariant isomorphism rejection** (iteration): implemented. The shared
  iterate framework's three theory-specific extension points route the live loop through this
  theory's own overrides (see "Model Iteration" above), and isomorphism detection/exclusion is
  rotation/permutation-invariant over `semantic/symmetry.py`'s shared group definition -- rotation
  of each lasso's periodic `back`/`fwd` segments and permutation of the witness-lasso indices --
  rather than merely exact-bit/guess difference (which `_create_difference_constraint` still
  implements, deliberately, as the fallback used when the shared framework's generic escape path
  is composed in).
- **A fixed-frame model-checking mode** (checking a given finite digraph directly, rather than
  searching for a certificate) is a distinct, optional feature, out of scope for this design.
- **The tableau/proof-system bridge**: wiring BimodalLogic's Lean tableau as a differential oracle
  at frame class Z-time, and JSON certificate export with a Lean re-verification round trip, are
  named successor tasks in the redesign's own report, not implemented here beyond the
  already-live `to_json`/`recheck_json` wire format and the `lake exe check_certificate` round
  trip this theory's own tests already exercise.

## Retired Designs

Two earlier designs are retired outright, kept here only so a future reader does not rediscover
the same dead ends:

- **The window-and-abundance encoding** (`N`/`M`-bounded time, `ForAll`/`Exists` frame axioms, a
  Skolemized "abundance" constraint asserting time-shift closure as a solver axiom). It refuted
  the paper's own MF axiom (`\Box A → \Box \Future A`) at `N=1, M=2` — decisive evidence it was not
  a model of the paper's semantics, not merely slow or incomplete. See `semantic/core.py`'s module
  docstring for the full list of deleted methods and constraint builders.
- **A separate quantifier-free `accessible_world`-witness encoding**, designed and partially
  landed before this redesign to work around an observed non-determinism in `\Box`-countermodel
  results. That non-determinism's real cause was a process-global bound-variable counter producing
  run-order-dependent Z3 variable names (fixed by resetting the counter per fresh semantics
  instance) — `ForAll` itself was never the problem. That earlier encoding is unrelated to, and
  superseded by, the certificate design this document describes; it predates the certificate
  redesign and should not be confused with `witness_registry.py`/`witness_constraints.py`'s
  current, unrelated bodies, which share only the module names.

## Testing Architecture

### Test Organization

```
tests/
├── conftest.py
├── unit/
│   ├── test_formula.py                    # Formula ADT, closure, translation, JSON codec
│   ├── test_certificate.py                # LabelledLasso/WitnessFamily, recheck
│   ├── test_certificate_fixtures.py       # Fixture certificates for round-trip tests
│   ├── test_witness_registry.py           # The Z3 variable layer
│   ├── test_witness_constraints.py        # The (C1)-(C4) constraint generators
│   ├── test_symmetry.py                   # Rotation/permutation group, actions, orbit key
│   ├── test_semantics_core.py             # BimodalSemantics settings and two-phase emission
│   ├── test_structure.py                  # BimodalStructure extraction, re-check, printing
│   ├── test_proposition.py                # BimodalProposition label lookups
│   ├── test_operators.py                  # Operator true_at/false_at against translate
│   ├── test_next_prev.py                  # Defined \Next/\Prev operators
│   ├── test_bimodal.py                    # End-to-end example checks
│   └── test_semantic_module_registration.py
└── integration/
    ├── test_certificate_lean_agreement.py # Round-trip against `lake exe check_certificate`
    ├── test_data_extraction.py
    ├── test_injection.py
    ├── test_iterate.py                    # BimodalModelIterator
    └── test_until_since_integration.py
```

See [tests/README.md](../tests/README.md) for the full running guide.

---

**Navigation**: [README](../README.md) | [Adequacy](ADEQUACY.md) | [Settings](SETTINGS.md) |
[API Reference](API_REFERENCE.md) | [User Guide](USER_GUIDE.md) | [Iteration](ITERATE.md)
