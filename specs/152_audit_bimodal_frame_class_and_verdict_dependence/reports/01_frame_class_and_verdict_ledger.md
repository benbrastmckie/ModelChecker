# Bimodal Frame-Class and Verdict-Dependence Audit

**Status**: audit-only (no changes to `core.py`, `operators.py`, or `examples.py`)
**Scope**: `code/src/model_checker/theory_lib/bimodal/semantic/core.py`,
`code/src/model_checker/theory_lib/bimodal/operators.py`,
`code/src/model_checker/theory_lib/bimodal/examples.py`

## 0. Summary

The oracle's `build_frame_constraints` currently asserts three of the JPL paper's `def:frame`
axioms in some form (`nullity_identity`, `converse`, and the composition half of
*Compositionality*, `forward_comp`) and asserts nowhere in `core.py` the other four the paper's
`def:frame` carries: *Seriality*, the interpolation half of *Compositionality*, *Limit*, and
*Spherical*. Section 1.2 below traces `thm:extension`'s actual dependency chain in the
BimodalLogic Lean formalization and finds the proof **consumes** all four of these — a larger
consumption surface than a first pass over the axiom list suggests, since the naive count only
spots the two the task's opening brief named (Seriality, Interpolation).

**Consumed is not the same question as must-be-asserted, and this audit's Phase 2 settles the
second question separately** (full three-way table in Section 1.2): of the four consumed axioms,
two — *Seriality* and *Interpolation* — must genuinely be asserted in ModelChecker's setting,
since nothing in the current encoding discharges them. The other two — *Limit* and *Spherical* —
are **free**: each is discharged by a citable BimodalLogic lemma whose hypotheses ModelChecker's
actual structure already satisfies (a finite world-state carrier for *Spherical*; the
already-asserted, unconditional `nullity_identity` biconditional over a discrete duration type
for *Limit*), with the hypothesis check carried out against ModelChecker's real encoding rather
than merely cited. So `thm:extension` cannot currently be invoked on a ModelChecker countermodel
— that conclusion is unchanged — but the corrected reason is "two axioms must be added, and two
more that the chain consumes are already free," not "four axioms are missing."

The regression baseline (Deliverable 2) shows the abundance-constraint approximation is load
bearing for exactly four examples in `examples.py`'s canonical test dictionary — the
`BM_TH_1`–`BM_TH_4` perpetuity-principle family — and for no others; every BX-axiom-system
theorem (24 examples) and every countermodel example (13 examples) is abundance-independent.

`task_restriction` (Deliverable 3) remains an **independent** gap: it grounds the Z3 solver's own
finite `is_world`/`world_function` enumeration, a concern `thm:extension` does not address at all
(it is a purely abstract-relation existence theorem). Adding the missing frame axioms would not
make `task_restriction` unnecessary.

---

## 1. Deliverable 1 — The Ledger

### 1.1 Existential vs. universal obligations

Every semantic obligation the bimodal oracle discharges falls into one of two columns:

| Column | What it requires | How the oracle discharges it |
|---|---|---|
| **(a) Existential** | A single witness: a countermodel to `\Box \phi`; a witness time falsifying `\Future \phi` | Z3 SAT search over a *finite* enumeration (`is_world` bounded by `max_world_id = M * 2**(M*N)`, `is_valid_time` bounded to the open interval `(-M, M)`) |
| **(b) Universal** | A guarantee across *all* of an unbounded/uncapped domain: truth of `\Box \phi` across all of `H_\F` (the paper's full class of world histories over a frame `\F`); truth of `\Future \phi` across all of `\D` (the paper's temporal order, an arbitrary nontrivial totally ordered abelian group — not itself finite) | No theorem in the paper is invoked. The `capped_skolem_abundance_constraint` / `depth_bounded_skolem_abundance_constraint` shift-closure family is the oracle's *sole* approximation of column (b), and it approximates only the "closed under time shifts that stay inside the window" fragment of `H_\F`'s abundance, not the paper's actual `ShiftClosed` property over an unbounded `\D`. |

**Code confirmation of the existential/finite character of column (a):**
- `is_world` is an uninterpreted Z3 predicate (`core.py:201`) whose extension in any given model
  is bounded by `max_world_id = self.M * (2 ** (self.M * self.N))` (`core.py:208`), a
  construction-time constant — never the paper's possibly-infinite `H_\F`.
- `is_valid_time`/`is_valid_duration` (`core.py:862`, `core.py:242`) restrict both time points and
  durations to the *bounded* open interval `(-M, M)` — a finite proxy for the paper's `\D`, which
  is an arbitrary totally ordered abelian group (see `TaskFrame.lean`'s `def:temporal-order`) with
  no finiteness assumption.

**Code confirmation that `\Box`/`\Future`/`\Past` quantify over the finite proxy, not the paper's
domains:**
- `NecessityOperator.true_at` (`operators.py:508`) quantifies `other_world` only over
  `semantics.is_world(other_world)` — the solver's enumerated, model-relative finite world-ID set
  — with **no** guard tying it to a paper-level `H_\F` membership condition beyond what `is_world`
  happens to satisfy in that model. The docstring's own gloss ("Box quantifies over ALL valid
  world histories unconditionally") is true only relative to *this model's* `is_world`, not to
  the paper's `H_\F` for the abstract frame.
- `FutureOperator.true_at` / `PastOperator.true_at` (`operators.py:691`, `operators.py:862`) route
  through `semantics.ForAllTime` (`core.py:396`), whose guard is `is_valid_time(time_var)` — the
  bounded `(-M, M)` window, not the paper's `\D`. The `ForAllTime` docstring is explicit that this
  is "domain D" in the *implementation's* sense (the bounded window chosen for solver
  performance), not the paper's `\D`.

**This is the single distinction the follow-on tasks are most likely to blur**: adding the
missing frame axioms (Section 1.2) to `build_frame_constraints` would still only constrain the
*finite* structures `is_world`/`is_valid_time` bound — it would never, by itself, turn column (a)'s
finite search into column (b)'s universal guarantee over the paper's unbounded `H_\F`/`\D`. The
missing axioms are a precondition for legitimately invoking `thm:extension` (which is itself
about existence of *some* extension, i.e. still an existential/constructive result, not a
universal one) — they do not close the abundance gap in column (b), which is a separate,
`ShiftClosed`-shaped question the paper's `thm:extension` chain does not speak to at all.

### 1.2 The frame-axiom gap is four axioms, not two

Re-resolving the code references against the current tree confirms the task's starting facts and
finds the gap is **larger** than "Seriality and interpolation are missing." The current
`build_frame_constraints` (`core.py:537`–`860`) asserts, of the paper's `def:frame` axiom family:

| `def:frame` axiom | Asserted in `core.py`? | Where |
|---|---|---|
| `nullity_identity` (not itself a paper axiom — see below) | Yes, as a full biconditional | `build_nullity_identity_constraint`, `core.py:280` |
| `converse` (definitional convention in the paper, not an independent axiom) | Yes | `build_converse_constraint`, `core.py:305` |
| *Compositionality*, `←` half (composition, `forward_comp`) | Yes | `build_forward_comp_constraint`, `core.py:344` |
| *Compositionality*, `→` half (interpolation) | **No** | absent |
| *Seriality* | **No** | absent — `grep -rn "serial" semantic/` (re-run for this audit) returns nothing outside comments |
| *Limit* | **No** | absent |
| *Spherical* | **No** | absent |

The BimodalLogic Lean formalization (`/home/benjamin/Projects/BimodalLogic/FormalSystem/Semantics/TaskFrame.lean`,
current tree, re-checked for this audit) states plainly: "The paper's `def:frame` carries exactly
FOUR axioms — *Compositionality* (a biconditional), *Seriality*, *Limit*, *Spherical* — and no
Nullity axiom (`lem:nullity` is derived, reflexivity only)." (`TaskFrame.lean:466`–`469`). So the
paper's actual axiom list is `{Compositionality, Seriality, Limit, Spherical}`; `nullity_identity`
and `converse` are *not* independent axioms of `def:frame` at all — `converse` is a definitional
convention and `nullity_identity` (an iff) is *strictly stronger* than what the paper's own
derived `lem:nullity` (reflexivity only) requires (`TaskFrame.lean:74`–`75`, `108`–`109`). This
means two of the three constraints `core.py`'s own docstring "bills" as TaskFrame axioms
(`core.py:554`–`560`) are not, in the paper's own terms, axioms the frame is required to carry —
they are either free (converse) or an over-strong choice already made (nullity_identity, whose
"design question stays open" per the Lean side, `Admissible.lean:286`).

**Definitions, transcribed verbatim from the Lean source of record** (paper anchors cited by
`\label`, not raw line number, per that repository's own citation convention):

- *Seriality* (`def:frame#Seriality`): "$w \Rightarrow_x u$ and $v \Rightarrow_x w$ for some
  $u, v \in W$" — **both** a successor and a predecessor exist at every nonnegative duration
  (`TaskFrame.lean`, `Serial` predicate: `∀ w x, 0 ≤ x → (∃ u, R w x u) ∧ (∃ v, R v x w)`). This is
  stronger than a one-sided "next state always exists" reading — both directions.
- *Compositionality* (`def:frame#Compositionality`), biconditional: "$w \Rightarrow_{x+y} v$ if and
  only if $w \Rightarrow_x u$ and $u \Rightarrow_y v$ for some $u \in W$." `forward_comp`
  (`core.py:344`) is exactly the `←` (composition) direction. The `→` (interpolation) direction —
  `Interpolates R := ∀ w v x y, 0 ≤ x → 0 ≤ y → R w (x+y) v → ∃ u, R w x u ∧ R u y v` — is absent.
- *Limit*: `∀ w u, (∀ x, 0 < x → ∃ y, |y| < x ∧ R w y u) → u = w` — every state within every
  positive-radius "cone" of `w` other than `w` itself is eventually excluded as the radius shrinks.
- *Spherical* (`def:frame#Spherical`): "$\bigcap \mathcal{S} \neq \emptyset$ for any
  $\supseteq$-directed family $\mathcal{S}$ of nonempty fibers and segments" — a
  spherical-completeness-style condition on the relation's fiber/segment structure, strictly
  stronger than the standard "spherically complete" ball-space condition (per the axiom's own
  paper footnote, transcribed at `TaskFrame.lean`).

**Why all four, not just two, are needed to invoke `thm:extension`.** The Lean chain
(`Extension.lean:19`–`21`) is:

```
def:constraints -> lem:constraint -> lem:admissible -> lem:step (sole Spherical site)
  -> thm:extension (Zorn) -> cor:occurrence
```

- `lem:constraint` (`Extension/Constraint.lean:43`–`55`) consumes exactly `Serial` (nonemptiness
  of fibers), `Interpolates` (nonemptiness of segments — "the left-to-right half of biconditional
  *Compositionality*"), and `forward_comp` (directedness). **Two of its three inputs are the
  missing ones.**
- `lem:admissible` (`Extension/Admissible.lean:285`–`319`), in its "new time twice" case, invokes
  `TaskFrame.nullity_of_serial_limit F.serial F.limit u` — i.e. it derives the paper's `lem:nullity`
  (zero-duration reflexivity) from *Seriality* **and** *Limit* jointly, explicitly *not* from the
  stronger `nullity_identity` field ModelChecker already asserts. **`Limit` is required here.**
- `lem:step` (`Extension/Step.lean:10`–`43`) is *Spherical*'s sole application site in the entire
  chain: "`F.spherical` — the structure field itself — ... `TaskFrame.Spherical TaskRel` ...
  applies `F.spherical` directly." **`Spherical` is required here, unavoidably** (Lean also proves,
  via `wlem_of_spherical`, that a fully choice-free discharge of the general case is impossible).
- `thm:extension` itself (`Extension/Extension.lean:44`–`58`) consumes only Zorn's lemma plus
  `lem:step` — no further axioms directly, but it inherits everything `lem:step` and
  `lem:admissible`/`lem:constraint` already needed.
- `cor:occurrence`'s one-point-history argument additionally needs `nullity_identity` specifically
  (`Extension.lean:97`–`99`, `TaskRel w 0 w` discharged by `TaskFrame.nullity_identity`) — the one
  place where ModelChecker's *stronger* choice actually pays off, since ModelChecker's iff-form
  `nullity_identity` already implies the paper's weaker derived fact.

**Ledger conclusion for Deliverable 1 (consumed)**: `thm:extension`'s proof chain, traced above,
**consumes** all four of **Seriality, Interpolation (the missing half of Compositionality),
Limit, and Spherical** — not merely the two the task's opening brief named. `nullity_identity` and
`converse` are already sufficient (indeed `nullity_identity` is over-sufficient) for what the
chain needs from them. None of the four consumed axioms would, by themselves, close the
column-(b) universal-guarantee gap (Section 1.1) — they are a precondition for a different,
existential result (`thm:extension`/`cor:occurrence`: some total history exists extending a
partial one / some history occurs at a state and time), not a substitute for it.

### 1.2a Consumed vs. asserted vs. free (this audit's Phase 2)

*Consumed* (the question Section 1.2 above answers) is a different question from *must be
asserted in ModelChecker* (the question the follow-on frame-axiom task actually needs answered).
This subsection settles the second question, with each "free" claim checked against
ModelChecker's actual encoding rather than merely cited, per the task's own instruction not to
re-derive but to re-verify.

| Axiom | Consumed by `thm:extension` chain? | Status in ModelChecker | Discharging fact |
|---|---|---|---|
| *Seriality* | Yes (`lem:constraint`, Section 1.2) | **Must be asserted** | Nothing in `core.py` discharges it; `grep -rn "serial" semantic/` returns nothing (Section 4.1, re-run) |
| *Interpolation* | Yes (`lem:constraint`, Section 1.2) | **Must be asserted** | Only the `←` (composition) half is asserted (`forward_comp`, `core.py:344`); the `→` half is absent |
| *Limit* | Yes (`lem:admissible`, Section 1.2) | **Free** | `TaskFrame.limit_of_succOrder` (`TaskFrame.lean:730`) |
| *Spherical* | Yes (`lem:step`, Section 1.2) | **Free** | `TaskFrame.spherical_of_finite` (`TaskFrame.lean:985`) |

**Why *Spherical* is free — hypothesis checked, not cited.** `spherical_of_finite`'s statement is
`theorem spherical_of_finite {W : Type} [Finite W] (R : W → D → W → Prop) : Spherical R`
(`TaskFrame.lean:985`) — its *sole* hypothesis is `[Finite W]`, and (per the `omit
[IsOrderedAddMonoid D] in` immediately above it) it is proved without using any ordered-group
structure on the duration type `D` at all, for a relation `R` of *arbitrary* shape. ModelChecker's
world-state carrier is `self.WorldStateSort = z3.BitVecSort(self.N)` (`core.py:153`) — a finite
sort of exactly `2^N` elements — which discharges `[Finite W]` directly. Because the lemma is
indifferent to `D`'s shape, none of the duration-bounding questions below bear on this discharge
at all.

**Why *Limit* is free — hypothesis checked, not cited.** `limit_of_succOrder`'s statement is
`theorem limit_of_succOrder [SuccOrder D] [NoMaxOrder D] {W : Type} {R : W → D → W → Prop}
(hnull : ∀ w u, R w 0 u ↔ w = u) : ∀ w u, (∀ x, 0 < x → ∃ y, |y| < x ∧ R w y u) → u = w`
(`TaskFrame.lean:730`). Two hypotheses:
1. `[SuccOrder D] [NoMaxOrder D]` — ModelChecker's duration argument to `task_rel` has Z3 sort
   `Int`, i.e. `D` is literally the mathematical integers `\Z`, which carry `SuccOrder`/
   `NoMaxOrder` instances as standard facts about the sort itself (`\Z` is a discrete linear order
   with no maximum). This instance search is a fact about the *type*, independent of any bound a
   particular constraint's quantifier might impose.
2. `hnull : ∀ w u, R w 0 u ↔ w = u` — this is exactly `build_nullity_identity_constraint`
   (`core.py:280`–`303`), confirmed by inspection to be **unguarded**: `z3.ForAll([w, u],
   self.task_rel(w, z3.IntVal(0), u) == (w == u))`, with no `is_valid_duration` clause anywhere in
   its body. It holds for every `w, u : BitVec[N]` unconditionally, exactly matching `hnull`'s
   shape.

The proof itself only ever instantiates the `Limit` hypothesis at `x = Order.succ 0 = 1`, which —
`\Z` being discrete — forces the witness duration `y` to be exactly `0` (`|y| < 1 ⟹ y = 0`), and
`hnull` at duration `0` closes the goal. So the discharge never reasons about `task_rel` at any
duration outside `{0}`, which is why the duration-bounding question below does not block it.

**Precedent for this exact configuration.** BimodalLogic's own `IntPresentation.toTaskFrame`
(`FormalSystem/Metalogic/Decidability/IntPresentation.lean:118`–`129`) builds a `TaskFrame ℤ` over
a finite world carrier (`Fin P.card`) and discharges *Spherical* via `spherical_of_finite` and
*Limit* via `limit_of_succOrder` — the identical `(D, W)` shape as ModelChecker's `(Z3 Int,
BitVec[N])`. Its own docstring states the consequence plainly: "bi-seriality is the sole frame
obligation a presentation ever pays... the four `def:frame` axioms cost one obligation here, not
four." This is not a novel derivation for ModelChecker's setting; it is an application of an
already-proved, already-used discharge pattern in the same repository.

**The duration-domain gap — recorded, not resolved, per the task's non-goals.** The paper requires
`\D` to be a nontrivial totally ordered abelian **group**; ModelChecker's `is_valid_duration`
(`core.py:242`) bounds durations to the open interval `(-M, M)`, which is not a group under
addition (it is not closed: two in-bounds durations can sum to an out-of-bounds one).
**`is_valid_duration` does not change this Phase 2 finding**: it is a value-level *guard*
selectively applied inside specific constraints' quantifier bodies (`converse`, `forward_comp`,
the disabled `task_restriction`) — it never restricts the Z3 *sort* of `task_rel`'s duration
argument, which remains `Int` (`= \Z`) throughout, and `build_nullity_identity_constraint` in
particular carries no such guard. So *Limit* and *Spherical* are free regardless of the
duration-bounding question.

But the gap is genuinely load-bearing **for the follow-on frame-axiom task**, in the opposite
direction from what might be assumed: because *Limit* and *Spherical* are now settled as free at
the sort level, the entire weight of "is this really an unbounded `TaskFrame \Z` in the sense
`thm:extension`'s Lean statement needs" falls on how *Seriality* and *Interpolation* get encoded.
`thm:extension`'s chain needs `F.serial`/`F.interpolates` (and the field `comp`/`forward_comp`) to
hold as literal, unconditional `TaskFrame` fields — quantified over all of `\Z`, not merely within
`(-M, M)`. If the follow-on task asserts Seriality/Interpolation guarded by `is_valid_duration`
(the natural choice for solver performance, mirroring how `converse` and `forward_comp` are
already guarded), the resulting structure would **not**, without further argument, be a genuine
`TaskFrame \Z` in the sense the Lean theorem consumes — only a `TaskFrame` restricted to a bounded
duration window, which is not literally what `Extension.lean`'s statement is over. This is
precisely the embedding question the follow-on frame-axiom task's own Deliverable 4 anticipates
("state and justify the embedding ... or record it explicitly as an open gap"); this audit
confirms the question is real and load-bearing, and leaves it open for that task to resolve rather
than resolving it here (out of this audit's scope, which is limited to Limit and Spherical).

---

## 2. Deliverable 2 — The Baseline

### 2.1 Method

Every example in `unit_tests` (`countermodel_examples` ∪ `theorem_examples`, the dictionary
`examples.py:1422` aliases as `test_example_range` — 52 examples total) was run twice, in-process,
via `model_checker.utils.testing.run_enhanced_test`, using `isolated_z3_context()` per run:

1. **baseline** — unmodified `BimodalSemantics.build_frame_constraints`.
2. **no_abundance** — a monkeypatched copy of `build_frame_constraints` with the
   `capped_skolem_abundance_constraint`/`depth_bounded_skolem_abundance_constraint` term dropped
   from the returned constraint list; every other constraint (world enumeration, convexity,
   interval, lawfulness, `nullity_identity`, `converse`, `forward_comp`, `world_uniqueness`)
   unchanged and in the same order.

The monkeypatch lives only in a throwaway process-local script
(`baselines/01_abundance-removal-script.py`); `core.py` on disk was never edited, per this
audit's non-goal. `BM_TH_5` — defined in `examples.py` but *not* included in `unit_tests`/
`test_example_range` (only in the separate, CLI-only `example_range` dict, `examples.py:1477`) —
was additionally run for completeness since Deliverable 2 asks for "every example in
`examples.py`"; it is reported separately from the 52-example canonical set.

**Host conditions** (per the task's request to record them, given `BM_CM_1`'s documented flake):
`uptime` load average at run start was 4.62/4.59/4.18 on a 24-core host (~19% average
utilization) — not a fully idle host, but not contended either. `BM_CM_1` (`example_case7`,
per the pytest `unstable` marker's own entry criteria in `test_bimodal.py:63`–`94`) resolved in
7.66s this run with no flake observed. This single run does not supersede the documented
20-run/20-seed exit criteria for that marker; it is recorded as one data point at a known host
condition, not a re-adjudication of the flake.

Full raw results: `baselines/01_abundance-removal-verdicts.json`. Full run transcript:
`baselines/01_abundance-removal-run.log`. Script: `baselines/01_abundance-removal-script.py`.

### 2.2 Classification

**Abundance-dependent (4 of 52) — verdict changes when the abundance constraint is removed:**

| Example | Formula | Baseline (with abundance) | No-abundance | Verdict impact |
|---|---|---|---|---|
| `BM_TH_1` | `\Box A -> \Future A` (M=3) | Timed out at 30s max_time — `inconclusive` this run (consistent with `test_bimodal.py`'s documented `KNOWN_TIMEOUT_EXAMPLES` exclusion for exactly this reason) | SAT countermodel found in 0.09s, `mismatch` against `expectation=False` | Abundance-dependent. `examples.py:1473`'s own inline comment on this example (`# Has countermodel`) independently corroborates that a countermodel exists once the theorem's supporting constraint is weakened/absent, matching `build_frame_constraints`'s own docstring claim (`core.py:598`–`601`) that abundance is *why* this is currently treated as valid. |
| `BM_TH_2` | `\Box A -> \Past A` (M=3) | Timed out at 30s — `inconclusive` this run (same documented exclusion) | SAT countermodel found in 0.10s, `mismatch` | Abundance-dependent, same basis as `BM_TH_1` (`examples.py:1474` `# Has countermodel`). |
| `BM_TH_3` | (M=2) | `match` (no countermodel), 0.04s, clean decision | SAT countermodel found, `mismatch`, 0.04s | Abundance-dependent — clean flip, both sides decided. |
| `BM_TH_4` | (M=2) | `match` (no countermodel), 0.04s, clean decision | SAT countermodel found, `mismatch`, 0.04s | Abundance-dependent — clean flip, both sides decided. |

For `BM_TH_1`/`BM_TH_2`, the baseline side did not reach a clean UNSAT decision in this run (a
known, previously-documented flake basis, not a new finding) — the dependence conclusion rests on
the no-abundance side's fast, unambiguous SAT result plus the pre-existing code-comment and
example-file corroboration cited above, not on treating the timeout itself as evidence.

**Abundance-independent (48 of 52, including `BM_TH_5`) — verdict unchanged either way:**

- All 13 countermodel examples (`EX_CM_1`, `MD_CM_1`–`6`, `TN_CM_1`, `TN_CM_2`, `BM_CM_1`–`4`)
  remain `match` (countermodel still found) with abundance removed — consistent with removing a
  constraint only ever *weakening* the frame, which can never destroy an already-satisfying
  countermodel. `TN_CM_2`'s baseline hit its own separately-documented timeout
  (`test_bimodal.py:46`: "countermodel search times out even at 15s") at the 10s `max_time` used
  here (`inconclusive`), while the no-abundance run found the same expected countermodel in 0.06s
  — a solver-speed effect, not a verdict dependency, since the countermodel is expected either
  way.
- All 24 BX-axiom-system theorems (Layers 1–4: `PROP_K_TH`/`PROP_S_TH`/`EX_FALSO_TH`/`PEIRCE_TH`,
  `MODAL_T_TH`/`MODAL_4_TH`/`MODAL_B_TH`/`MODAL_5_TH`, and the full `BX1`–`BX13` temporal family)
  plus `EX_TH_1`, `MD_TH_1`, `MD_TH_2`, `TN_TH_2` remain `match` (still no countermodel) with
  abundance removed. These formulas' validity does not route through the `\Box`/full-timeline
  `\Future`/`\Past` shift-closure the abundance constraint approximates.
- `MF_MODAL_FUTURE_TH` (`\Box A -> \Box \Future A`) and `BM_TH_5` (`\Box A -> \Future \Box A`,
  present in `examples.py` but excluded from `unit_tests`/`test_example_range`) are **already**
  `mismatch` (a countermodel is found) with abundance intact, and remain `mismatch` without it —
  pre-existing, already-known non-theorems (see `test_bimodal.py:35`–`37`'s note on
  `MF_MODAL_FUTURE_TH`), independent of this audit's abundance question.

### 2.3 What this means for the follow-on tasks

The regression surface that narrowing the frame class must not silently break is exactly
`BM_TH_1`–`BM_TH_4` (and, if it is ever added back to the canonical suite, `BM_TH_5`, which is
already a known non-theorem and not at risk of a new regression). Every other example's verdict
is decided by constraints untouched by the abundance approximation and is not informative for
distinguishing "legitimate frame-class narrowing" from "genuine regression" with respect to
*this* constraint. A follow-on task that adds the four missing frame axioms (Section 1.2) should
re-run this same baseline script against the *new* constraint set and confirm `BM_TH_1`–`BM_TH_4`
resolve the same way (or, if the paper's genuine axioms happen to also validate/invalidate them
by a different route, document that explicitly rather than silently accepting a verdict change).

---

## 3. Deliverable 3 — The `task_restriction` Verdict

**Verdict: `task_restriction` remains an independent gap. It is not subsumed by adding
Seriality/Interpolation (or Limit/Spherical) and should not be treated as redundant once those
axioms land.**

**Reasoning.** `task_restriction` (disabled constraint documented at `core.py:747`–`835`, the
soundness analysis this audit was asked to assess) would assert:

```
forall s, d, u.  task_rel(s, d, u)  ->  exists w, t.  is_world(w) and w(t) = s and w(t+d) = u
```

— i.e., every triple the abstract `task_rel` relation makes true must be *witnessed* by one of
the solver's finitely many enumerated world histories (`is_world`/`world_function`). This is a
constraint that couples two structurally separate pieces of the encoding: the free/uninterpreted
ternary relation `task_rel`, and the finite enumeration `is_world`/`world_function` the solver
actually builds.

Seriality, Interpolation, Limit, and Spherical, by contrast, are all stated **purely over the
abstract `task_rel` relation** — inspecting their Z3-encoding analogues (`build_nullity_identity_constraint`,
`build_converse_constraint`, `build_forward_comp_constraint`, `core.py:280`–`394`) and their Lean
statements (`Serial`, `Interpolates`, `cone`/`Limit`, `Spherical`, `TaskFrame.lean`) confirms none
of them mention `is_world` or `world_function` at all. Adding all four to `build_frame_constraints`
would only ever constrain `task_rel` as an abstract relation on the raw `BitVec[N]` state space; it
supplies no mechanism forcing every `task_rel` triple to correspond to some enumerated world's
slice. The same holds transitively for `thm:extension` itself: it is a statement about the
*abstract* structure `(W, \D, \Rightarrow)` — "every partial history is extended by some total
world history [in the abstract sense the paper defines `H_\F` by]" — not a claim that a
*specific finite Z3 model's* `is_world` enumeration must contain a witness for every triple that
model's `task_rel` happens to satisfy. `thm:extension` and `task_restriction` answer genuinely
different questions: the former is about existence of members of `H_\F` in the abstract frame;
the latter is about self-consistency between two separate structures *within one already-built Z3
model*.

**Consequence for the existing soundness analysis (`core.py:751`–`801`).** The analysis's claim
that phantom `task_rel` triples do not affect operator truth values (`operators.py`'s
`\Box`/`\Future`/`\Past` truth conditions read only `is_world` and `world_function` array
contents — confirmed by inspection of `NecessityOperator.true_at`, `FutureOperator.true_at`,
`PastOperator.true_at`, none of which reference `task_rel` directly) is unaffected by whether the
four missing frame axioms are added. Adding them does not change what `task_rel`'s role is in the
truth-condition machinery, and does not newly ground any triple in a concrete world — so the
existing SAT/UNSAT-asymmetry conclusion in that comment (SAT results may not transfer to the
grounded class; UNSAT results do) stands independent of this audit's other findings, and
`task_restriction` should continue to be tracked as a separate, standing gap rather than something
the interpolation/seriality follow-on work will incidentally close.

---

## 4. Code References (re-resolved for this audit, current tree)

| Item | Location |
|---|---|
| `build_frame_constraints` | `code/src/model_checker/theory_lib/bimodal/semantic/core.py:537` |
| `build_nullity_identity_constraint` | `core.py:280` |
| `build_converse_constraint` | `core.py:305` |
| `build_forward_comp_constraint` | `core.py:344` |
| Disabled `task_restriction` constraint + soundness analysis comment | `core.py:747`–`835` |
| `capped_skolem_abundance_constraint` | `core.py:1447` |
| `depth_bounded_skolem_abundance_constraint` | `core.py:1530` |
| `build_task_minimization_constraint` (also disabled, item 11) | `core.py:1628` |
| `is_valid_time` / `is_valid_duration` (bounded `(-M, M)` proxy for `\D`) | `core.py:862`, `core.py:242` |
| `ForAllTime` / `ExistsTime` (bounded, not paper-`\D`) | `core.py:396`, `core.py:469` |
| `is_world` (finite, model-relative; `max_world_id` bound) | `core.py:201`, `core.py:208` |
| `NecessityOperator.true_at` / `false_at` | `code/src/model_checker/theory_lib/bimodal/operators.py:508`, `562` |
| `FutureOperator.true_at` | `operators.py:691` |
| `PastOperator.true_at` | `operators.py:862` |
| `unit_tests` / `test_example_range` (52-example canonical dict) | `code/src/model_checker/theory_lib/bimodal/examples.py:1422`, `1426` |
| `example_range` (CLI-only, includes `BM_TH_5`) | `examples.py:1435`–`1478` |
| `KNOWN_TIMEOUT_EXAMPLES` / `UNSTABLE_EXAMPLES` (pytest exclusion basis) | `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:44`–`95` |
| Lean: `def:frame`'s four-axiom list, `nullity_identity` design-question note | `/home/benjamin/Projects/BimodalLogic/FormalSystem/Semantics/TaskFrame.lean:74`–`75`, `108`–`109`, `466`–`469` |
| Lean: `Serial`, `Interpolates`, `Spherical`, `cone`/`Limit` predicates | `TaskFrame.lean:377` (`Serial`), `:395` (`Interpolates`), `:362` (`Spherical`), `:231` (`cone`) |
| Lean: `lem:constraint`'s three-input proof (`Serial`, `Interpolates`, `forward_comp`) | `FormalSystem/Semantics/Extension/Constraint.lean:43`–`91`, `217`–`244` |
| Lean: `lem:admissible`'s `Serial`+`Limit` nullity derivation | `FormalSystem/Semantics/Extension/Admissible.lean:285`–`319` |
| Lean: `lem:step`, sole `Spherical` application site | `FormalSystem/Semantics/Extension/Step.lean:10`–`43`, `129` |
| Lean: `thm:extension` / `cor:occurrence` chain and inputs | `FormalSystem/Semantics/Extension/Extension.lean:19`–`99` |

### 4.1 Verification provenance (re-checked 2026-08-31 for this audit)

Every row above was opened and its cited line(s) compared against the current tree, both
repositories. **Result: no drift.** All 21 rows resolve to exactly the cited symbol at exactly
the cited line(s), with one non-drift annotation recorded below.

**ModelChecker-side rows (11 of 11 confirmed unchanged):** `build_frame_constraints`
(`core.py:537`), `build_nullity_identity_constraint` (`core.py:280`), `build_converse_constraint`
(`core.py:305`), `build_forward_comp_constraint` (`core.py:344`), the disabled `task_restriction`
constraint and its soundness-analysis comment (`core.py:747`–`835`, confirmed as the exact span
from the `# 10. Task relation...` comment header through the constraint's closing `)`),
`capped_skolem_abundance_constraint` (`core.py:1447`), `depth_bounded_skolem_abundance_constraint`
(`core.py:1530`), `build_task_minimization_constraint` (`core.py:1628`), `is_valid_duration` /
`is_valid_time` (`core.py:242`, `core.py:862`), `ForAllTime` / `ExistsTime` (`core.py:396`,
`core.py:469`), `is_world` / `max_world_id` (`core.py:201`, `core.py:208`),
`NecessityOperator.true_at` / `false_at` (`operators.py:508`, `562`), `FutureOperator.true_at`
(`operators.py:691`), `PastOperator.true_at` (`operators.py:862`), `unit_tests` /
`test_example_range` (`examples.py:1422`, `1426`), `example_range` (`examples.py:1435`–`1478`,
closing brace confirmed at line 1478), and `KNOWN_TIMEOUT_EXAMPLES` / `UNSTABLE_EXAMPLES`
(`test_bimodal.py:44`–`95`). The `BM_TH_1`/`BM_TH_2` inline comments (`# Has countermodel`) were
independently confirmed at `examples.py:1473`–`1474` exactly as cited in Section 2.2's table.

**The re-run grep** (Section 1.2's negative claim that Seriality is asserted nowhere in
`semantic/`):
```
$ grep -rn "serial" code/src/model_checker/theory_lib/bimodal/semantic/
(no output — exit code 1)
```
Confirms the report's claim unchanged: no occurrence of "serial" (case-sensitive) anywhere in
`semantic/`, including comments.

**Lean-side rows (10 of 10 confirmed unchanged, one annotation):** `TaskFrame.lean:74`–`75`,
`108`–`109`, `466`–`469` (four-axiom list and `nullity_identity` design-question note); `Serial`
(`:377`), `Interpolates` (`:395`), `Spherical` (`:362`), `cone` (`:231`); `Constraint.lean:43`–`55`
(the three-input enumeration) and `:217`–`244` (`nonempty_fib_of_serial`,
`nonempty_seg_of_interpolates`); `Admissible.lean:285`–`319` (the "new time twice" case invoking
`TaskFrame.nullity_of_serial_limit F.serial F.limit u`, confirmed verbatim); `Step.lean:10`–`43`
(the sole-`Spherical`-site claim) and `:129` (`F.spherical (Constraints τ z) hdir ...`, confirmed);
`Extension.lean:44`–`58` (the two-input proof: Zorn plus `lem:step`) and `:97`–`99`
(`cor:occurrence`'s `TaskRel w 0 w` discharge by `TaskFrame.nullity_identity`, confirmed verbatim).

**Annotation, not drift**: `Extension.lean:19`–`21`'s printed chain now reads
`def:constraints → lem:constraint → lem:fibers (RETIRED anchor; see below) → lem:admissible →
lem:step → ...`, one node longer than Section 1.2's simplified inline diagram
(`def:constraints -> lem:constraint -> lem:admissible -> lem:step -> thm:extension -> cor:occurrence`).
The added node is a documentation artifact of a prior anchor rename/retirement in the Lean
source, not an additional proof obligation or a fourth axiom-consuming step — `lem:constraint`'s
three inputs (Section 1.2) and `lem:step`'s sole-`Spherical`-site status are both unchanged by it.
Section 1.2's diagram is accurate as a reader-facing summary and is left as-is; this note records
the fuller citation for a reader who opens the Lean file directly and finds the extra label.

## 5. Non-Goals Respected

No change was made to `core.py`, `operators.py`, or `examples.py` in the ModelChecker tree. The
abundance-removal experiment (Deliverable 2) ran entirely against an in-process monkeypatched
copy of `build_frame_constraints`, defined in the throwaway script under `baselines/`, never
written to the tracked source file. `task_restriction` was not enabled.
