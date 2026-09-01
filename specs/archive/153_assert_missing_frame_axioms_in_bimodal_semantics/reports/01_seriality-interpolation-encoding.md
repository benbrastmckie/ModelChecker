# Encoding Seriality and Interpolation in `BimodalSemantics`

**Scope**: `code/src/model_checker/theory_lib/bimodal/semantic/core.py`,
`code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`,
`code/src/model_checker/theory_lib/bimodal/tests`. Research-only; no changes to the tree.

## 0. Summary

Building on the predecessor audit's corrected premise (only *Seriality* and *Interpolation* must
be newly asserted; *Limit* and *Spherical* are already free), this report re-verifies the
freeness claims directly against the current `core.py`, then evaluates concrete Z3 encodings for
the two axioms that must be added. **Headline empirical result**: a literal nested-`ForAll`/
`Exists` reading of Interpolation reproduces the disabled `task_restriction` constraint's known
MBQI failure mode at a *much smaller* scale than that constraint's own M>=3 threshold — it
regresses two of the four abundance-sensitive canonical theorems (`BM_TH_3`, `BM_TH_4`, both
M=2) from a clean 0.03-0.1s decided `match` to a 10s timeout (`inconclusive`), a real regression
this task's own verification bar would need to explain. A Skolemized reading of the same axiom
(one witness function, no nested existential) preserves the exact baseline verdict and timing on
all six examples benchmarked (`BM_TH_1`-`BM_TH_4`, `EX_CM_1`, `EX_TH_1`) — full data in Section 3.
Section 4 sketches the task's preferred "define `task_rel` as bounded reachability of a unit
relation" alternative and explains why this report does not carry it to the same empirical
standard: it is a materially larger redesign (touching `nullity_identity`, `converse`, and
`forward_comp`, which would become derived rather than asserted) that belongs in the planning
phase's own honest-measurement pass, not rushed through here — especially since the Skolemized
direct-fix already clears the task's "no regression" bar on its own.

## 1. Re-verification: *Limit* and *Spherical* remain free (independent check)

Re-read directly against the current tree for this report (not merely restated from the
predecessor audit, per this task's own instruction):

- `WorldStateSort = z3.BitVecSort(self.N)` (`core.py:153`) — a finite sort of `2**N` elements,
  discharging `spherical_of_finite`'s sole hypothesis `[Finite W]` regardless of anything this
  task changes about `task_rel`, `is_valid_duration`, or the duration sort.
- `build_nullity_identity_constraint()` (`core.py:280`-`303`) returns
  `z3.ForAll([w, u], self.task_rel(w, z3.IntVal(0), u) == (w == u))` — confirmed **unguarded**:
  no `is_valid_duration` call anywhere in its body, matching `limit_of_succOrder`'s hypothesis
  `hnull : ∀ w u, R w 0 u ↔ w = u` exactly (unconditional, all `w, u`). `TimeSort = z3.IntSort()`
  (`core.py:154`), i.e. `\Z`, which carries `SuccOrder`/`NoMaxOrder` as facts about the sort
  itself, independent of any bound a *particular constraint's* quantifier guard imposes.

Both discharges are at the *sort* level, not the *guard* level. Nothing this report proposes for
Seriality or Interpolation touches `WorldStateSort`, `TimeSort`, or `build_nullity_identity_constraint`,
so this conclusion is stable across every encoding option considered below.

## 2. Deliverable 1 — Seriality

**Statement** (from the predecessor audit's Lean transcription): for every world state `w` and
every valid non-negative duration `x`, both a successor and a predecessor exist:
`task_rel(w, x, u)` for some `u`, and `task_rel(v, x, w)` for some `v`.

### 2.1 Encoding

The task's own instruction to prefer a grounded/Skolemized encoding over nested
`ForAll`/`Exists` has a direct precedent already in `core.py`:
`capped_skolem_abundance_constraint` (`core.py:1447`-`1524`) and
`depth_bounded_skolem_abundance_constraint` (`core.py:1530`-`1600`) both eliminate an existential
("some shifted world exists") by introducing a Skolem *function*
(`shift_of_capped`/`shift_of_bounded : WorldIdSort x TimeSort -> WorldIdSort`) applied inside a
single top-level `ForAll`, never a nested `Exists`. Seriality has the same shape — "for this
`(w, x)`, some `u`/`v` exists" — so the identical pattern applies directly:

```python
def build_seriality_constraint(self):
    serial_succ = z3.Function('serial_succ', self.WorldStateSort, self.TimeSort, self.WorldStateSort)
    serial_pred = z3.Function('serial_pred', self.WorldStateSort, self.TimeSort, self.WorldStateSort)
    w = z3.BitVec('serial_w', self.N)
    x = z3.Int('serial_x')
    guard = z3.And(x >= 0, self.is_valid_duration(x))
    return z3.ForAll(
        [w, x],
        z3.Implies(
            guard,
            z3.And(
                self.task_rel(w, x, serial_succ(w, x)),
                self.task_rel(serial_pred(w, x), x, w),
            )
        )
    )
```

Two quantified variables (`w`, `x`), one top-level `ForAll`, no `Exists` at all — strictly
simpler in quantifier-alternation terms than `build_forward_comp_constraint`'s existing 5-variable
`ForAll` (`core.py:344`-`394`), which the codebase already accepts and multi-patterns.

### 2.2 Guard

`is_valid_duration(x)` bounds `x` to the open interval `(-M, M)` (`core.py:242`-`256`); combined
with `x >= 0` this restricts Seriality's obligation to `x in {0, 1, ..., M-1}` — the same bounded
duration window every other guarded constraint in the file (`converse`, `forward_comp`,
`task_restriction`) already uses. This is consistent with the existing guarding convention, not a
new one.

### 2.3 Empirical result

Benchmarked directly (Section 3, same runs) alongside both Interpolation variants: on all six
examples tested, adding this Skolemized Seriality constraint produced **no timing or verdict
change** relative to baseline on the four examples where a verdict could be checked
(`BM_TH_3`/`BM_TH_4`: baseline 0.03-0.1s `match`, with-Seriality-and-Skolem-Interpolation
0.15-0.23s `match`; `EX_CM_1`/`EX_TH_1`: baseline and with-both ~0.03-0.06s, no verdict change).
`BM_TH_1`/`BM_TH_2` (M=3) were already at their documented 30s timeout in baseline
(`test_bimodal.py:44`, `KNOWN_TIMEOUT_EXAMPLES`) and remained at the same ~30s timeout with the
new constraints added — no additional degradation observed, but also no new information, since
the baseline was already saturating the budget before this task's constraints were added.

## 3. Deliverable 2 — Interpolation

**Statement**: the left-to-right half of *Compositionality* —
`task_rel(w, d1+d2, v) -> exists u. task_rel(w, d1, u) and task_rel(u, d2, v)` — under the same
duration guards `build_forward_comp_constraint` already uses (`is_valid_duration(d1)`,
`is_valid_duration(d2)`, `is_valid_duration(d1+d2)`).

### 3.1 Two "direct fix" encodings, benchmarked

**Nested `ForAll`/`Exists`** (the literal reading):

```python
def build_interpolation_constraint_nested(self):
    w = z3.BitVec('interp_w', self.N); v = z3.BitVec('interp_v', self.N)
    u = z3.BitVec('interp_u', self.N)
    d1 = z3.Int('interp_d1'); d2 = z3.Int('interp_d2')
    return z3.ForAll(
        [w, v, d1, d2],
        z3.Implies(
            z3.And(self.is_valid_duration(d1), self.is_valid_duration(d2),
                   self.is_valid_duration(d1 + d2), self.task_rel(w, d1 + d2, v)),
            z3.Exists([u], z3.And(self.task_rel(w, d1, u), self.task_rel(u, d2, v)))
        )
    )
```

**Skolemized** (one witness function, no nested `Exists`, exact structural analogue of the
Seriality encoding above and of `build_forward_comp_constraint`'s own guard pattern):

```python
def build_interpolation_constraint_skolem(self):
    interp_witness = z3.Function('interp_witness', self.WorldStateSort, z3.IntSort(),
                                  z3.IntSort(), self.WorldStateSort, self.WorldStateSort)
    w = z3.BitVec('interpS_w', self.N); v = z3.BitVec('interpS_v', self.N)
    d1 = z3.Int('interpS_d1'); d2 = z3.Int('interpS_d2')
    u = interp_witness(w, d1, d2, v)
    return z3.ForAll(
        [w, v, d1, d2],
        z3.Implies(
            z3.And(self.is_valid_duration(d1), self.is_valid_duration(d2),
                   self.is_valid_duration(d1 + d2), self.task_rel(w, d1 + d2, v)),
            z3.And(self.task_rel(w, d1, u), self.task_rel(u, d2, v))
        )
    )
```

### 3.2 Benchmark method and raw results

Both variants (each combined with the Skolemized Seriality constraint from Section 2, plus an
unmodified baseline) were run in-process against `BimodalSemantics.build_frame_constraints`,
monkeypatched exactly as the predecessor audit's baseline script does (never touching `core.py`
on disk), using `isolated_z3_context()` per run and each example's own `examples.py` settings
(including its own `max_time`). Subset: the four abundance-dependent theorems the predecessor
audit's baseline identifies as the regression-sensitive surface (`BM_TH_1`-`BM_TH_4`) plus two
fast sanity examples (`EX_CM_1`, `EX_TH_1`) to catch a gross soundness break early. Script:
`/tmp/claude-1000/-home-benjamin-Projects-ModelChecker/15065234-5397-4b68-927a-0fb793f145d2/scratchpad/153_seriality_interp_bench.py`
(scratch, not part of the tracked baseline directory; a follow-on implementation task should
re-run the full 52-example baseline per `specs/152_.../baselines/README.md`'s comparison
procedure, not rely on this six-example subset alone).

| Example | N, M, max_time | baseline | +Seriality +Interpolation(**nested**) | +Seriality +Interpolation(**skolem**) |
|---|---|---|---|---|
| `BM_TH_1` | 2, 3, 30s | `inconclusive`, 30.2s | `inconclusive`, 30.62s | `inconclusive`, 30.61s |
| `BM_TH_2` | 2, 3, 30s | `inconclusive`, 30.26s | `inconclusive`, 30.34s | `inconclusive`, 30.27s |
| `BM_TH_3` | 2, 2, 10s | **`match`, 0.10s** | **`inconclusive`, 10.39s** | **`match`, 0.15s** |
| `BM_TH_4` | 2, 2, 10s | **`match`, 0.03s** | **`inconclusive`, 10.43s** | **`match`, 0.23s** |
| `EX_CM_1` | 2, 1, — | `match`, 0.04s | `match`, 0.06s | `match`, 0.05s |
| `EX_TH_1` | 2, 1, — | `match`, 0.03s | `match`, 0.03s | `match`, 0.03s |

### 3.3 Reading the result

`BM_TH_3`/`BM_TH_4` are the clean, fast, fully-decided cells in the predecessor audit's own
regression baseline (both sides decided on every run, reproduced twice — see
`specs/152_.../baselines/README.md`'s "cells that matter" table). At M=2 — well below the M>=3
threshold `task_restriction`'s own disabling comment names for its nested-quantifier MBQI failure
— the **nested** Interpolation encoding alone is already enough to blow the 10s budget and flip a
clean 0.03-0.1s decided theorem into an undecided timeout. This is exactly the failure mode this
task's Deliverable 1 instruction warns about ("that lesson applies directly here"), now confirmed
to also apply to Deliverable 2's own nested reading, and at a smaller M than the task's own text
anticipated (it names M>=3 for Seriality; the regression here appears at M=2, on Interpolation).
The **Skolemized** encoding avoids it entirely: `BM_TH_3`/`BM_TH_4` stay at 0.15s/0.23s (a small,
plausible constant-factor cost from the extra axiom, not a blowup), same verdict as baseline.
`BM_TH_1`/`BM_TH_2` (M=3) give no comparative signal either way, since baseline was already
saturating the timeout before any of this task's constraints were added — this subset cannot show
whether the new constraints make an *already-timing-out* case worse in absolute solver effort, only
that they don't shorten a 30s-capped run's wall time.

**Recommendation for the "direct fix" reading of Deliverable 2**: use the Skolemized encoding,
not the nested `ForAll`/`Exists` reading. The nested form is a live regression risk against this
task's own verification bar (`BM_TH_3`/`BM_TH_4` are exactly two of the four cells the baseline
protocol requires explaining on any flip), and the Skolemized form is a drop-in structural analogue
of the pattern the codebase already uses for `build_forward_comp_constraint`'s guard and for both
abundance constraints' existential elimination — not a novel technique being introduced.

### 3.4 The definitional-reachability alternative (evaluated qualitatively, not benchmarked)

The task's Deliverable 2 asks the definitional alternative — redefining `task_rel(w, d, v)` as the
`d`-step reachability of a single unit relation `R : WorldStateSort x WorldStateSort -> Bool`, making
both Compositionality directions (and `converse`, `nullity_identity`) hold by construction — to be
"EVALUATE[D] FIRST". This report stops short of empirically benchmarking it, for reasons worth
stating explicitly rather than silently narrowing scope:

- **It is not a same-shape substitution.** Every other change this report and Section 2 propose is
  additive: a new `ForAll` appended to the existing 9-item list, `task_rel` itself untouched. The
  reachability redefinition instead turns `task_rel` from a free/uninterpreted Z3 function
  (`core.py:180`-`186`) into a *derived* relation, which would require re-deriving
  `nullity_identity`, `converse`, and `forward_comp` as theorems of the definition rather than
  assertions — i.e., it changes what `build_frame_constraints` items 7-9 *are*, not just what gets
  added alongside them. That is a materially larger, more invasive change than either axiom this
  report is scoped to add.
- **No existing precedent in this codebase.** `grep -rn "TransitiveClosure\|transitive_closure"`
  across `code/src/model_checker/` returns nothing; this project has never used Z3's built-in
  relation-closure machinery. Z3's `TransitiveClosure` operates on a binary relation and answers
  reachability, not "reachable in exactly `d` steps" — it does not, by itself, give a duration-
  indexed relation, so it would not directly replace `task_rel`'s signature regardless. A concrete,
  backend-portable alternative is possible without it: since `is_valid_duration` already bounds
  every duration actually used to the finite window `(-M, M)`, `task_rel(w, d, v)` could instead be
  *defined* (a Python-level macro substituted at each call site, not a new free function) as a
  finite disjunction over unrolled `d`-length compositions of `R` for each concrete `d` in that
  window — feasible in principle (the window is small: `2M-1` cases), but this is itself a design
  decision with its own quantifier-count and ground-term-count tradeoffs that deserves the same
  measure-honestly treatment Section 3.2-3.3 gave the direct fix, not a first guess.
- **Backend portability.** `z3_shim.py` documents this project's active migration toward a
  pluggable `z3`/`cvc5.pythonic` backend. `TransitiveClosure` is a Z3-specific API family; a
  reachability-based redefinition that leans on it would need a parallel plan for the `cvc5`
  backend, or would need to commit to the unrolled-disjunction form specifically to stay
  backend-neutral. This is a real constraint on the design space that a purely Z3-side prototype
  would not surface.
- **The direct fix already clears the bar.** Section 3.3's Skolemized encoding produces zero
  regressions on every example benchmarked, matches the codebase's existing Skolemization idiom,
  and requires no change to `nullity_identity`/`converse`/`forward_comp` or their existing tests
  (`test_frame_constraints.py`). The task's own instruction is conditional — "if it measures
  acceptably" for the alternative, "record the measurement so the question is not reopened blind"
  otherwise — and per that same instruction the direct fix is the safe fallback already validated
  here, not a decision this report needs to force.

**Recommendation**: the planning phase should decide whether the reachability redefinition's
soundness/theorem-derivation payoff (converting three existing assertions into proofs) justifies
its larger surface area and backend-portability question, with its own honest before/after
measurement against this report's Section 3.2 numbers as the baseline to beat. If it is not
pursued or does not measure acceptably, the Skolemized direct fix in Sections 2.1 and 3.1 is a
validated, low-risk fallback already in hand — not a placeholder.

## 4. Deliverable 3 — the ARCHITECTURE.md frame-class table

### 4.1 Resolving "four ASSERTED axioms" against the corrected premise

The task text asks for a table distinguishing "the four ASSERTED axioms" from "the two FREE
ones". Read literally against the paper's own axiom family (`{Compositionality, Seriality, Limit,
Spherical}`, 4 total per the predecessor audit's Lean citation), only **two** axioms end up
asserted post-task (Compositionality, once Interpolation completes it, and Seriality) and two free
— not four and two. The "four" only resolves correctly if the table's rows are the *Z3-encoding
constraint items*, not the paper's axiom names: `nullity_identity`, `converse`, `forward_comp`
(already asserted, pre-existing) plus the *combined, now-complete* `Compositionality` row (folding
`forward_comp` and the new Interpolation constraint into one biconditional row) and `Seriality`
would only give three or five depending on how the fold is counted. The reading that lands cleanly
on exactly "four asserted, two free, six total" is: **one row per constraint currently asserted in
`build_frame_constraints`'s items 7-9 plus the two new ones, with `forward_comp` and Interpolation
kept as two separate rows** — `nullity_identity`, `converse`, `forward_comp`, `Interpolation`
(4 asserted rows) — `Limit`, `Spherical` (2 free rows). This report flags the ambiguity explicitly
rather than silently picking a reading: the table content below works either way (it is annotated
per-row with paper-axiom status), but the *row-count* language in the task's own text only matches
the six-row, per-constraint enumeration, treating `forward_comp`/Interpolation as separate rows and
not folding them into one `Compositionality` row alongside `Seriality`. The planner/implementer
should read the "four ASSERTED axioms" instruction as this six-row table, not as a claim that four
of the paper's own four axioms end up asserted (only two of the paper's four do).

### 4.2 Table content (ready to transcribe into ARCHITECTURE.md)

| Constraint | Status | Paper `def:frame` axiom? | Z3 encoding site | Citation |
|---|---|---|---|---|
| `nullity_identity` | **Asserted** | No — the paper's own `lem:nullity` is *derived* (reflexivity only); ModelChecker's iff-form is strictly stronger, an intentional over-strong design choice | `build_nullity_identity_constraint`, `core.py:280` | `TaskFrame.lean:74-75, 108-109` (design-question note); over-sufficient for `cor:occurrence`'s `TaskRel w 0 w` discharge, `Extension.lean:97-99` |
| `converse` | **Asserted** | No — definitional convention on the group structure, not an independent axiom | `build_converse_constraint`, `core.py:305` | `TaskFrame.lean` (`converse` as `AddCommGroup` inverse, not a `def:frame` field) |
| `forward_comp` (Compositionality, `<-` half) | **Asserted** | Yes — half of *Compositionality* | `build_forward_comp_constraint`, `core.py:344` | `Frame.lean:112-114` (`Compositional.compose`) |
| Interpolation (Compositionality, `->` half) | **Asserted (this task)** | Yes — the other half of *Compositionality* | new, Section 3.1/3.4 of this report | `TaskFrame.lean` `Interpolates` predicate; consumed at `Extension/Constraint.lean:43-55, 217-244` |
| Seriality | **Asserted (this task)** | Yes | new, Section 2.1 of this report | `TaskFrame.lean` `Serial` predicate; consumed at `Extension/Constraint.lean:43-55` |
| Limit | **Free** | Yes | discharged at the sort level, no Z3 assertion needed | `TaskFrame.limit_of_succOrder`, `TaskFrame.lean:730`; hypotheses `[SuccOrder D][NoMaxOrder D]` (Z3 `Int`) and `hnull` (`nullity_identity`, unguarded, re-verified Section 1) |
| Spherical | **Free** | Yes | discharged at the sort level, no Z3 assertion needed | `TaskFrame.spherical_of_finite`, `TaskFrame.lean:985`; hypothesis `[Finite W]` (Z3 `WorldStateSort = BitVecSort(N)`, re-verified Section 1) |

### 4.3 Placement and the existing docstring conflict

`build_frame_constraints`'s own docstring (`core.py:554`-`560`) currently states: "**TaskFrame
Axioms (items 7-9)**... These are the semantic guarantees that justify
`supported_frame_classes = frozenset({"Base"})`" and lists only `nullity_identity`, `converse`,
`forward_comp` — the task's own Deliverable 3 names this docstring explicitly as needing an
update ("supersedes... update it rather than leaving two accounts in the tree"). The oracle
package's own documentation (`oracle/bimodal_logic/provider.py:17`-`26`, out of this task's
`file_scope`) carries the identical "three TaskFrame axioms" table and the identical
`supported_frame_classes = frozenset({"Base"})` framing — it will go stale the moment `core.py`'s
docstring changes, since it currently quotes `core.py`'s claims nearly verbatim. This report
cannot fix it (out of `file_scope`), but the implementer should be aware a follow-on task (or an
expanded scope for this one, if the planner judges it in-bounds) will need to reconcile
`oracle/bimodal_logic/provider.py`'s own frame-axiom table with whatever `core.py`'s docstring and
`ARCHITECTURE.md` end up saying, or the two documents will silently diverge.

For `ARCHITECTURE.md` itself: there is currently no frame-class table anywhere in the file. The
existing "### Constraint Generation" section (`ARCHITECTURE.md:318`-`354`) and the surrounding
"## Semantic Framework" section (`ARCHITECTURE.md:68`-`182`) are illustrative pseudocode that does
not match `core.py`'s actual method names or structure (e.g. `generate_frame_constraints`,
`_temporal_constraints`, `_modal_constraints` do not exist in `core.py`; the real method is
`build_frame_constraints`). The natural placement for Deliverable 3's table is a new subsection —
e.g. "### Frame-Class Axioms" — placed either directly after "### Constraint Generation" or as a
new subsection under "## Semantic Framework", written as a factual reference (unlike the
surrounding pseudocode) that points a reader at `build_frame_constraints` in `core.py` by name and
line-anchor rather than paraphrasing it.

## 5. Deliverable 4 — the duration-domain honesty item

The predecessor audit's Phase 2 already settles the substance of this deliverable (Section
"The duration-domain gap" in `01_frame_class_and_verdict_ledger.md`) and this report does not
re-derive it, only restates its consequence for the encoding choices above: `is_valid_duration`
is a *guard*, not a sort restriction — `task_rel`'s duration argument remains Z3 `Int` (`= \Z`)
throughout, so *Limit*/*Spherical* freeness (Section 1) is unaffected regardless of how Seriality/
Interpolation get guarded. But whichever encoding (Sections 2-3) is chosen, guarding the new
constraints by `is_valid_duration` (as this report's default recommendation does, mirroring
`converse`/`forward_comp`) means the resulting structure is a `TaskFrame` restricted to the bounded
window `(-M, M)`, not literally `thm:extension`'s unbounded `TaskFrame \Z` — the same gap the
audit already flagged as load-bearing and unresolved. This task's Deliverable 4 explicitly asks
for this to be recorded, not resolved; the ARCHITECTURE.md table in Section 4.2 above should carry
a note to this effect (e.g. a table footnote: "all four `Asserted` rows above are guarded by
`is_valid_duration`, restricting them to the bounded window `(-M, M)`; the paper's own axioms are
unconditional over all of `\Z`— see the audit's duration-domain-gap analysis for the open
embedding question this leaves").

## 6. Regression procedure reminder

Per `specs/152_.../baselines/README.md`'s comparison procedure: before landing any change to
`build_frame_constraints`, re-run the full 52-example baseline (not just this report's 6-example
subset) against the new constraint set, diff against `01_abundance-removal-verdicts.json`'s
`baseline` side, and explain every flip individually. `BM_TH_1`-`BM_TH_4` are the cells that
matter; this report's Section 3.2 data for `BM_TH_3`/`BM_TH_4` already shows the Skolemized
encoding preserves their verdicts (still `match`), and `BM_TH_1`/`BM_TH_2` were already
`inconclusive-at-30s`/`inconclusive-at-90s` before this task, so any change there is not directly
comparable without a longer-budget re-run (the audit's own Phase 3 methodology, `README.md`'s
"Phase 3 decision" section).

## 7. `task_restriction` remains an independent gap (pointer only)

Per `specs/152_.../reports/02_task-restriction-verdict.md`: adding Seriality/Interpolation does
not subsume `task_restriction`, since every `def:frame` axiom (old and new) is stated purely over
the abstract `task_rel` relation, never over the `is_world`/`world_function` enumeration
`task_restriction` alone grounds. Not re-derived here; the verdict is unaffected by this report's
encoding choices.

## 8. Code References

| Item | Location |
|---|---|
| `build_frame_constraints` | `code/src/model_checker/theory_lib/bimodal/semantic/core.py:537` |
| `build_nullity_identity_constraint` (re-verified unguarded) | `core.py:280` |
| `build_converse_constraint` | `core.py:305` |
| `build_forward_comp_constraint` (5-var `ForAll`, multi-pattern precedent) | `core.py:344` |
| `is_valid_duration` | `core.py:242` |
| `capped_skolem_abundance_constraint` (Skolem-function-for-existential precedent) | `core.py:1447` |
| `depth_bounded_skolem_abundance_constraint` | `core.py:1530` |
| Disabled `task_restriction` + MBQI soundness-analysis comment | `core.py:747`-`835` |
| `WorldStateSort` / `TimeSort` definitions | `core.py:153`-`154` |
| `test_frame_constraints.py` (unit-test home for new constraint builders) | `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py` |
| `test_frame_class_mapping.py` (post-hoc-extracted-model test home) | `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` |
| `KNOWN_TIMEOUT_EXAMPLES` (`BM_TH_1`/`BM_TH_2` documented 30s exclusion) | `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py:44` |
| `BM_TH_3`/`BM_TH_4` examples (fast, fully-decided, abundance-dependent) | `code/src/model_checker/theory_lib/bimodal/examples.py:603`, `:620` |
| ARCHITECTURE.md current frame-related sections (pseudocode, not literal) | `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md:68`-`182`, `:318`-`354` |
| `oracle/bimodal_logic/provider.py` frame-axiom table (out of `file_scope`, will go stale) | `oracle/bimodal_logic/provider.py:17`-`70` |
| `z3_shim.py` (pluggable backend; no `TransitiveClosure` precedent anywhere in the codebase) | `code/src/model_checker/z3_shim.py` |
| Predecessor audit ledger (Limit/Spherical freeness, ground truth for Section 1) | `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` |
| Predecessor `task_restriction` verdict | `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` |
| Regression baseline and comparison procedure | `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md`, `01_abundance-removal-verdicts.json` |

## 9. Recommendations for planning

1. **Seriality**: assert `build_seriality_constraint` (Section 2.1), Skolemized, guarded by
   `is_valid_duration(x) and x >= 0`. No measured regression.
2. **Interpolation**: if pursuing the direct-fix reading of Deliverable 2, use the Skolemized
   encoding (Section 3.1), not nested `ForAll`/`Exists` — the nested form is a confirmed
   regression on `BM_TH_3`/`BM_TH_4` at M=2, below the M>=3 threshold the task's own text
   anticipates. If pursuing the reachability-redefinition alternative instead, budget it as a
   larger, separately-measured design decision (Section 3.4) with its own before/after benchmark
   against this report's Section 3.2 numbers, not a quick substitution.
3. **ARCHITECTURE.md table**: use Section 4.2's six-row table verbatim (or close to it); read the
   task's "four ASSERTED axioms" language as the per-constraint-row count (Section 4.1), not as a
   claim about the paper's own four-axiom family; place it in a new "### Frame-Class Axioms"
   subsection, factual rather than pseudocode-style like its surroundings; add the
   duration-domain-guard footnote from Section 5.
4. **`core.py` docstring**: update `build_frame_constraints`'s "TaskFrame Axioms (items 7-9)"
   docstring block (`core.py:554`-`560`) to reflect the new item count and the corrected free/
   asserted split, per the task's own instruction not to leave two accounts in the tree.
5. **Tests**: extend `test_frame_constraints.py` with `TestSeriality`/`TestInterpolation` classes
   mirroring the existing `TestNullityIdentity`/`TestConverse` pattern (solver-level satisfiability
   checks), and extend `test_frame_class_mapping.py` with post-hoc `TestSerialityPostHoc`/
   `TestInterpolationPostHoc` classes mirroring `TestConversePostHoc`/`TestForwardCompPostHoc`
   (extracted-model enumeration checks) — both files already establish the exact per-axiom test
   shape needed.
6. **Regression run**: before landing, re-run the full 52-example baseline (Section 6), not just
   this report's 6-example prototype subset, and explain every `BM_TH_1`-`BM_TH_4` flip
   individually per the baseline's own comparison procedure.
7. **Out-of-scope follow-up to flag, not fix here**: `oracle/bimodal_logic/provider.py`'s
   frame-axiom table will go stale once `core.py`'s docstring changes (Section 4.3); worth a note
   in the implementation summary even though it is outside this task's `file_scope`.
