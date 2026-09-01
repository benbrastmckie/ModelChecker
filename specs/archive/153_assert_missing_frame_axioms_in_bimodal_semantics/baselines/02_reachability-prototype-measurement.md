# Phase 2 Measurement: Definitional-Reachability Alternative for `task_rel`

**Time-box**: 1.5h hard box (per plan). Actual time spent on the measurement itself (prototype
authoring, debugging, and the six-example run): well within the box. `core.py` on disk is
unmodified (`git status --short` on `core.py`: clean) -- the prototype lives entirely in
`02_reachability_prototype_script.py`, a process-local `ReachabilitySemantics(BimodalSemantics)`
subclass that monkeypatches `self.task_rel` after `define_primitives()` runs.

## What was measured (and what was not)

`self.task_rel` is called only as `self.task_rel(w, d, v)` throughout
`code/src/model_checker/theory_lib/bimodal/` (verified: no bare `FuncDeclRef` reference to
`task_rel` anywhere else in the package) -- so it is transparent to monkeypatch it to a plain
Python closure that returns a Z3 formula instead of leaving it a free `z3.Function`. The closure
implements the plan's unrolled-disjunction form: for each concrete `d` in the bounded window
`(-(M-1), M-1)` -- `2M-1` cases -- a chain of `d` applications of a single free relation
`R : WorldStateSort x WorldStateSort -> Bool`, with intermediate chain nodes given by per-`(w,v)`
Skolem functions (`chain_{k}_{i}`), never a nested `Exists`. Negative `d` is defined as the
reversed chain. `z3.TransitiveClosure` is not used, per the report's independent ruling-out
(no in-tree precedent; answers reachability, not reachability-in-exactly-`d`-steps; Z3-specific
against `z3_shim.py`'s `cvc5.pythonic` migration).

**Important scope caveat, stated explicitly rather than left implicit**: this prototype measures
only the *performance* of substituting the reachability macro for `task_rel` while **keeping
`nullity_identity`, `converse`, and `forward_comp` asserted exactly as today**, now stated over the
macro-expanded relation. It does **not** attempt to re-derive those three as *theorems* of the
reachability definition (dropping their explicit assertions), which is the actual soundness payoff
the report's Section 3.4 and the task's own preference describe. Deriving compositionality as a
theorem from independent per-pair Skolem witnesses is not automatic -- nothing forces a `d1+d2`
chain's witness nodes to coincide with a `d1`-chain's and a `d2`-chain's witnesses -- and making it
so would need either a properly quantified transitive-relation construction (risking exactly the
nested-quantifier blowup this task exists to avoid) or a materially more careful shared-witness
design. That harder half of the redesign was not measured here; the time-box was spent honestly on
the narrower, well-defined question the plan's own macro description asks for.

## Prototype adjustment required to run at all

`build_forward_comp_constraint`'s existing `z3.MultiPattern(self.task_rel(w, d1, v),
self.task_rel(v, d2, u))` hint fails once `task_rel(...)` expands to an `Or`/`And` compound formula
-- Z3 rejects `And`/`Or` as pattern terms ("invalid pattern"). The prototype's
`ReachabilitySemantics` overrides `build_forward_comp_constraint` to drop the explicit pattern
(falling back to Z3's automatic pattern selection). This is itself a data point: the reachability
redefinition is incompatible with the existing hand-tuned multi-pattern without further rework, a
real (if minor) integration cost the "go" reading below does not erase.

## Results (six-example subset, same subset the report's Section 3.2 used)

| Example | N, M, max_time | baseline | reachability (macro'd task_rel) |
|---|---|---|---|
| `BM_TH_1` | 2, 3, 30s | `inconclusive`, 30.16s | `inconclusive`, 30.17s (timeout) |
| `BM_TH_2` | 2, 3, 30s | `inconclusive`, 30.19s | `inconclusive`, 30.19s (timeout) |
| `BM_TH_3` | 2, 2, 10s | **`match`, 0.11s** | **`match`, 0.05s** |
| `BM_TH_4` | 2, 2, 10s | **`match`, 0.04s** | **`match`, 0.05s** |
| `EX_CM_1` | 2, 1, — | `match`, 0.05s | `match`, 0.03s |
| `EX_TH_1` | 2, 1, — | `match`, 0.03s | `match`, 0.03s |

`EX_CM_1` carries the same benign `truth_value_at() missing 'eval_time'` interpretation error in
*both* arms (confirmed against `01_pre-change-verdicts.json`'s `EX_CM_1` entry, which shows the
identical error string) -- this is the pre-existing, out-of-scope interpretation-only error the
plan's Non-Goals section already documents ("present on every recorded baseline run... does not
affect any verdict"), not something introduced by this prototype.

## Go/no-go determination

Applying the plan's three stated criteria to the **narrow, measured scope** (macro'd `task_rel`,
axioms kept as assertions):

- (a) `BM_TH_3`/`BM_TH_4` still decided `match`: **met** (0.05s/0.05s, both `match`).
- (b) wall times within roughly the same order as the Skolemized encoding's 0.15s/0.23s: **met**
  (0.05s/0.05s -- same order, no blowup).
- (c) expressible without Z3-specific API: **met**, at the cost of dropping one existing
  hand-tuned `MultiPattern` hint (recorded above, not a Z3-specific-API violation but a real
  integration cost).

**Outcome: go, on the narrow question the macro description asks for -- but this measured scope
does not cover the redesign's actual soundness payoff** (deriving `nullity_identity`/`converse`/
`forward_comp` as theorems rather than assertions), which was not attempted in this time-box and
remains unmeasured. Per this plan's scope call, a "go" here does **not** expand this task: Phases
3-7 proceed against the Skolemized direct-fix encoding regardless. **This measurement, together
with its scope caveat, should be handed to a follow-on task if the reachability redesign is
pursued** -- that follow-on would need to additionally measure the theorem-derivation half before
any implementation decision, not just the macro-substitution performance measured here.

## Artifacts

- `02_reachability_prototype_script.py` -- the prototype (process-local; `core.py` untouched).
- `02_reachability-prototype-raw.json` -- raw per-example JSON written incrementally by the script.
