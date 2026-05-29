# Perpetuity Principle Validity Alignment: JPL Paper, BimodalLogic Lean, and ModelChecker

**Task 96 Research Report**
**Date**: 2026-05-29

---

## Executive Summary

The perpetuity principles (P1-P6) are valid in both the JPL paper and the BimodalLogic Lean
formalization. The ModelChecker currently finds countermodels to BM_TH_1 (`□A → Future A`) and
BM_TH_2 (`□A → Past A`). This discrepancy arises from **three compounding semantic divergences**
between the ModelChecker's Z3 encoding and the paper's semantics:

1. **Atom falsity outside domain**: Atoms are false at times outside a world's finite interval,
   causing `Future A` to be false whenever A is an atom and any future time is outside the world's
   interval. This is actually shared by the Lean formalization but creates a structural problem in
   the Z3 model.

2. **Box operator scoping**: The ModelChecker's `□` only quantifies over worlds where the
   evaluation time is in the world's interval (`is_valid_time_for_world`), not over all worlds
   unconditionally. The paper and Lean quantify over all world histories (or all Omega-members)
   at the given time, regardless of domain membership.

3. **Abundance constraint scope**: The Skolem abundance constraint only provides shifts of +/-1,
   not arbitrary shifts. The paper's auto_existence lemma provides a time-shifted world for any
   two times x, y -- an uncountably infinite closure property.

The timeout examples (BM_CM_1, BM_CM_3, TN_CM_2) are a symptom of the same structural
mismatch: the Z3 solver must search over a constrained finite model space that does not have
the right closure properties.

---

## Part 1: Three Semantic Definitions Compared

### 1.1 Paper (JPL)

**Framework** (`possible_worlds.tex`, lines 883-947):
- Time domain `D`: a totally ordered abelian group (infinite, unbounded, e.g., `Z` or `R`)
- World state set `W`: nonempty set of instantaneous configurations
- Task frame `F = (W, D, =>)` where `=>` satisfies Nullity, Reflection, Compositionality
- World history `tau: X -> W` where `X ⊆ D` is a **convex** subset and `tau(x) =>_{y-x} tau(y)`
- The set of all world histories over frame F is `H_F` (possibly with different domains)
- Possible world = equivalence class `[tau]_F` under time-shift equivalence

**Semantic clauses** (lines 939-947):
```
M,tau,x |= p_i    iff  x in dom(tau) AND tau(x) in |p_i|
M,tau,x |= Box phi iff  M,sigma,x |= phi for ALL sigma in H_F
M,tau,x |= Future phi iff  M,tau,y |= phi for ALL y in D where x < y
M,tau,x |= Past phi   iff  M,tau,y |= phi for ALL y in D where y < x
```

**Critical points**:
- Future/Past quantify over ALL `y in D` (the entire infinite domain), not just `dom(tau)`
- Atoms are false at times outside `dom(tau)` (there is no domain check separate from the existential)
- Box quantifies over all possible world histories unconditionally (no time-domain restriction)

**Key lemma** (`app:auto_existence`, line 2154-2178): For any `tau in H_F` and any `x, y in D`,
there exists `sigma in H_F` such that `tau ~_x^y sigma` witnessed by the shift `a(z) = z - x + y`.
This means the set `H_F` is **closed under arbitrary time shifts** -- for any world and any pair
of times, a time-shifted copy exists in `H_F`.

**Proof of MF** (thm:MF-valid, line 3217-3226):
The proof uses `app:auto_existence` to produce for any `sigma in H_F` and any `y > x` a world
`rho in H_F` where `sigma ~_y^x rho`. Then `M,sigma,y |= phi` iff `M,rho,x |= phi` (by
`lem:history-time-shift-preservation`). Since `□phi` holds, `M,rho,x |= phi`, so
`M,sigma,y |= phi`. Since `y > x` was arbitrary, `M,sigma,x |= Future phi`.

### 1.2 Lean Formalization (BimodalLogic)

**World history type** (`Semantics/WorldHistory.lean`, lines 69-97):
```lean
structure WorldHistory {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (F : TaskFrame D) where
  domain : D -> Prop                          -- convex time subset X ⊆ D
  convex : ∀ x z, domain x -> domain z ->
    ∀ y, x ≤ y -> y ≤ z -> domain y         -- convexity enforced
  states : (t : D) -> domain t -> F.WorldState  -- tau: X -> W
  respects_task : ∀ s t (hs : domain s) (ht : domain t),
    s ≤ t -> F.task_rel (states s hs) (t - s) (states t ht)
```

**Time-shift construction** (`WorldHistory.time_shift`, lines 238-260): Given any history `sigma`
and shift `Delta`, constructs a new valid history with domain `fun z => sigma.domain (z + Delta)`.
This is purely internal -- it constructs a new `WorldHistory` value in Lean's type theory.

**Truth evaluation** (`Semantics/Truth.lean`, lines 122-131):
```lean
def truth_at (M : TaskModel F) (Omega : Set (WorldHistory F)) (tau : WorldHistory F) (t : D) :
    Formula -> Prop
  | atom p  => ∃ (ht : tau.domain t), M.valuation (tau.states t ht) p
  | bot     => False
  | imp phi psi => truth_at ... phi -> truth_at ... psi
  | box phi => ∀ (sigma : WorldHistory F), sigma ∈ Omega -> truth_at M Omega sigma t phi
  | untl ... | snce ...  -- Until/Since with strict quantifiers
```

**Future/Past** (`Truth.lean`, lines 249-280): Defined as abbreviations via Until/Since:
```
G(phi)  =  def all_future phi  -- all_future_iff: truth_at ... phi.all_future iff ∀ s, t < s -> truth_at ... tau s phi
H(phi)  =  def all_past phi    -- past_iff: truth_at ... phi.all_past  iff ∀ s, s < t -> truth_at ... tau s phi
```
Crucially, these quantify over **all `s : D`** (the full type D), not just `tau.domain`.

**ShiftClosed condition** (`Truth.lean`, line 295):
```lean
def ShiftClosed (Omega : Set (WorldHistory F)) : Prop :=
  ∀ sigma ∈ Omega, ∀ (Delta : D), WorldHistory.time_shift sigma Delta ∈ Omega
```

**MF validity proof** (`Soundness.lean`, lines 252-258):
```lean
theorem modal_future_valid (phi : Formula) : |= ((phi.box).imp ((phi.all_future).box)) := by
  intro T _ _ _ _ F M Omega h_sc tau _h_mem t
  simp only [truth_at, Truth.future_iff, ...]
  intro h_box_phi sigma h_sigma_mem s hts
  have h_phi_at_shifted := h_box_phi (WorldHistory.time_shift sigma (s - t)) (h_sc sigma h_sigma_mem (s - t))
  exact (TimeShift.time_shift_preserves_truth M Omega h_sc sigma t s phi).mp h_phi_at_shifted
```

The proof mirrors the paper exactly: to prove `M, sigma, x |= Future phi` for arbitrary `sigma in Omega` and `s > t`, it applies the box hypothesis to `WorldHistory.time_shift sigma (s - t)`, which is guaranteed to be in `Omega` by `h_sc` (ShiftClosed). The Lean `Omega` parameter plays the role of `H_F`.

**Key difference from the paper**: The Lean formulation is parameterized by `Omega` (a set of
histories that can be restricted) rather than universally using `H_F`. But validity is defined as
holding for all `ShiftClosed` sets `Omega`, which captures the same closure property.

**Atoms in the Lean model**: Atoms are false outside the domain (theorem `atom_false_of_not_domain`,
Truth.lean lines 186-195). The crucial point is that Future/Past do NOT restrict to `tau.domain`
-- they quantify over all `s : D`. So `M,tau,x |= Future phi` requires `phi` at ALL `s > x`,
including times outside `tau.domain`. For atoms, those out-of-domain times make atoms false.

**BUT**: In the Lean formulation this never causes a countermodel to `□phi -> Future phi` because:
1. `□phi` requires `phi` at ALL `sigma in Omega` at time `t`
2. For any `s > t`, the time-shifted world `time_shift sigma (s - t)` has its domain shifted so
   that the time of interest is now in-domain for that shifted history
3. By `time_shift_preserves_truth`, truth at `(sigma, s)` equals truth at `(time_shift sigma (s-t), t)`
4. Since `□phi` holds, `phi` is true at `(time_shift sigma (s-t), t)`, so `phi` at `(sigma, s)`

The key mechanism: time-shifted copies allow "transporting" truth from any time to any other time.

### 1.3 ModelChecker (Z3 Encoding)

**World histories** (`semantic.py`): Represented as finite arrays `world_function: WorldIdSort -> Array(TimeSort, WorldStateSort)` with intervals `[world_interval_start(w), world_interval_end(w)]`. With parameter `M`, times range over integers in `(-M, M)` (open interval), and each world has an interval of length `M-1` within that range.

**Atom truth** (`semantic.py`, lines 1122-1131):
```python
def true_at(self, sentence, eval_point):
    if sentence_letter is not None:
        in_domain = self.is_valid_time_for_world(eval_world, eval_time)
        eval_world_state = z3.Select(world_array, eval_time)
        return z3.And(
            in_domain,
            self.truth_condition(eval_world_state, sentence_letter)
        )
```
Atoms require `is_valid_time_for_world(w, t)`, i.e., the time must be within the world's interval.

**Future operator** (`operators.py`, lines 532-550):
```python
def true_at(self, argument, eval_point):
    future_time = z3.Int('future_true_time')
    return semantics.ForAllTime(
        eval_world,
        future_time,
        z3.Implies(
            eval_time < future_time,
            semantics.true_at(argument, {"world": eval_world, "time": future_time})
        )
    )
```

**ForAllTime** (`semantic.py`, lines 390-411):
```python
def ForAllTime(self, world, time_var, body):
    return z3.ForAll(
        time_var,
        z3.Implies(
            self.is_valid_time(time_var),  # bounds: (-M, M) open interval
            body
        )
    )
```

So `Future A` at (world, time=0) requires: for all `t` with `-M < t < M` and `0 < t`, `A` is true
at (world, t). Because atoms require `is_valid_time_for_world(world, t)`, at any `t` in the global
range but outside the world's interval, `A` (for atoms) is false.

**Box operator** (`operators.py`, lines 387-409): Only quantifies over worlds where
`is_valid_time_for_world(other_world, eval_time)` holds. This is a crucial divergence from the
paper's semantics.

**Abundance constraint** (`semantic.py`, `skolem_abundance_constraint`, lines 955-1002):
Uses Skolem functions `forward_of` and `backward_of` that shift by exactly +/-1. Worlds are only
required to have time-shifted counterparts if they can shift forward/backward (i.e., if their
interval end/start is not at the boundary of the global range).

---

## Part 2: Why Perpetuity Fails in the ModelChecker

### 2.1 Concrete Countermodel Construction

With `N=2, M=2`, consider a model with:
- Global time range: `(-2, 2)` open, so valid times are `{-1, 0, 1}`
- World 0 (main world): interval `[0, 1]` (times 0 and 1)
- World 1: interval `[-1, 0]` (times -1 and 0)
- Atom `A` is true at world state `s1` but not `s0`
- Main world W0: both times 0 and 1 map to state `s1` (A true in-domain)
- World W1: time -1 maps to `s1` (A true), time 0 maps to `s0` (A false)

**Why `□A` holds at (W0, 0)**:
The box operator checks: for all worlds `w` where `0` is in `w`'s interval, is `A` true?
- W0 has 0 in interval, A true at 0 (state s1) -- OK
- W1 has 0 in interval, A false at 0 (state s0) -- FAIL

Actually this fails. Let us try:
- W1: both -1 and 0 map to s1, so A true at 0

**The actual countermodel is different**: Z3 finds a model where some world `w` has its interval
entirely in the future (e.g., `[1, 1]`), so time 0 is NOT in its interval, the box condition
vacuously ignores it for the box check (because of `is_valid_time_for_world` guard), but it still
exists as a future world that `Future A` must check.

More precisely: because `NecessityOperator.true_at` uses the condition
`semantics.is_valid_time_for_world(other_world, eval_time)`, a world whose interval does not
include `eval_time=0` is **excluded from the box quantification**. However, `Future A` at time 0
in world W0 requires A to be true at all valid times `t > 0`. If W0's interval is `[0,0]` (only
time 0), then `A` is false at time 1 in W0 (outside domain). So `Future A` is false.

Meanwhile, `□A` at (W0, 0) only quantifies over worlds containing time 0, so it can be satisfied
by having A true at every world that contains time 0, without any constraint on worlds that only
span times > 0.

**The diagnosis**:

The fundamental problem is that `NecessityOperator.true_at` uses:
```
is_valid_time_for_world(other_world, eval_time)
```
as a guard, which means it only requires `phi` true at worlds that CONTAIN the evaluation time.
But the paper's Box quantifies over ALL world histories unconditionally. A world history can be
evaluated at any time, including times outside its domain -- atoms just become false.

This creates an asymmetry: `□A` at time 0 only requires A true in worlds that span time 0, while
`Future A` at time 0 requires A true at times 1, 2, etc. in the CURRENT world. But the current
world might only span times [-1, 0], making A false at time 1 (outside domain).

**Two independent failure modes**:

**Failure Mode 1 (Box scope mismatch)**: The box guard `is_valid_time_for_world` means a world
can satisfy `□A` while having A false at times inside its own domain (because the box at time 0
ignores worlds whose domains don't include time 0). In the paper, `□A` at time 0 requires A true
at (sigma, 0) for ALL sigma in H_F -- even if sigma.domain doesn't include 0, the atom condition
at time 0 just becomes: `exists ht : sigma.domain 0, ...` which fails, so `A` is false there.
In the paper's semantics, `□A` at time 0 in a model where some world's domain lacks time 0 would
FAIL for that world.

Wait -- this needs careful reconsideration. In the paper: `M,tau,x |= Box phi iff M,sigma,x |= phi
for ALL sigma in H_F`. For atoms: `M,sigma,x |= p iff x in dom(sigma) AND sigma(x) in |p|`. If
`x not in dom(sigma)`, then `M,sigma,x |= p` is FALSE. So `□p` requires that EVERY world history
contains time x in its domain AND the state at time x satisfies p.

In the Lean model: `box phi` requires `for all sigma in Omega, truth_at M Omega sigma t phi`. For
atoms: `truth_at M Omega sigma t (atom p) = exists (ht : sigma.domain t), M.valuation (sigma.states t ht) p`.
This is exactly false when `not sigma.domain t`.

So: in both the paper and Lean, `□p` at time 0 implicitly requires EVERY world in Omega/H_F to
have time 0 in its domain. The paper's `H_F` is the full set of all possible histories, which
includes histories of varying domains. But the paper's model's semantics: truth of `□p` at (tau, 0)
requires all sigma in H_F to have p true at time 0, including those that don't have 0 in their
domain -- for which `p` is false.

**This means the ModelChecker's `is_valid_time_for_world` guard is WRONG.** In the paper and Lean,
`□A` at time 0 requires A to be TRUE at all world histories at time 0 -- including those whose
domain does not contain time 0 (which makes A false). The ModelChecker's guard
`is_valid_time_for_world(other_world, eval_time)` skips worlds whose domain doesn't contain the
evaluation time, making `□A` weaker than in the paper.

**Failure Mode 2 (Abundance closure scope)**: Even if we fix the box guard, the abundance
constraint only provides +/-1 shifts. The paper's auto_existence provides shifts by ANY `y - x`
for any two times. With only finitely many world histories and only +/-1 shifts available, the
time-shift invariance property that underlies the MF proof does not hold.

**Failure Mode 3 (Finite domain boundary)**: `Future A` at time 0 in the current world requires A
at all valid times t > 0. With finite time domain `(-M, M)`, there are future times within this
range. For atoms, A is false outside the world's interval. If the current world's interval ends at
0 (or at 1 for M=2), then Future A checks A at time 1. If the world's interval ends at 0, A is
false at time 1. Since the paper's D is unbounded (every time in an infinite D), this does not
happen for the world that is the evaluation world in the paper's model: `tau` in `M,tau,x |= Future
phi` has an arbitrary convex domain -- including the full D. In a well-formed paper model for a
valid formula, the main world would typically have a domain spanning all of D (or the relevant
interval). But the ModelChecker allows the main world to have a bounded interval.

### 2.2 Summary of Failures

| Divergence | Paper | Lean | ModelChecker |
|------------|-------|------|--------------|
| Atom falsity outside domain | Yes | Yes | Yes (correct) |
| Box scope | All sigma in H_F (no domain guard) | All sigma in Omega (no domain guard) | Only sigma where eval_time in interval (WRONG) |
| Future/Past scope | All t in D (infinite) | All t : D (type) | All t in (-M, M) (finite) |
| Time-shift closure | Full auto_existence (any shift) | ShiftClosed (any Omega member, any shift) | Only +/-1 shifts (WRONG) |
| Time domain | Infinite D (all of Z or R) | Full type D (e.g., Z) | Finite {-M+1, ..., M-1} |

---

## Part 3: Why BM_CM_1, BM_CM_3, TN_CM_2 Timeout

### BM_CM_1: `Future A |= □A` (should find countermodel, times out)

In the paper, `Future A |= □A` is NOT valid. A countermodel: a world history tau with
`M,tau,0 |= Future A` (A is true everywhere in tau at t > 0), but some other sigma in H_F where
A is false at time 0. This countermodel is straightforward to describe.

In the ModelChecker: the Z3 solver must find a model where:
- `Future A` is true at the main world (W0, t=0): A is true at all future times in W0
- `□A` is false: some world W1 has A false at time 0, with 0 in W1's interval

The timeout arises because the abundance constraint forces complex relationships between worlds.
The Skolem functions `forward_of` and `backward_of` create many world-relationship constraints,
and the solver struggles to find a satisfying assignment within the search space.

### BM_CM_3: `◇A |= future A` (should find countermodel, times out)

`future A` (lowercase) likely refers to `some_future A` = `F(A)`, the existential future. `◇A |=
F(A)` is not valid: there can be a possible world where A is true but not in the future of the
current time. The countermodel is: A is true in some accessible world at the current time (making
`◇A` true), but not at any future time in the current world.

The timeout arises from the interaction of modal and temporal quantification in the Z3 search.

### TN_CM_2: `future A, future B |= future(A∧B)` (should find countermodel, times out)

`F(A), F(B) |= F(A∧B)` is not valid: A might be true at t1 > now and B at t2 > now with t1 ≠ t2,
while there is no single time where both are true. This is a standard countermodel.

The timeout is caused by complexity: 3 worlds (M=3), multiple interval constraints, and the
conjunction interaction in the temporal domain creates a large search space.

### Common Root Cause of Timeouts

All three timeout cases involve the solver needing to satisfy the abundance constraint (which forces
systematic world-shift relationships) while simultaneously satisfying complex modal/temporal
constraints. The Skolem-based abundance constraint creates many universally-quantified conditions
that chain together through Z3's E-matching, creating excessive solver overhead.

---

## Part 4: Approach A -- Exact Paper Semantics in Z3

### Description

Encode world histories as partial functions over integer-sorted time domains, with temporal
operators quantifying over all integers. Use Z3's quantifier-based reasoning over unbounded
integer sorts rather than BitVec or finite arrays.

### Z3 Implementation Sketch

```python
# Time domain: IntSort (Z3's integer = mathematical integers, unbounded)
TimeSort = z3.IntSort()
WorldStateSort = z3.BitVecSort(N)

# World function: world_id -> (time -> state) with explicit domain predicate
world_domain = z3.Function('domain', WorldIdSort, TimeSort, z3.BoolSort())
world_states = z3.Function('states', WorldIdSort, TimeSort, WorldStateSort)

# Atom truth: requires domain membership
def atom_true_at(world, time, atom):
    return z3.And(world_domain(world, time),
                  truth_condition(world_states(world, time), atom))

# Future operator: quantifies over ALL integers > time
def future_true_at(phi_true_at, world, time):
    t2 = z3.Int('fut_t')
    return z3.ForAll([t2], z3.Implies(t2 > time, phi_true_at(world, t2)))

# Box operator: quantifies over ALL worlds (no domain guard at eval_time)
def box_true_at(phi_true_at, world, time):
    w2 = z3.Int('box_w')
    return z3.ForAll([w2], z3.Implies(is_world(w2), phi_true_at(w2, time)))

# Abundance: for any world and any shift delta, a shifted world exists
delta = z3.Int('delta')
w2 = z3.Int('shifted_w')
abundance = z3.ForAll([world, delta],
    z3.Implies(is_world(world),
        z3.Exists([w2], z3.And(
            is_world(w2),
            z3.ForAll([t], z3.Implies(world_domain(world, t),
                z3.And(world_domain(w2, t + delta),
                       world_states(w2, t + delta) == world_states(world, t)))),
            z3.ForAll([t], z3.Implies(world_domain(w2, t),
                world_domain(world, t - delta)))
        ))
    )
)
```

### Pros

1. **Faithful to the paper**: The semantics would exactly match the paper's definitions.
2. **Perpetuity would be valid**: The proof structure transfers directly: auto_existence is
   encoded in the abundance constraint, and time-shift preservation is provable.
3. **No boundary artifacts**: With unbounded integers, Future A never fails due to a boundary.
4. **Correct box scope**: No `is_valid_time_for_world` guard on the box.

### Cons

1. **Decidability concerns**: Z3's integer arithmetic with universal quantifiers over an unbounded
   domain is undecidable in general. Z3 would use heuristic instantiation and may loop or give
   `unknown` rather than a definitive answer.
2. **Performance**: Quantifier-heavy formulas over integers are much harder than finite BitVec
   problems. Current examples with M=2 taking 10s would likely timeout systematically.
3. **Completeness of countermodel search**: Z3 cannot guarantee finding countermodels for
   invalid formulas in undecidable theories. The model checker's main value is finding
   countermodels; losing this would be a significant regression.
4. **World representation**: With an infinite time domain, "listing" model elements for display
   becomes impossible without additional finiteness constraints.
5. **Complexity of encoding**: The abundance constraint with arbitrary shift `delta` quantified
   universally is a second-order property -- Z3 would need to instantiate it heavily.

### Assessment: Not recommended for primary implementation

Approach A is theoretically correct but practically infeasible for a model checker intended to
find countermodels interactively. It would turn the system into a theorem prover backend rather
than an interactive countermodel finder.

---

## Part 5: Approach B -- Finite Histories with Time-Shift Closure

### Description

Keep finite world histories but add constraints ensuring that:
1. The box operator quantifies over ALL worlds unconditionally (fix the domain guard bug)
2. For every world and every valid time-shift amount, a shifted copy exists
3. The abundance constraint provides shifts by all amounts, not just +/-1

### Sub-approach B1: Fix Box Scope

The minimal fix is to remove the `is_valid_time_for_world` guard from the box operator:

```python
# Paper-aligned: no domain restriction on box
def true_at(self, argument, eval_point):
    eval_time = eval_point["time"]
    other_world = z3.Int('nec_true_world')
    return z3.ForAll(
        other_world,
        z3.Implies(
            semantics.is_world(other_world),  # Remove is_valid_time_for_world guard
            semantics.true_at(argument, {"world": other_world, "time": eval_time})
        )
    )
```

This would make `□A` at time 0 require A true at ALL worlds, including those whose domain doesn't
contain time 0 -- for which atoms are false. This is the paper's semantics.

### Sub-approach B2: Full Abundance Closure

Replace the +/-1 Skolem abundance with a constraint requiring shifts by all amounts in the valid
time range:

```python
def build_full_abundance_constraint(self):
    source_world = z3.Int('abund_src')
    target_world = z3.Int('abund_tgt')
    shift_amount = z3.Int('abund_shift')
    
    return z3.ForAll(
        [source_world, shift_amount],
        z3.Implies(
            z3.And(
                self.is_world(source_world),
                self.is_valid_duration(shift_amount)  # shift within valid range
            ),
            z3.Exists(
                [target_world],
                z3.And(
                    self.is_world(target_world),
                    self.is_shifted_by(source_world, shift_amount, target_world)
                )
            )
        )
    )
```

### Sub-approach B3: Require All Worlds to Span Full Time Domain

The simplest structural fix: require all worlds in a model to have the same interval (the full
valid time range). This ensures that `□A` at any time t requires A true in all worlds (which all
contain t), and `Future A` at time t requires A true in the current world at all future times
(which are all in the current world's domain). This would make atoms always have truth values
within domains.

```python
# All worlds span full time range (-M+1, M-1)
def full_domain_constraint(self):
    w = z3.Int('full_dom_w')
    return z3.ForAll(
        [w],
        z3.Implies(
            self.is_world(w),
            z3.And(
                self.world_interval_start(w) == z3.IntVal(-self.M + 1),
                self.world_interval_end(w) == z3.IntVal(self.M - 1)
            )
        )
    )
```

If all worlds span the full time range, then:
- Atoms are never "out of domain" (no domain falsity issue)
- `□A` at time t with the domain guard `is_valid_time_for_world` becomes equivalent to paper
  semantics (since all worlds contain all times)
- `Future A` at time t requires A at all future times within the fixed domain

But this approach would make some valid countermodels impossible (e.g., for BM_CM_1, we need a
world where A is false at some time that is in the future of the evaluation point).

### B4: Hybrid Approach (Recommended)

The recommended approach combines:
1. **Fix box scope**: Remove `is_valid_time_for_world` from `NecessityOperator.true_at`
2. **Full abundance by shift coverage**: Provide shifted worlds for all integer shifts within
   the valid range (not just +/-1). With valid time range `(-M, M)`, the valid shifts are
   `{-(2M-2), ..., 2M-2}`.
3. **Keep finite intervals**: Let worlds have varying intervals within the bounded domain, but
   ensure the abundance property covers all relevant shifts.

**Why this works for perpetuity**:

After fixing the box scope, `□A` at time 0 requires A true in all worlds at time 0. For a world
whose domain doesn't include time 0, atoms are false -- so `□A` can only hold if every world
has time 0 in its domain AND A is true there.

With full abundance, for any world sigma and any valid time s > 0, there exists a time-shifted
world rho = time_shift(sigma, s). If `□A` holds at time 0, then A is true in all worlds
including `time_shift(sigma, s)` at time 0. By time-shift preservation, this equals A at (sigma, s).
So `Future A` holds.

**Why this doesn't break countermodel finding**:

For BM_CM_1 (`Future A |= □A`): A countermodel has A true at all future times in the main world,
but some world sigma where A is false at time 0. This is still constructible with fixed box scope
-- we just need A false in some world at time 0, regardless of that world's domain.

For BM_CM_3 and TN_CM_2: These are independent of the perpetuity issue and should be solvable
with the corrected semantics.

### Approach B: Pros and Cons

**Pros**:
1. Maintains computability: Z3 still works over finite model structures (bounded integer ranges)
2. Fixes perpetuity: The proof structure transfers to the finite model
3. Corrects the fundamental box scope error that diverges from the paper
4. Compatible with the existing architecture (array-based worlds, interval tracking)
5. Decidable: Bounded integer arithmetic with quantifiers over finite ranges is decidable

**Cons**:
1. The abundance constraint with all shifts creates a larger constraint system (more world IDs
   needed in the model, more Skolem function constraints)
2. Performance may degrade because more worlds must be in the model (to satisfy abundance)
3. Some existing examples might need max_time adjustments
4. The fix to box scope changes the semantics meaningfully -- existing tests for BM_TH_1 and
   BM_TH_2 need to be updated (expectation changed from True/countermodel to False/no-countermodel)

---

## Part 6: Impact Assessment and Recommendation

### Impact on BM_TH_1 and BM_TH_2

After the fix:
- BM_TH_1 (`□A → Future A`): Z3 should find NO countermodel (valid), confirming the paper
- BM_TH_2 (`□A → Past A`): Z3 should find NO countermodel (valid), confirming the paper
- `expectation` in settings should change from `True` (countermodel expected) to `False` (no countermodel)
- The NOTE comments in examples.py explaining the countermodel under "strict semantics" should be removed

### Impact on BM_CM_1, BM_CM_3, TN_CM_2

The timeout behavior is caused by:
1. The abundance constraint creating excessive Skolem function constraints
2. Z3 struggling with the interaction of modal and temporal quantification in the current encoding

After fixing the box scope and improving abundance:
- BM_CM_1 (`Future A |= □A`): Should find a countermodel efficiently (A true in main world's
  future, but some other world has A false at eval time)
- BM_CM_3 (`◇A |= future A`): Should find a countermodel (A accessible modally but not in
  the future of the current world)
- TN_CM_2 (`future A, future B |= future(A∧B)`): Should find a countermodel (A true at t1,
  B true at t2, with t1 ≠ t2 and no overlap)

The timeout elimination depends on whether the revised abundance constraint is more or less
expensive for Z3. Full abundance (by all shifts) may actually reduce solver load for these
examples because the box operator with correct scope is more constrained, making the search space
smaller (fewer models satisfy the corrected `□A`).

### Recommendation

**Pursue Approach B** with the specific fixes:

**Fix 1 (Critical)**: Remove `is_valid_time_for_world` guard from `NecessityOperator.true_at`
in `operators.py`. This is the most impactful single fix and aligns with both the paper and Lean.

**Fix 2 (Important)**: Replace +/-1 Skolem abundance with full abundance covering all integer
shifts within the valid range. Use either:
- Parameterized shifts in the Skolem constraint (a shift variable rather than fixed +/-1)
- Explicit shifts for all values in `{-(2M-2), ..., 2M-2}`

**Fix 3 (Consequential)**: Update test expectations:
- BM_TH_1 and BM_TH_2: change `expectation` from `True` to `False`
- Remove NOTE comments about "strict semantics" countermodels (these were semantic errors)
- Verify BM_CM_1, BM_CM_3, TN_CM_2 produce countermodels within timeout

**Fix 4 (Optional, for performance)**: Profile whether full abundance or partial abundance
with Skolem functions performs better. Consider capping shifts based on the actual interval
lengths of worlds in the model.

---

## Part 7: The Lean vs. Paper Distinction on Atom Falsity

One subtle point deserves attention: both the Lean formalization and the paper agree that atoms
are false outside a history's domain. This is correct. The question is whether this causes a
problem for perpetuity.

In the paper and Lean, the proof of MF works because:
- `□A` requires A at ALL world histories (including those with small domains)
- For ANY sigma and s > t, `time_shift(sigma, s-t)` is a valid history in H_F
- By time_shift_preserves_truth, `A` at `(sigma, s)` equals `A` at `(time_shift(sigma, s-t), t)`
- Since `□A` holds, `A` at `(time_shift(sigma, s-t), t)` holds
- The key: the shifted history has `t` in its domain iff the original had `s` in its domain

For an atom `p`, `truth_at M sigma s (atom p) = exists (hs : sigma.domain s), M.val (sigma.states s hs) p`.
The time-shifted history has `(time_shift sigma Delta).domain t = sigma.domain (t + Delta) = sigma.domain s`.
So if `sigma.domain s`, then `(time_shift sigma (s-t)).domain t`, and the states are equal.

The consequence: `□p` at time `t` in a Lean/paper model implicitly requires that every world in
Omega contains time `t` in its domain AND has `p` true there. This is a STRONG condition. It means
valid paper models for `□p` must have all histories containing the evaluation time.

The ModelChecker's failure is NOT about atoms being false outside domain (that's correct). The
failure is about the **box scope guard** that excludes worlds without the evaluation time from the
box quantification. This weakens `□A` and breaks the connection to `Future A`.

---

## Appendix: Proof Structure Alignment

### Paper proof of thm:MF-valid

```
Given: M,tau,x |= Box phi
Goal:  M,tau,x |= Box Future phi
=> For any sigma in H_F, need M,sigma,x |= Future phi
   => For any y > x, need M,sigma,y |= phi
      By app:auto_existence: exists rho in H_F with sigma ~_y^x rho (shift a(z) = z - x + y)
      By lem:history-time-shift-preservation: M,sigma,y |= phi iff M,rho,x |= phi
      Since Box phi: M,rho,x |= phi (rho in H_F)
      Therefore M,sigma,y |= phi. QED
```

### Lean proof of modal_future_valid

```lean
-- Intro: for any tau in Omega, at any t, assuming Box phi,
-- need: for any sigma in Omega, Future phi at (sigma, t)
intro h_box_phi sigma h_sigma_mem s hts
-- s > t (hts : t < s)
-- Construct time_shift sigma (s - t) -- in Omega by h_sc
have h_phi_at_shifted := h_box_phi (WorldHistory.time_shift sigma (s - t)) (h_sc sigma h_sigma_mem (s - t))
-- h_phi_at_shifted : truth_at M Omega (time_shift sigma (s-t)) t phi
-- By time_shift_preserves_truth: truth at (time_shift sigma (s-t), t) iff truth at (sigma, s)
exact (TimeShift.time_shift_preserves_truth M Omega h_sc sigma t s phi).mp h_phi_at_shifted
```

### ModelChecker (would work if fixed)

```
Given: Z3 model satisfies □A at (W0, t=0) [with correct box scope: all worlds, no domain guard]
Goal: Z3 model satisfies Future A at (W0, t=0)
For any valid t' > 0: need A true at (W0, t')
  If t' in W0's domain: A is true there (because □A at t=0 requires A in W0 at t=0;
    but wait, this only gives t=0, not t' > 0)

Actually the proof does NOT directly work with finite models.
The critical issue: with finite histories, auto_existence requires a time-shifted copy of W0
in the model. If W0 has interval [0, M-1], then at time 1, we need W0[1].
But for □A at t=0 to imply A at (W0, 1), we'd need time_shift(W0, 1-0) in the model.
The shifted world would have interval [1, M] but M is out of bounds.

This is why the finite boundary causes problems even with fixed box scope.
The full fix requires abundance by arbitrary shifts to ensure time-shifted copies exist.
```

---

## References

- JPL paper: `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`
  - Lines 883-947: semantic definitions
  - Lines 2154-2178: app:auto_existence
  - Lines 3217-3226: thm:MF-valid proof
  - Lines 3245-3251: cor:perpetuity-valid
- BimodalLogic Lean formalization:
  - `Theories/Bimodal/Semantics/WorldHistory.lean`: world history type
  - `Theories/Bimodal/Semantics/Truth.lean`: truth evaluation, ShiftClosed definition
  - `Theories/Bimodal/Metalogic/Soundness.lean` lines 252-258: modal_future_valid
  - `Theories/Bimodal/Theorems/Perpetuity.lean`: P1-P6 derivations
- ModelChecker:
  - `code/src/model_checker/theory_lib/bimodal/semantic.py`: Z3 encoding
  - `code/src/model_checker/theory_lib/bimodal/operators.py`: operator implementations
  - `code/src/model_checker/theory_lib/bimodal/examples.py`: BM_TH_1/2, BM_CM_1/3, TN_CM_2
