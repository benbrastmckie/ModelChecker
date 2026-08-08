# Known External Oracle Defects

## Scope

This document records defects in **external** reference oracles that this repository's
differential test suite (`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`)
accommodates rather than fixes. An accommodation here means: the differential suite adjudicates
each disagreement against `oracle/bimodal_logic/ground_truth.py` (an independent brute-force
decision procedure) and attributes the divergence to the external oracle rather than treating it
as an unexplained or silently-tolerated failure.

**Standing rule**: an accommodation recorded here is deleted, not weakened, once the upstream
project fixes the underlying defect. The differential suite's staleness guard (see
`test_temporal_only_agreement_complexity_5` in `test_cross_oracle_differential.py`) fails loudly
when the accommodated defect stops reproducing — that failure is the correct signal to remove the
accommodation, never to relax the assertion that detects it.

## Defect: BimodalHarness `find_countermodel` scans its own frame's boundary cells as genuine falsifying points

**Location**: `bimodal_harness/oracle/z3_provider.py`, `Z3OracleProvider.find_countermodel`'s
`encoded_cells` loop, which asserts `z3.Or([z3.Not(cell_enc) for _, _, cell_enc in encoded_cells])`
across every `(w, t)` cell for `w` in `[0, n_worlds)` and `t` in `[0, m_time]` — i.e. it searches
for a falsifying point *anywhere in its entire bounded frame*, including the frame's own edges
(`t = 0`, no past available, and `t = m_time`, no future available).

### Root cause

For a formula shaped `(TAUTOLOGY \Until Y)` or `(TAUTOLOGY \Since Y)` — an event operand that is a
closed tautology (true under every valuation, at every time: e.g. `bot -> bot`, `bot -> p`,
`p -> p`) combined with Until/Since and a guard operand that can be false (`bot` or `p`) — the
*only* witness that reliably satisfies the formula when the guard can be false is the immediately
adjacent time step (`t+1` for Until, `t-1` for Since), because at that witness the guard interval
is empty and holds vacuously, and the event holds regardless of valuation. So the formula is true
at time `t` if and only if an adjacent time step exists.

In the true, unbounded-time semantics both oracles are meant to approximate, an adjacent time step
always exists — every formula of this shape is a genuine tautology, valid everywhere, with no
countermodel. BimodalHarness's `find_countermodel`, however, evaluates its formula at `t = m_time`
(for Until) or `t = 0` (for Since) as part of its exhaustive cell scan. At exactly that edge, the
needed adjacent time step does not exist *within BH's own finite window*, so BH's encoding
correctly computes `z3.Or([]) == False` there — a correct fact about BH's own bounded frame, but
not a genuine falsification in the semantics both oracles approximate. BH reports this as a
countermodel (SAT); the countermodel is a boundary artifact of BH's own window choice, not a real
one.

### Why ModelChecker is correct

ModelChecker never evaluates a formula at its own frame's edge. `main_time` is fixed at
`z3.IntVal(0)` (`code/src/model_checker/theory_lib/bimodal/semantic/core.py:225`), and the valid
time domain is the open interval `(-M, M)` with `M = max(depth + 2, 3)`
(`oracle/bimodal_logic/provider.py:225-226`), where `depth` is the formula's temporal nesting
depth (`oracle/bimodal_logic/translation.py`'s `temporal_depth`). `is_valid_time`'s own docstring
(`core.py:804-819`) states the invariant directly: "Boundary safety: For a formula of temporal
depth d, M >= d+2 ensures that genuine (non-vacuous) evaluation can occur from t=0" — this is a
deliberate design invariant, not an incidental property, and it is independently tracked by
`TestBoundaryVacuity` in `oracle/bimodal_logic/tests/test_soundness_regression.py`.

The canonical semantics (the Lean `BimodalLogic` specification's `Semantics.lean`) types the time
domain as a `LinearOrderedAddCommGroup`, which by definition has no minimal or maximal element —
matching ModelChecker's boundary-safe design intent, not BimodalHarness's edge-inclusive scan.

### The 12 affected formulas

All 12 share the identical `(TAUTOLOGY \Until/\Since Y)` shape and the identical verdict signature
`MC_sat=False` (UNSAT, correct), `BH_sat=True` (SAT, wrong), ground truth `UNSAT`:

| # | Formula (readable) | Formula (JSON) |
|---|---|---|
| 1 | `(bot -> bot) Until bot` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"bot"}}` |
| 2 | `(bot -> bot) Until p` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"atom","name":"p"}}` |
| 3 | `(bot -> p) Until bot` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"bot"}}` |
| 4 | `(bot -> p) Until p` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"atom","name":"p"}}` |
| 5 | `(p -> p) Until bot` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"atom","name":"p"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"bot"}}` |
| 6 | `(p -> p) Until p` | `{"tag":"untl","event":{"tag":"imp","left":{"tag":"atom","name":"p"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"atom","name":"p"}}` |
| 7 | `(bot -> bot) Since bot` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"bot"}}` |
| 8 | `(bot -> bot) Since p` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"atom","name":"p"}}` |
| 9 | `(bot -> p) Since bot` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"bot"}}` |
| 10 | `(bot -> p) Since p` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"atom","name":"p"}}` |
| 11 | `(p -> p) Since bot` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"atom","name":"p"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"bot"}}` |
| 12 | `(p -> p) Since p` | `{"tag":"snce","event":{"tag":"imp","left":{"tag":"atom","name":"p"},"right":{"tag":"atom","name":"p"}},"guard":{"tag":"atom","name":"p"}}` |

### Reproduction

Run the full differential test class against a real BimodalHarness checkout:

```bash
PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5 \
  -v -s -p no:cacheprovider
```

Or adjudicate a single formula directly against the ground-truth evaluator:

```bash
python -m bimodal_logic.ground_truth '{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"bot"}}'
```

### Proposed upstream fixes (for BimodalHarness maintainers)

Either of the following, applied to `find_countermodel`'s `encoded_cells` loop in
`bimodal_harness/oracle/z3_provider.py`:

1. **Exclude the literal edge cells** (`t = 0` for Since's falsifying-point search, `t = m_time`
   for Until's) from the falsifying-point search, matching ModelChecker's boundary-safety design
   intent. The simpler, more targeted change.
2. **Pad `m_time`** relative to the formula's own temporal depth before scanning (mirroring
   ModelChecker's `M = max(depth + 2, 3)`), so the scanned window's edges are never reachable by
   any formula's own recursive witness search. More invasive but generalizes beyond Until/Since
   specifically.

### Removal criterion

When BimodalHarness is fixed upstream (by either proposed fix or an equivalent), the differential
suite's staleness assertion (assertion 4 in `test_temporal_only_agreement_complexity_5`) fires: it
asserts the `external_bh_defect` bucket is non-empty, and a fixed BH will empty that bucket. The
correct response at that point is to **delete this accommodation** — remove the
`classify_disagreement` call path this document backs and this file itself — not to relax the
assertion that detected the fix.
