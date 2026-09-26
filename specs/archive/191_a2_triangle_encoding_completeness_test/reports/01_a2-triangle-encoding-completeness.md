# Research Report: A2-triangle encoding-completeness test for bimodal certificates

- **Task**: 191 - A2 triangle encoding completeness test
- **Started**: 2026-09-25T23:10:27Z
- **Completed**: 2026-09-25T23:45:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (sections 5, 7.1-7.4 — the A2
    obligation and its deciding test's exact statement)
  - `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` (the pure-Python
    re-checker, `recheck`/`recheck_json`, window helpers)
  - `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` and
    `witness_constraints.py` (the Z3 variable layer and constraint generators leg (iii) exercises)
  - `code/src/model_checker/theory_lib/bimodal/semantic/core.py` and `semantic/model.py`
    (`BimodalSemantics`/`BimodalStructure` — the actual search entry point)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
    (leg (i)/(ii) infrastructure: `lake exe check_certificate` invocation, skip discipline)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
    (`_build()` helper and `TestA0FrameClassStandingTest` — the sibling ADEQUACY-7 deciding test
    already landed, and the closest structural precedent for A2)
  - `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/*.json` and README.md
    (existing small Γ/Δ examples with known, adjudicated closures)
  - `specs/184_.../plans/01_witness-family-certificate-redesign.md` (Phase 5 and Phase 9 —
    confirms the broken "Phase 9 handoff" resumption pointer and where A0 actually landed)
  - Live probe of this host: `lake` (`~/.elan/bin/lake`) and `~/Projects/BimodalLogic` are both
    present, so the Lean leg can actually execute here, not merely be exercised in skip-mode.
- **Artifacts**: This report only (research phase).
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The task description's premise is confirmed: no A2-triangle test exists anywhere in the repo
  (no `itertools.product`/enumeration precedent in any bimodal test file), and the "Phase 9
  handoff" the certificate-redesign plan pointed to carries only the A0 test
  (`test_structure.py:224-263`), not A2 — the plan's own Phase 5 task list (line 476-479)
  independently confirms this deferral and names Phase 9 as the resumption point, which never
  happened for A2.
- All three legs' entry points already exist and need no new production code: (i) the re-checker
  is `certificate.recheck`; (ii) the Lean leg reuses `test_certificate_lean_agreement.py`'s
  `_run_check_certificate` helper; (iii) the real Z3 search is reached exactly as
  `test_structure.py`'s `_build(premises, conclusions, **settings)` helper already does — build
  `Syntax` → `BimodalSemantics` → `ModelConstraints` → `BimodalStructure` and read
  `structure.z3_model_status`.
- The "encoding unsoundness" half of A2 (iii=SAT where the checkers reject) is **already
  guarded at runtime** by `BimodalStructure.__init__` (`semantic/model.py:73-94`): any Z3-SAT
  model whose extracted certificate fails the Python re-check raises `ModelConstructionError`
  immediately. The genuinely untested direction — and the one this task's own description
  emphasizes — is **encoding incompleteness**: Z3 reports UNSAT even though a candidate
  certificate exists that both the Python re-checker and the Lean binary accept.
- A literal brute-force enumeration ("every candidate `(bx, Λ0,…,Λk)` over subsets of `C`") is
  combinatorially cheap for a box-free closure (~1,500 candidates) but explodes to ~1.6 million
  raw candidates for a closure containing even a single boxed formula (main lasso + one witness
  lasso, each independently ranging over `2^|C|` labels per of 3 slots). Section "Combinatorics"
  below gives exact counts and a two-tier mitigation (exhaustive-but-cheap Python re-check,
  Lean cross-check bounded to the python-flagged countermodel candidates plus a small sample of
  rejects) that keeps runtime in line with the existing Lean-agreement suite.
- Two concrete, closure-verified Γ/Δ pairs are identified and ready to drive the test directly:
  a box-free Until case (`|C|=3`, no witness lasso) and a single-box case (`|C|=3`, one witness
  lasso) that exactly mirrors fixture `01_positive_box.json` and the A0 test's own example
  formulas.

## Context & Scope

ADEQUACY.md §7.3 states the A2-triangle test precisely: fix `back = mid = fwd = 1` and a closure
`C` with `|C| ≤ 4`; exhaustively enumerate every candidate witness family at those lengths;
compare (i) the Python re-checker, (ii) `lake exe check_certificate`, (iii) whether the real Z3
encoding (run at the same lengths, on the same Γ/Δ) reports SAT. This report scopes what the
implementation phase needs: which code to call for each leg, which Γ/Δ pairs keep the
enumeration tractable, and how to bound the parts that don't scale (raw enumeration size, and
Lean subprocess count).

This is a **research** deliverable — no test code is written here. The recommendations below are
sized so `/plan` can turn them directly into phases.

## Findings

### Leg (i): the Python re-checker — no new code needed

`certificate.recheck(family, premises, conclusions, target_time)` (`certificate.py:358-433`)
takes an already-decoded `WitnessFamily` (`bx` dict + tuple of `LabelledLasso`) and a target time,
and returns `{"status": "countermodel", ...}` or `{"status": "rejected", "failed": [...]}`. This
is exactly the API an exhaustive-candidate generator needs to drive per candidate; no
`recheck_json`/wire-format round-trip is required for this leg (that wrapper only matters for
leg (ii)'s JSON payload).

### Leg (ii): `lake exe check_certificate` — reuse the existing helper

`tests/integration/test_certificate_lean_agreement.py` already has every piece needed:
`_resolve_bimodal_logic_path`/`_resolve_lake` (skip discipline), `_run_check_certificate(payload,
timeout)` (the per-invocation subprocess wrapper with a bounded timeout), and the module-level
probe-then-skip pattern (`_probe()`, `pytestmark = pytest.mark.skipif(...)`). The new test module
should follow the identical skip discipline (never fail when BimodalLogic/`lake` are absent) and
can either import these helpers directly or duplicate the ~15-line wrapper — the existing module
does not currently export them as a public API, so the plan should decide between a small
refactor (export a `bimodal.testing` helper) or an intentional near-duplicate, consistent with
Phase 5's own precedent of extending the existing module in place rather than duplicating
plumbing (plan Phase 5, "Deviation" note, line 445-451).

`WitnessFamily.to_json(premises, conclusions, target_time)` (`certificate.py:149-167`) is the
existing serializer for any candidate family — including a synthetically constructed one that
was never run through Z3 — so leg (ii) needs no export machinery beyond what already exists.

On this host, both `lake` and `~/Projects/BimodalLogic` are present and the module's own probe
already passes (confirmed by the existing 10/10 green suite recorded in the plan's Phase 5
verification), so leg (ii) is not merely a skip-mode placeholder here — it will actually run.

### Leg (iii): the real Z3 search — `_build()` is the exact entry point

`test_structure.py:30-38` already builds the complete pipeline outside `run_test`'s
match/mismatch abstraction, giving direct access to `structure.z3_model_status` (bool) and
`structure.certificate` (the extracted, already re-checked `WitnessFamily`, or `None`):

```python
def _build(premises, conclusions, **setting_overrides):
    settings = _settings(**setting_overrides)
    syntax = Syntax(premises, conclusions, bimodal_operators)
    model_constraints = ModelConstraints(settings, syntax, BimodalSemantics(settings), BimodalProposition)
    structure = BimodalStructure(model_constraints, settings)
    return structure
```

Calling `_build(premises, conclusions, back=1, mid=1, fwd=1)` is leg (iii) in full: SAT/UNSAT is
`structure.z3_model_status`. Note `BimodalStructure.__init__` (`semantic/model.py:62-104`)
**already** independently re-checks whatever certificate Z3 extracts and raises
`ModelConstructionError` if it fails — so if this call ever returns SAT with an unsound
certificate, the test never sees a silent false positive; it sees an exception. This means the
"iii=true where checkers reject" (unsoundness) half of A2 is already fail-fast-guarded in
production for whichever single certificate Z3 happens to produce. The new test's marginal value
on the unsoundness side is checking Lean agreement on that specific extracted certificate too
(the production guard only calls the Python `recheck`, never Lean) — cheap, since it is one
extra `lake` invocation per Γ/Δ example, not per candidate.

The genuinely new leg is completeness: confirming that whenever the *exhaustive* candidate
enumeration contains at least one family both checkers accept, `structure.z3_model_status` is
`True` — i.e., the encoder's constraint set is not stricter than (C1)-(C4).

Each Γ/Δ example needs exactly **one** Z3 solve (leg iii is a single SAT/UNSAT fact per closure,
independent of which candidate is being compared against it) — the combinatorial cost below is
entirely on the candidate-enumeration side (legs i/ii), not leg iii.

### Combinatorics: why "exhaustive" needs bounding, and how

With `back = mid = fwd = 1`, `WitnessRegistry.slots_per_lasso` (`witness_registry.py:120-122`)
is exactly 3 (one back slot, one mid slot, one fwd slot) — matching `target_window()`
(`range(-nb, nm+nf)` = `range(-1, 2)`, 3 positions, one per slot). Each label is an arbitrary
subset of the closure `C`, so a single lasso has `(2^|C|)^3` possible labelings. A boxed
subformula in `C` requires one additional witness lasso (`finalize_certificate`,
`core.py:308-314`), each independently ranging over the same `(2^|C|)^3` space, plus one free
`bx` boolean per boxed child.

Two closure-verified example candidates (closures computed via `subformula_closure`,
`formula.py:156-179`, which is plain syntactic decomposition — no negation/fixpoint closure, so
`|C|` stays small for short formulas):

| Γ/Δ (surface syntax) | Closure `C` | `\|C\|` | Boxes | Lassos | Raw label combos | × `bx` | × target-time (3) | Total recheck calls |
|---|---|---|---|---|---|---|---|---|
| `[]`, `["(q \Until p)"]` | `{Untl(guard=p,event=q), p, q}` | 3 | 0 | 1 | `8^3 = 512` | 1 | 3 | **1,536** |
| `["\Box A"]`, `["B"]` | `{Box(A), A, B}` | 3 | 1 | 2 (main+witness) | `(8^3)^2 = 262,144` | 2 | 3 | **1,572,864** |

The first case (mirroring fixtures `02_infinite_postponement.json`/`04_...coherence.json`'s own
Until-only closures) is trivially fast — well under a second of pure-Python `recheck` calls. The
second (mirroring fixture `01_positive_box.json` and the A0 test's own `["\Box A"], ["B"]`
example, just with `mid=1` instead of `mid=0`) is the one that needs a bounding strategy:
~1.57M `recheck()` calls, each constructing fresh `WitnessFamily`/`LabelledLasso` dataclasses
and frozensets, is likely to run from tens of seconds to a few minutes in pure Python — not
prohibitive, but worth benchmarking before committing to it as an unconditional per-run test.

**Recommended two-tier structure** (keeps the Lean leg — the genuinely expensive one, subprocess
per call — bounded regardless of the outer enumeration size):

1. **Tier 1 (exhaustive, Python-only, always runs)**: enumerate every candidate at the fixed
   lengths for the chosen closure; call `recheck()` on each; record whether *any* candidate is a
   `"countermodel"`. Compare this single boolean against `_build(...).z3_model_status` for the
   same Γ/Δ. A mismatch localizes an encoding defect per ADEQUACY §7.3's own rule (SAT-should-be
   iff completeness fails; UNSAT-should-be iff... — see next tier for why the reverse direction
   is already runtime-guarded).
2. **Tier 2 (bounded, Lean, skipped cleanly when `lake`/BimodalLogic are absent)**: run
   `lake exe check_certificate` on (a) every candidate Tier 1 flagged as `"countermodel"`
   (expected to be small — a handful at most, given how constrained (C1)-(C4) are) to confirm
   leg (i)/(ii) agreement on exactly the candidates that matter for the completeness aggregate,
   and (b) the one certificate `_build(...)` actually extracts when SAT, to confirm leg (ii)
   agreement on the live Z3-derived certificate (closing the gap the production fail-fast guard
   leaves: it only calls Python `recheck`, never Lean). A small, fixed-size random or systematic
   sample of the non-countermodel candidates can optionally be added as a spot-check against a
   systematic Python-recheck bug masking a true completeness failure, capped (e.g. ~20-50
   samples) to stay in the same runtime order as the existing 10-test Lean-agreement suite.

**A further optimization worth flagging for the implementer** (not required, but cuts the ~1.57M
figure substantially if runtime proves an issue): `recheck`'s own local-coherence biconditionals
(`_coherent_at`, `certificate.py:266-298`) make every non-atomic formula's label membership a
*derived* fact of the atom valuations, the neighbouring positions, and the `bx` guesses — an
`Imp`/`Box`/`Untl`/`Snce` node's presence in a label is not actually a free choice once atoms and
`bx` are fixed and the fixpoint is solved. A generator that enumerates only over free atom
valuations per slot (not full formula-subset labels) and derives the rest would shrink the
per-slot branching factor from `2^{|C|}` to `2^{|C \cap \text{Atoms}|}` — e.g. `2^2=4` instead of
`2^3=8` in the box example above, a 2x-per-slot (8x-per-lasso, 64x-total) reduction. This is a
genuine implementation-phase design choice, not resolved here, since the ADEQUACY §7.3 text
literally says "enumerate every candidate ... over subsets of `C`," and generating-then-filtering
the raw space is simpler to argue as faithful to that text than a smarter derived generator is.

### Where the new test belongs

`test_structure.py`'s own docstring (`:1-7`) already frames itself as carrying the sibling A0
deciding test "since it needs this phase's own working solve-and-render path" — the same
justification applies to A2 (it needs `_build()`'s working solve path). Two placement options:
add an `TestA2TriangleEncodingCompleteness` class alongside `TestA0FrameClassStandingTest` in
`test_structure.py` (keeping every ADEQUACY-§7 deciding test in one file, consistent with how A0
was placed), or a new `tests/integration/test_certificate_a2_triangle.py` (consistent with the
`test_certificate_lean_agreement.py` precedent for anything with an optional Lean dependency,
since Tier 2 above needs the same skip discipline that module already implements). The second
option avoids adding a `lake`/`BIMODAL_LOGIC_PATH` dependency to `test_structure.py`, which
today has none.

## Decisions

- None — this is a research report; the placement and generator-design choices above are
  recommendations for `/plan`, not decisions.

## Recommendations

1. Place the new test using the `lake`-dependent, skip-disciplined module pattern (new
   `tests/integration/test_certificate_a2_triangle.py`, or extend
   `test_certificate_lean_agreement.py` itself) rather than `test_structure.py`, so the Lean
   dependency's skip discipline is isolated from the always-runs structural tests.
2. Start with the two closure-verified Γ/Δ pairs in the Combinatorics table (Until-only, `|C|=3`,
   no boxes; single-box, `|C|=3`, one witness lasso) — both fit the `|C|≤4` bound with room to
   spare, and both directly reuse formula shapes already adjudicated in the existing fixture
   corpus and the A0 test.
3. Implement Tier 1 (exhaustive Python enumeration + `_build()` SAT/UNSAT comparison)
   unconditionally; implement Tier 2 (Lean cross-check) bounded and skip-guarded exactly like
   `test_certificate_lean_agreement.py`.
4. Benchmark the single-box case's ~1.57M-candidate enumeration before committing to it
   unconditionally; if it proves too slow for the normal test run, either apply the
   atoms-only-generation optimization noted above, or mark that specific case with whatever
   slow-test convention this suite already uses elsewhere (none found in bimodal's own tests;
   check `code/pyproject.toml`'s marker registration, referenced in `test_bimodal.py:36`, for a
   suitable existing marker before inventing a new one).
5. Decide, during planning, whether `_run_check_certificate`/skip-resolution helpers should be
   promoted to a shared, importable location (e.g. a `bimodal/tests/_lean_agreement.py` helper
   module) rather than duplicated a second time — this task is the second consumer of that exact
   logic, which is the usual threshold for extraction.

## Risks & Mitigations

- **Risk**: the ~1.57M-candidate enumeration is too slow for routine test runs.
  **Mitigation**: benchmark early (recommendation 4); fall back to the atoms-only derived
  generator (Combinatorics section) if needed, which is still faithful to enumerating "every
  candidate" since the derivation is forced by (C1), not a narrowing of scope.
- **Risk**: leg (ii) is unavailable in CI or on contributors' machines without a BimodalLogic
  checkout. **Mitigation**: already solved by the skip discipline this task reuses verbatim from
  `test_certificate_lean_agreement.py` — Tier 1 (the actually novel completeness check) still
  runs and is meaningful with Tier 2 skipped.
- **Risk**: picking a Γ/Δ pair whose surface syntax uses `\rightarrow`/`\wedge`/`\vee` (all
  `DefinedOperator`s expanded into nested `Imp`/`Bot` before `translate()`, per
  `formula.py:353-363`) silently blows past `|C|≤4`. **Mitigation**: the two recommended examples
  use only atoms, `\Box`, and `\Until` directly — confirmed by hand against `subformula_closure`
  — and this pitfall should be called out explicitly in the plan/implementation so a later
  example addition doesn't reintroduce it.

## Appendix

- ADEQUACY.md §7.3's literal test statement is quoted in full in the task description and in
  `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md:587-601`.
- The broken "Phase 9 handoff" pointer: `specs/184_.../plans/01_witness-family-certificate-redesign.md:476-479`
  (Phase 5's deferral) and `:673-681` (Phase 9's own deferral of A0, which is what actually landed
  in Phase 12/`test_structure.py`, per `:1006` region — i.e. two different amendment tasks were
  both deferred at Phase 9, and only one of them was ever picked back up).
