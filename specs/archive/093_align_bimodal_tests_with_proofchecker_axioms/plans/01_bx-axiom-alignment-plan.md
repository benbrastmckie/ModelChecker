# Implementation Plan: Align Bimodal Tests with ProofChecker BX Axiom System

- **Task**: 93 - Align bimodal tests with ProofChecker BX axiom system
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: 89 (Until/Since operators), 90 (strict semantics)
- **Research Inputs**: reports/01_bx-axiom-alignment.md
- **Artifacts**: plans/01_bx-axiom-alignment-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The BimodalLogic ProofChecker defines 42 axiom constructors across 8 layers. The ModelChecker currently tests only 3 of these axioms (7% coverage). With Until/Since operators (task 89) and strict semantics (task 90) now implemented, 32 of 42 axioms are directly testable. This plan adds structured test examples to `examples.py` and validates them through the existing test framework, organized by BX axiom layer from simple propositional axioms through advanced temporal axioms.

### Research Integration

Research report `reports/01_bx-axiom-alignment.md` provides the complete BX axiom catalog (42 axioms across 8 layers), operator mappings between ProofChecker and ModelChecker syntax, ready-to-use formula translations, and recommended N/M settings per axiom. Key finding: 32 axioms (76%) are testable now; 10 axioms (24%) are blocked on frame class support (tasks 91/92).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add examples for all 32 currently-testable BX axioms to `examples.py`
- Organize examples by BX axiom layer with clear naming conventions mapping to ProofChecker constructor names
- Validate each axiom runs correctly through `test_bimodal.py`
- Achieve 74% BX axiom coverage (31/42, excluding modal_future already partially tested)
- Include appropriate N/M settings and expectation values for each axiom

**Non-Goals**:
- Testing blocked axioms (uniformity, prior, Z1, density) that require frame class support from tasks 91/92
- Modifying the semantic engine or operator implementations
- Adding new operators or syntactic constructs
- Performance optimization of Z3 solver for complex formulas
- Adding countermodel (CM) examples for invalid formulas

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Complex nested Until/Since formulas cause Z3 timeouts | M | M | Use conservative M settings, add to KNOWN_TIMEOUT_EXAMPLES if needed |
| BX7 linearity axioms (4 variables) exceed solver capacity | M | H | Use N=4, M=5 with extended max_time; mark as known-expensive |
| BX13 enrichment axioms have incorrect syntax translation | M | L | Verify formula structure against ProofChecker source carefully |
| Strict semantics causes unexpected countermodels for valid axioms | H | L | Cross-reference with research report's strict-semantics analysis |
| Large example count slows full test suite | L | M | Maintain KNOWN_TIMEOUT_EXAMPLES exclusion list for CI |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Propositional and S5 Modal Axiom Examples [COMPLETED]

**Goal**: Add test examples for Layer 1 (propositional, 4 axioms) and Layer 2 (S5 modal, 4 new axioms) to `examples.py`.

**Tasks**:
- [ ] Add Layer 1 propositional theorem examples: `PROP_K_TH` (K axiom, N=3), `PROP_S_TH` (weakening, N=2), `EX_FALSO_TH` (ex falso, N=1), `PEIRCE_TH` (Peirce's law, N=2)
- [ ] Add Layer 2 S5 modal theorem examples: `MODAL_T_TH` (reflexivity, N=1), `MODAL_4_TH` (transitivity, N=1), `MODAL_B_TH` (symmetry, N=1), `MODAL_5_TH` (S5 characteristic, N=1, M=2)
- [ ] Add all 8 new examples to the `theorem_examples` dictionary
- [ ] Add all 8 new examples to the `unit_tests` dictionary (via the existing merge)
- [ ] Run `pytest` on `test_bimodal.py` to verify all 8 new examples pass (expectation=False, no countermodel found)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - Add 8 theorem examples in new "BX AXIOM" sections

**Verification**:
- All 8 new examples appear in `unit_tests`
- `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -k "PROP_K_TH or PROP_S_TH or EX_FALSO_TH or PEIRCE_TH or MODAL_T_TH or MODAL_4_TH or MODAL_B_TH or MODAL_5_TH"` passes

---

### Phase 2: Basic BX Temporal Axiom Examples [COMPLETED]

**Goal**: Add test examples for the simpler BX temporal axioms: seriality (BX1/BX1'), connectedness (BX4/BX4'), eventuality extraction (BX10/BX10'), and F-Until/P-Since bridge (BX12/BX12'). Also add the modal-temporal interaction axiom.

**Tasks**:
- [ ] Add BX1 seriality theorems: `BX1_SERIAL_F_TH` (future seriality, M=2), `BX1P_SERIAL_P_TH` (past seriality, M=2)
- [ ] Add BX4 connectedness theorems: `BX4_CONNECT_F_TH` (already tested as TN_TH_2 but add canonical name), `BX4P_CONNECT_P_TH` (past connect, M=3)
- [ ] Add BX10 eventuality extraction theorems: `BX10_UNTIL_F_TH` (Until to F, N=2, M=3), `BX10P_SINCE_P_TH` (Since to P, N=2, M=3)
- [ ] Add BX12 bridge theorems: `BX12_F_UNTIL_TH` (F to Until, M=3), `BX12P_P_SINCE_TH` (P to Since, M=3)
- [ ] Add BX2G/BX2H guard monotonicity theorems: `BX2G_MONO_U_TH` (Until guard mono, N=3, M=4), `BX2H_MONO_S_TH` (Since guard mono, N=3, M=4)
- [ ] Add BX3/BX3' event monotonicity theorems: `BX3_MONO_U_TH` (Until event mono, N=3, M=4), `BX3P_MONO_S_TH` (Since event mono, N=3, M=4)
- [ ] Add modal-temporal interaction: `MF_MODAL_FUTURE_TH` (Box phi -> Box(G phi), already partially tested as BM_TH_5 but add canonical name)
- [ ] Register all new examples in `theorem_examples` dictionary
- [ ] Run `pytest` on `test_bimodal.py` to verify all new examples pass

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - Add 13 temporal theorem examples

**Verification**:
- All new temporal axiom examples produce no countermodel (expectation=False)
- `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` passes with all new examples included

---

### Phase 3: Advanced BX Temporal Axiom Examples [COMPLETED]

**Goal**: Add test examples for the more complex BX temporal axioms: self-accumulation (BX5/BX5'), absorption (BX6/BX6'), temporal linearity (BX11/BX11'), and enrichment (BX13/BX13').

**Tasks**:
- [ ] Add BX5 self-accumulation theorems: `BX5_ACCUM_U_TH` (Until self-accum, N=2, M=4), `BX5P_ACCUM_S_TH` (Since self-accum, N=2, M=4)
- [ ] Add BX6 absorption theorems: `BX6_ABSORB_U_TH` (Until absorption, N=2, M=4), `BX6P_ABSORB_S_TH` (Since absorption, N=2, M=4)
- [ ] Add BX11 temporal linearity theorems: `BX11_LIN_F_TH` (F linearity, N=2, M=4), `BX11P_LIN_P_TH` (P linearity, N=2, M=4)
- [ ] Add BX13 enrichment theorems: `BX13_ENRICH_U_TH` (Until enrichment, N=3, M=4), `BX13P_ENRICH_S_TH` (Since enrichment, N=3, M=4)
- [ ] Register all 8 new examples in `theorem_examples` dictionary
- [ ] Run `pytest` on all new examples, adding any timeout-prone ones to `KNOWN_TIMEOUT_EXAMPLES`
- [ ] Adjust max_time settings if any axioms require longer solver time

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - Add 8 advanced temporal theorem examples
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - Update `KNOWN_TIMEOUT_EXAMPLES` if needed

**Verification**:
- All 8 advanced temporal axiom examples are correctly defined with proper formula translations
- `pytest` passes for all non-timeout examples
- Any timeout-prone examples are documented and excluded from CI

---

### Phase 4: BX7 Linearity Axioms and Final Validation [COMPLETED]

**Goal**: Add the most complex BX7 linearity axioms (4-variable formulas) and perform full test suite validation to confirm complete coverage.

**Tasks**:
- [ ] Add BX7 Until linearity theorem: `BX7_LINEAR_U_TH` (4 variables: A,B,C,D; N=4, M=5, max_time=60)
- [ ] Add BX7' Since linearity theorem: `BX7P_LINEAR_S_TH` (4 variables; N=4, M=5, max_time=60)
- [ ] Register BX7 examples in `theorem_examples` dictionary
- [ ] Test BX7 axioms individually (they may require extended time)
- [ ] Add BX7 examples to `KNOWN_TIMEOUT_EXAMPLES` in `test_bimodal.py` if they exceed reasonable CI time
- [ ] Run full `pytest` suite on `test_bimodal.py` to verify no regressions
- [ ] Add comments documenting BX axiom coverage status (tested / blocked / total)
- [ ] Verify final count: 31 new axiom examples added (32 total testable minus 1 already tested as MD_TH_1)

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/examples.py` - Add 2 BX7 linearity examples; add coverage summary comment
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - Update `KNOWN_TIMEOUT_EXAMPLES` if needed

**Verification**:
- Full test suite passes: `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -v`
- `examples.py` contains examples covering all 32 testable BX axioms
- Coverage reaches 74% (31/42 axioms, with modal_k_dist already covered by MD_TH_1)
- All blocked axioms (layers 5-8) are documented with comments indicating which task unblocks them

## Testing & Validation

- [ ] Each phase's examples pass `pytest` individually
- [ ] Full test suite `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -v` passes with no regressions
- [ ] All theorem examples have `expectation: False` (no countermodel expected)
- [ ] Complex formulas (BX7 linearity, BX13 enrichment) are verified against ProofChecker source for correctness
- [ ] No existing examples (EX_CM_*, MD_CM_*, TN_CM_*, BM_CM_*, EX_TH_*, MD_TH_*, TN_TH_*, BM_TH_*) are modified or broken
- [ ] KNOWN_TIMEOUT_EXAMPLES list is updated if any new examples are too slow for CI

## Artifacts & Outputs

- `specs/093_align_bimodal_tests_with_proofchecker_axioms/plans/01_bx-axiom-alignment-plan.md` (this file)
- `code/src/model_checker/theory_lib/bimodal/examples.py` (modified: ~31 new axiom examples)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (modified: KNOWN_TIMEOUT_EXAMPLES if needed)
- `specs/093_align_bimodal_tests_with_proofchecker_axioms/summaries/01_bx-axiom-alignment-summary.md` (generated at completion)

## Rollback/Contingency

- All changes are additive (new examples only); existing examples remain untouched
- If a formula translation is incorrect, remove the offending example and adjust coverage count
- If Z3 solver cannot handle certain axioms within reasonable time, add to KNOWN_TIMEOUT_EXAMPLES and document as "valid but computationally expensive"
- Git revert of the examples.py changes restores original state with no side effects
