# BX Axiom System Alignment Report

**Task**: 93 - Align bimodal tests with ProofChecker BX axiom system
**Session**: sess_1780078805_eaddb5
**Date**: 2026-05-29

## Executive Summary

The BimodalLogic ProofChecker defines 42 axiom constructors organized into 8 layers. The ModelChecker currently tests approximately 7 patterns (17% coverage). With Until/Since operators (task 89) and strict semantics (task 90) now implemented, many previously untestable axioms become accessible.

**Key Findings**:
- 32 base axioms valid on all linear temporal orders
- 5 uniformity axioms (ordered abelian groups)
- 2 Prior axioms + 1 Z1 axiom (discrete orders only)
- 2 density axioms (dense orders only)
- Current ModelChecker tests cover ~7 of 42 axiom patterns

---

## 1. Complete BX Axiom Catalog

### Layer 1: Propositional (4 axioms)

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| prop_k | Propositional K | `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))` | `((A \rightarrow (B \rightarrow C)) \rightarrow ((A \rightarrow B) \rightarrow (A \rightarrow C)))` | Testable |
| prop_s | Weakening | `phi -> (psi -> phi)` | `(A \rightarrow (B \rightarrow A))` | Testable |
| ex_falso | Ex Falso Quodlibet | `bot -> phi` | `(\bot \rightarrow A)` | Testable |
| peirce | Peirce's Law | `((phi -> psi) -> phi) -> phi` | `(((A \rightarrow B) \rightarrow A) \rightarrow A)` | Testable |

### Layer 2: S5 Modal (5 axioms)

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| modal_t | Reflexivity | `Box phi -> phi` | `(\Box A \rightarrow A)` | **Tested (implied by MD_TH_1)** |
| modal_4 | Transitivity | `Box phi -> Box Box phi` | `(\Box A \rightarrow \Box \Box A)` | Testable |
| modal_b | Symmetry | `phi -> Box Diamond phi` | `(A \rightarrow \Box \Diamond A)` | Testable |
| modal_5_collapse | S5 Characteristic | `Diamond Box phi -> Box phi` | `(\Diamond \Box A \rightarrow \Box A)` | Testable |
| modal_k_dist | K Distribution | `Box(phi -> psi) -> (Box phi -> Box psi)` | `(\Box (A \rightarrow B) \rightarrow (\Box A \rightarrow \Box B))` | **Tested (MD_TH_1)** |

### Layer 3: BX Temporal (22 axioms = 11 pairs)

#### BX1/BX1': Seriality

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| serial_future | Future Seriality | `top -> F(top)` | `(\top \rightarrow \future \top)` | Testable (strict semantics) |
| serial_past | Past Seriality | `top -> P(top)` | `(\top \rightarrow \past \top)` | Testable (strict semantics) |

#### BX2G/BX2H: Guard Monotonicity (Under G/H)

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| left_mono_until_G | Until Guard Mono | `G(phi -> chi) -> (U(psi, phi) -> U(psi, chi))` | `(\Future (A \rightarrow C) \rightarrow (\Until B A \rightarrow \Until B C))` | Testable |
| left_mono_since_H | Since Guard Mono | `H(phi -> chi) -> (S(psi, phi) -> S(psi, chi))` | `(\Past (A \rightarrow C) \rightarrow (\Since B A \rightarrow \Since B C))` | Testable |

#### BX3/BX3': Event Monotonicity

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| right_mono_until | Until Event Mono | `G(phi -> psi) -> (U(phi, chi) -> U(psi, chi))` | `(\Future (A \rightarrow B) \rightarrow (\Until A C \rightarrow \Until B C))` | Testable |
| right_mono_since | Since Event Mono | `H(phi -> psi) -> (S(phi, chi) -> S(psi, chi))` | `(\Past (A \rightarrow B) \rightarrow (\Since A C \rightarrow \Since B C))` | Testable |

#### BX4/BX4': Temporal Connectedness

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| connect_future | Future Connect | `phi -> G(P(phi))` | `(A \rightarrow \Future \past A)` | Testable |
| connect_past | Past Connect | `phi -> H(F(phi))` | `(A \rightarrow \Past \future A)` | Testable |

#### BX5/BX5': Self-Accumulation

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| self_accum_until | Until Self-Accum | `U(psi, phi) -> U(psi, phi and U(psi, phi))` | `(\Until B A \rightarrow \Until B (A \wedge \Until B A))` | Testable |
| self_accum_since | Since Self-Accum | `S(psi, phi) -> S(psi, phi and S(psi, phi))` | `(\Since B A \rightarrow \Since B (A \wedge \Since B A))` | Testable |

#### BX6/BX6': Absorption

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| absorb_until | Until Absorption | `U(phi and U(psi, phi), phi) -> U(psi, phi)` | `(\Until (A \wedge \Until B A) A \rightarrow \Until B A)` | Testable |
| absorb_since | Since Absorption | `S(phi and S(psi, phi), phi) -> S(psi, phi)` | `(\Since (A \wedge \Since B A) A \rightarrow \Since B A)` | Testable |

#### BX7/BX7': Linearity

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| linear_until | Until Linearity | `U(psi,phi) and U(theta,chi) -> U(psi and theta, phi and chi) or U(psi and chi, phi and chi) or U(phi and theta, phi and chi)` | Complex 4-variable formula | Testable (N>=4) |
| linear_since | Since Linearity | `S(psi,phi) and S(theta,chi) -> S(psi and theta, phi and chi) or S(psi and chi, phi and chi) or S(phi and theta, phi and chi)` | Complex 4-variable formula | Testable (N>=4) |

#### BX10/BX10': Eventuality Extraction

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| until_F | Until to F | `U(psi, phi) -> F(psi)` | `(\Until B A \rightarrow \future B)` | Testable |
| since_P | Since to P | `S(psi, phi) -> P(psi)` | `(\Since B A \rightarrow \past B)` | Testable |

#### BX11/BX11': Temporal Linearity

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| temp_linearity | F Linearity | `F(phi) and F(psi) -> F(phi and psi) or F(phi and F(psi)) or F(F(phi) and psi)` | `((\future A \wedge \future B) \rightarrow ((\future (A \wedge B)) \vee ((\future (A \wedge \future B)) \vee (\future (\future A \wedge B)))))` | Testable |
| temp_linearity_past | P Linearity | `P(phi) and P(psi) -> P(phi and psi) or P(phi and P(psi)) or P(P(phi) and psi)` | Similar past version | Testable |

#### BX12/BX12': F-Until/P-Since Bridge

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| F_until_equiv | F to Until | `F(phi) -> U(phi, top)` | `(\future A \rightarrow \Until A \top)` | Testable |
| P_since_equiv | P to Since | `P(phi) -> S(phi, top)` | `(\past A \rightarrow \Since A \top)` | Testable |

#### BX13/BX13': Enrichment

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| enrichment_until | Until Enrichment | `p and U(psi, phi) -> U(psi and S(p, phi), phi)` | Complex 3-variable formula | Testable |
| enrichment_since | Since Enrichment | `p and S(psi, phi) -> S(psi and U(p, phi), phi)` | Complex 3-variable formula | Testable |

### Layer 4: Modal-Temporal Interaction (1 axiom)

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| modal_future | Modal-Future | `Box phi -> Box(G phi)` | `(\Box A \rightarrow \Box \Future A)` | **Partially tested (BM_TH_5)** |

### Layer 5: Uniformity Axioms (5 axioms)

These axioms require ordered abelian group structure. U(top, bot) = "next top" witnesses immediate successor.

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| discrete_symm_fwd | Forward Symmetry | `U(top, bot) -> S(top, bot)` | `(\Until \top \bot \rightarrow \Since \top \bot)` | Requires discrete support |
| discrete_symm_bwd | Backward Symmetry | `S(top, bot) -> U(top, bot)` | `(\Since \top \bot \rightarrow \Until \top \bot)` | Requires discrete support |
| discrete_propagate_fwd | Forward Propagation | `U(top, bot) -> G(U(top, bot))` | `(\Until \top \bot \rightarrow \Future \Until \top \bot)` | Requires discrete support |
| discrete_propagate_bwd | Backward Propagation | `U(top, bot) -> H(U(top, bot))` | `(\Until \top \bot \rightarrow \Past \Until \top \bot)` | Requires discrete support |
| discrete_box_necessity | Box Necessity | `U(top, bot) -> Box(U(top, bot))` | `(\Until \top \bot \rightarrow \Box \Until \top \bot)` | Requires discrete support |

### Layer 6: Prior Axioms (2 axioms) - Discrete Only

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| prior_UZ | Prior-UZ | `F(phi) -> U(phi, neg phi)` | `(\future A \rightarrow \Until A \neg A)` | **Blocked** (discrete frames) |
| prior_SZ | Prior-SZ | `P(phi) -> S(phi, neg phi)` | `(\past A \rightarrow \Since A \neg A)` | **Blocked** (discrete frames) |

### Layer 7: Z1 Axiom (1 axiom) - Discrete Only

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| z1 | Z1 | `G(G phi -> phi) -> (F(G phi) -> G phi)` | `(\Future (\Future A \rightarrow A) \rightarrow ((\future \Future A) \rightarrow \Future A))` | **Blocked** (discrete frames) |

### Layer 8: Density Axioms (2 axioms) - Dense Only

| ID | Name | Formula | ModelChecker Syntax | Status |
|----|------|---------|---------------------|--------|
| density | Density | `G(G phi) -> G phi` | `(\Future \Future A \rightarrow \Future A)` | **Blocked** (dense frames, task 92) |
| dense_indicator | Dense Indicator | `neg U(top, bot)` | `\neg \Until \top \bot` | **Blocked** (dense frames, task 92) |

---

## 2. Current ModelChecker Coverage Analysis

### Currently Tested Patterns

From `examples.py`:

| Example ID | Formula Pattern | Maps to BX Axiom |
|------------|-----------------|------------------|
| MD_TH_1 | `Box(A -> B) -> (Box A -> Box B)` | **modal_k_dist** |
| TN_TH_2 | `A -> Future past A` | **connect_future** (BX4) |
| BM_TH_3 | `future A -> Diamond A` | Related to perpetuity |
| BM_TH_4 | `past A -> Diamond A` | Related to perpetuity |
| BM_TH_5 | `Box A -> Future Box A` | **modal_future** |

### Coverage Summary

| Layer | Total | Tested | Coverage |
|-------|-------|--------|----------|
| 1. Propositional | 4 | 0 | 0% |
| 2. S5 Modal | 5 | 1 | 20% |
| 3. BX Temporal | 22 | 1 | 5% |
| 4. Interaction | 1 | 1 | 100% |
| 5. Uniformity | 5 | 0 | 0% |
| 6. Prior | 2 | 0 | 0% (blocked) |
| 7. Z1 | 1 | 0 | 0% (blocked) |
| 8. Density | 2 | 0 | 0% (blocked) |
| **Total** | **42** | **3** | **7%** |

---

## 3. ModelChecker Syntax Translations

### Operator Mapping

| ProofChecker | ModelChecker | Notes |
|--------------|--------------|-------|
| `phi.imp psi` | `(A \rightarrow B)` | |
| `phi.neg` | `\neg A` | |
| `phi.and psi` | `(A \wedge B)` | |
| `phi.or psi` | `(A \vee B)` | |
| `Formula.bot` | `\bot` | |
| `Formula.top` | `\top` | Defined as `\neg \bot` |
| `Formula.box phi` | `\Box A` | |
| `phi.diamond` | `\Diamond A` | Defined |
| `Formula.untl phi psi` | `\Until A B` | Burgess: untl(event, guard) |
| `Formula.snce phi psi` | `\Since A B` | Burgess: snce(event, guard) |
| `phi.all_future` | `\Future A` | G operator |
| `phi.all_past` | `\Past A` | H operator |
| `phi.some_future` | `\future A` | F operator |
| `phi.some_past` | `\past A` | P operator |

### Ready-to-Test Axiom Examples

#### Propositional Layer (Priority: Low - trivially valid)

```python
# prop_k: Propositional K axiom
PROP_K_premises = []
PROP_K_conclusions = ['((A \\rightarrow (B \\rightarrow C)) \\rightarrow ((A \\rightarrow B) \\rightarrow (A \\rightarrow C)))']
PROP_K_settings = {'N': 3, 'M': 1, 'expectation': False}

# prop_s: Weakening
PROP_S_premises = []
PROP_S_conclusions = ['(A \\rightarrow (B \\rightarrow A))']
PROP_S_settings = {'N': 2, 'M': 1, 'expectation': False}

# ex_falso: Ex Falso Quodlibet
EX_FALSO_premises = []
EX_FALSO_conclusions = ['(\\bot \\rightarrow A)']
EX_FALSO_settings = {'N': 1, 'M': 1, 'expectation': False}

# peirce: Peirce's Law
PEIRCE_premises = []
PEIRCE_conclusions = ['(((A \\rightarrow B) \\rightarrow A) \\rightarrow A)']
PEIRCE_settings = {'N': 2, 'M': 1, 'expectation': False}
```

#### S5 Modal Layer (Priority: Medium)

```python
# modal_t: Reflexivity
MODAL_T_premises = []
MODAL_T_conclusions = ['(\\Box A \\rightarrow A)']
MODAL_T_settings = {'N': 1, 'M': 1, 'expectation': False}

# modal_4: Transitivity
MODAL_4_premises = []
MODAL_4_conclusions = ['(\\Box A \\rightarrow \\Box \\Box A)']
MODAL_4_settings = {'N': 1, 'M': 1, 'expectation': False}

# modal_b: Symmetry
MODAL_B_premises = []
MODAL_B_conclusions = ['(A \\rightarrow \\Box \\Diamond A)']
MODAL_B_settings = {'N': 1, 'M': 1, 'expectation': False}

# modal_5_collapse: S5 Characteristic
MODAL_5_premises = []
MODAL_5_conclusions = ['(\\Diamond \\Box A \\rightarrow \\Box A)']
MODAL_5_settings = {'N': 1, 'M': 2, 'expectation': False}
```

#### BX Temporal Layer (Priority: High - Now Testable)

```python
# BX1: serial_future
BX1_premises = []
BX1_conclusions = ['(\\top \\rightarrow \\future \\top)']
BX1_settings = {'N': 1, 'M': 2, 'expectation': False}

# BX1': serial_past
BX1P_premises = []
BX1P_conclusions = ['(\\top \\rightarrow \\past \\top)']
BX1P_settings = {'N': 1, 'M': 2, 'expectation': False}

# BX4: connect_future
BX4_premises = []
BX4_conclusions = ['(A \\rightarrow \\Future \\past A)']
BX4_settings = {'N': 1, 'M': 3, 'expectation': False}

# BX4': connect_past
BX4P_premises = []
BX4P_conclusions = ['(A \\rightarrow \\Past \\future A)']
BX4P_settings = {'N': 1, 'M': 3, 'expectation': False}

# BX10: until_F
BX10_premises = []
BX10_conclusions = ['(\\Until B A \\rightarrow \\future B)']
BX10_settings = {'N': 2, 'M': 3, 'expectation': False}

# BX10': since_P
BX10P_premises = []
BX10P_conclusions = ['(\\Since B A \\rightarrow \\past B)']
BX10P_settings = {'N': 2, 'M': 3, 'expectation': False}

# BX12: F_until_equiv
BX12_premises = []
BX12_conclusions = ['(\\future A \\rightarrow \\Until A \\top)']
BX12_settings = {'N': 1, 'M': 3, 'expectation': False}

# BX12': P_since_equiv
BX12P_premises = []
BX12P_conclusions = ['(\\past A \\rightarrow \\Since A \\top)']
BX12P_settings = {'N': 1, 'M': 3, 'expectation': False}

# BX5: self_accum_until
BX5_premises = []
BX5_conclusions = ['(\\Until B A \\rightarrow \\Until B (A \\wedge \\Until B A))']
BX5_settings = {'N': 2, 'M': 4, 'expectation': False}

# BX6: absorb_until
BX6_premises = []
BX6_conclusions = ['(\\Until (A \\wedge \\Until B A) A \\rightarrow \\Until B A)']
BX6_settings = {'N': 2, 'M': 4, 'expectation': False}

# BX11: temp_linearity (requires 2 propositions)
BX11_premises = []
BX11_conclusions = ['((\\future A \\wedge \\future B) \\rightarrow ((\\future (A \\wedge B)) \\vee ((\\future (A \\wedge \\future B)) \\vee (\\future (\\future A \\wedge B)))))']
BX11_settings = {'N': 2, 'M': 4, 'expectation': False}
```

---

## 4. Implementation Plan Sketch

### Phase 1: Propositional + Modal S5 (Easy)

**Scope**: 9 axioms (4 propositional + 5 modal)
**Blockers**: None
**Settings**: `N: 1-3, M: 1-2`
**Effort**: Low

Add test cases for:
- prop_k, prop_s, ex_falso, peirce
- modal_t, modal_4, modal_b, modal_5_collapse, modal_k_dist

### Phase 2: Basic BX Temporal (Medium)

**Scope**: 12 axioms
- Seriality: serial_future, serial_past
- Connectedness: connect_future, connect_past
- Eventuality: until_F, since_P
- Bridge: F_until_equiv, P_since_equiv
- Monotonicity: left_mono_until_G, left_mono_since_H, right_mono_until, right_mono_since

**Blockers**: None (Until/Since implemented in task 89)
**Settings**: `N: 1-2, M: 3-4`
**Effort**: Medium

### Phase 3: Advanced BX Temporal (Medium-High)

**Scope**: 8 axioms
- Self-accumulation: self_accum_until, self_accum_since
- Absorption: absorb_until, absorb_since
- Linearity: temp_linearity, temp_linearity_past
- Enrichment: enrichment_until, enrichment_since

**Blockers**: None
**Settings**: `N: 2-4, M: 4-5`
**Effort**: Medium-High (complex formulas, nested Until/Since)

### Phase 4: BX7 Linearity (High Complexity)

**Scope**: 2 axioms
- linear_until (4 variables)
- linear_since (4 variables)

**Blockers**: None, but high computational cost
**Settings**: `N: 4, M: 5-6, max_time: 60+`
**Effort**: High

### Phase 5: Uniformity Axioms (Requires Task 91)

**Scope**: 5 axioms
**Blockers**: Discrete frame class support (task 91/92)
**Status**: BLOCKED

### Phase 6: Prior + Z1 (Requires Task 91)

**Scope**: 3 axioms
**Blockers**: Discrete frame class support
**Status**: BLOCKED

### Phase 7: Density Axioms (Requires Task 92)

**Scope**: 2 axioms
**Blockers**: Dense frame class support
**Status**: BLOCKED

---

## 5. Blockers Identified

### Frame Class Support (Tasks 91/92)

The following axiom groups require frame class-specific semantics:

| Frame Class | Axioms | Count | Blocking Task |
|-------------|--------|-------|---------------|
| Discrete | uniformity (5), prior (2), z1 (1) | 8 | Task 91 |
| Dense | density (2) | 2 | Task 92 |

**Total Blocked**: 10 of 42 axioms (24%)

### Current Testable Without Blockers

32 axioms (76%) are testable with current implementation:
- 4 propositional
- 5 S5 modal
- 22 BX temporal
- 1 modal-temporal interaction

---

## 6. Recommended Test Organization

```python
# Suggested structure in examples.py

# === Layer 1: Propositional ===
PROP_K_example = [...]
PROP_S_example = [...]
EX_FALSO_example = [...]
PEIRCE_example = [...]

# === Layer 2: S5 Modal ===
MODAL_T_example = [...]
MODAL_4_example = [...]
MODAL_B_example = [...]
MODAL_5_example = [...]
MODAL_K_example = [...]  # Already tested as MD_TH_1

# === Layer 3: BX Temporal ===
BX1_SERIAL_F_example = [...]
BX1P_SERIAL_P_example = [...]
BX2G_LEFT_MONO_U_example = [...]
BX2H_LEFT_MONO_S_example = [...]
BX3_RIGHT_MONO_U_example = [...]
BX3P_RIGHT_MONO_S_example = [...]
BX4_CONNECT_F_example = [...]
BX4P_CONNECT_P_example = [...]
BX5_ACCUM_U_example = [...]
BX5P_ACCUM_S_example = [...]
BX6_ABSORB_U_example = [...]
BX6P_ABSORB_S_example = [...]
BX7_LINEAR_U_example = [...]
BX7P_LINEAR_S_example = [...]
BX10_UNTIL_F_example = [...]
BX10P_SINCE_P_example = [...]
BX11_TEMP_LIN_F_example = [...]
BX11P_TEMP_LIN_P_example = [...]
BX12_F_UNTIL_example = [...]
BX12P_P_SINCE_example = [...]
BX13_ENRICH_U_example = [...]
BX13P_ENRICH_S_example = [...]

# === Layer 4: Modal-Temporal ===
MF_MODAL_FUTURE_example = [...]  # Already tested as BM_TH_5

# === Blocked (Frame Classes) ===
# Layer 5: Uniformity - requires discrete support
# Layer 6: Prior - requires discrete support
# Layer 7: Z1 - requires discrete support
# Layer 8: Density - requires dense support
```

---

## 7. Summary

### Coverage After Implementation

| Phase | Axioms Added | Cumulative Coverage |
|-------|--------------|---------------------|
| Current | 3 | 7% (3/42) |
| Phase 1 | +6 | 21% (9/42) |
| Phase 2 | +12 | 50% (21/42) |
| Phase 3 | +8 | 69% (29/42) |
| Phase 4 | +2 | 74% (31/42) |
| (Blocked) | +10 | 98% (41/42) |
| modal_future (already) | +1 | 100% (42/42) |

### Priority Recommendation

1. **Immediate** (Phases 1-2): Add 18 basic axiom tests
2. **Near-term** (Phases 3-4): Add 10 advanced axiom tests
3. **Blocked** (Phases 5-7): Await frame class support from tasks 91/92

### Expected Outcome

After Phases 1-4, ModelChecker will test 74% of the BX axiom system (31/42 axioms), providing comprehensive validation of the proof system against the model checker semantics.
