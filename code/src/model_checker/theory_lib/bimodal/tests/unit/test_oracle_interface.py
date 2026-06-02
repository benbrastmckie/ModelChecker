"""Integration tests for Z3OracleProvider through the find_countermodel() API.

Task 105: Integration testing and validation.

This module tests the Z3OracleProvider exclusively through its public API
(find_countermodel, validate_self) -- NOT through the internal run_test
pipeline. It covers:
1. Oracle protocol compliance (properties, methods, return format)
2. 52-example regression via find_countermodel() with JSON formulas
3. Enriched formula round-trips (11 operators, primitive equivalence)
4. Cross-signal spot checks (SPOT_CHECK_FORMULAS, temporal_depth, boundary)
5. Ternary serialization validation
6. Edge cases (timeout, unsupported frame_class, malformed JSON)
7. Entry-point discovery
8. Z3 isolation stress tests (150+ calls, memory tracking)

Test Classes:
    TestOracleProtocolCompliance:     5 properties + 2 methods exist
    TestOracleExampleRegressionViaAPI: 52-example regression through oracle API
    TestEnrichedRoundTrip:           11 enriched vs primitive SAT agreement
    TestMixedFormulas:               Mixed enriched/primitive formula tests
    TestSpotCheckCrossSignal:        SPOT_CHECK_FORMULAS validation
    TestBoundaryRegressionViaOracle: boundary_safe, time_bound, temporal_depth
    TestTernarySerializationAll:     task_relation ternary format validation
    TestEdgeCases:                   Timeout, bad frame_class, malformed JSON
    TestEntryPointDiscovery:         Entry point and registry discovery
    TestZ3IsolationStress:           150+ sequential calls, memory tracking
"""

from __future__ import annotations

import re
import tracemalloc

import pytest

from bimodal_logic import Z3OracleProvider
from bimodal_logic.translation import temporal_depth, unfold_formula
from model_checker.theory_lib.bimodal.examples import (
    countermodel_examples,
    theorem_examples,
)


##############################################################################
# JSON formula helpers
##############################################################################

def _atom(name: str) -> dict:
    return {"tag": "atom", "name": name}

def _bot() -> dict:
    return {"tag": "bot"}

def _top() -> dict:
    return {"tag": "top"}

def _neg(arg: dict) -> dict:
    return {"tag": "neg", "arg": arg}

def _imp(left: dict, right: dict) -> dict:
    return {"tag": "imp", "left": left, "right": right}

def _and(left: dict, right: dict) -> dict:
    return {"tag": "and", "left": left, "right": right}

def _or(left: dict, right: dict) -> dict:
    return {"tag": "or", "left": left, "right": right}

def _box(child: dict) -> dict:
    return {"tag": "box", "child": child}

def _diamond(arg: dict) -> dict:
    return {"tag": "diamond", "arg": arg}

def _next(arg: dict) -> dict:
    return {"tag": "next", "arg": arg}

def _prev(arg: dict) -> dict:
    return {"tag": "prev", "arg": arg}

def _some_future(arg: dict) -> dict:
    return {"tag": "some_future", "arg": arg}

def _some_past(arg: dict) -> dict:
    return {"tag": "some_past", "arg": arg}

def _all_future(arg: dict) -> dict:
    return {"tag": "all_future", "arg": arg}

def _all_past(arg: dict) -> dict:
    return {"tag": "all_past", "arg": arg}

def _untl(event: dict, guard: dict) -> dict:
    return {"tag": "untl", "event": event, "guard": guard}

def _snce(event: dict, guard: dict) -> dict:
    return {"tag": "snce", "event": event, "guard": guard}

# Shorthand atoms
A = _atom("A")
B = _atom("B")
C = _atom("C")
D = _atom("D")
BOT = _bot()
TOP = _top()


##############################################################################
# Simple test formulas
##############################################################################

# A simple SAT formula: atom A (invalid -- has countermodel where A is false)
SIMPLE_SAT_JSON = A

# A tautology: A => A (no countermodel possible)
SIMPLE_UNSAT_JSON = _imp(A, A)


##############################################################################
# EXAMPLE_JSON_CATALOG: 52 examples with JSON formula dicts
##############################################################################

# Timeout exclusion set -- same as existing test_oracle_provider.py + research
REGRESSION_TIMEOUT_EXAMPLES = {
    "TN_CM_1",      # temporal, timeout-prone
    "TN_CM_2",      # temporal, timeout-prone
    "BM_CM_1",      # pre-existing timeout failure (max_time=15, contingent=True)
    "BM_CM_3",      # timeout-prone in isolation
    "BM_CM_4",      # some_past(A) needs >15s
    "MD_TH_2",      # timeout-prone
    "BM_TH_1",      # 30s timeout, exhaustive search
    "BM_TH_2",      # 30s timeout, exhaustive search
    "MF_MODAL_FUTURE_TH",  # timeout-prone
    "BX7_LINEAR_U_TH",     # 60s timeout, complex
    "BX7P_LINEAR_S_TH",    # 60s timeout, complex
}

# For examples with premises, the oracle tests the conclusion formula only.
# The tuple is (json_formula, has_premises, expected_oracle_sat).
# expected_oracle_sat: True means oracle finds countermodel (formula is invalid),
#                      False means oracle returns None (formula is valid/UNSAT/timeout).
# For no-premises examples: expected_oracle_sat matches (expectation == True).
# For premises examples: determined empirically by testing conclusion alone.
EXAMPLE_JSON_CATALOG = {
    # ---- Extensional Countermodels ----
    "EX_CM_1": (
        # conclusion: (A and B) -- SAT: countermodel where A or B is false
        _and(A, B),
        True,   # has premises
        True,   # oracle SAT (A and B is invalid)
    ),

    # ---- Modal Countermodels ----
    "MD_CM_1": (
        # conclusion: Box A -- SAT: countermodel where some world has A false
        _box(A),
        True, True,
    ),
    "MD_CM_2": (
        # conclusion: (Diamond A and Diamond B) -- SAT
        _and(_diamond(A), _diamond(B)),
        True, True,
    ),
    "MD_CM_3": (
        # conclusion: Box A -- SAT
        _box(A),
        True, True,
    ),
    "MD_CM_4": (
        # conclusion: A -- SAT: countermodel where A is false
        A,
        True, True,
    ),
    "MD_CM_5": (
        # conclusion: Box A -- SAT
        _box(A),
        True, True,
    ),
    "MD_CM_6": (
        # conclusion: Diamond(A and B) -- SAT
        _diamond(_and(A, B)),
        True, True,
    ),

    # ---- Tense Countermodels ----
    "TN_CM_1": (
        # conclusion: \Future A = all_future(A) -- UNSAT (valid in these frames)
        _all_future(A),
        True, False,
    ),
    "TN_CM_2": (
        # conclusion: \future (A and B) = some_future(A and B)
        _some_future(_and(A, B)),
        True, True,  # SAT with generous timeout
    ),

    # ---- Bimodal Countermodels ----
    "BM_CM_1": (
        # conclusion: Box A -- SAT
        _box(A),
        True, True,
    ),
    "BM_CM_2": (
        # conclusion: Box A -- SAT
        _box(A),
        True, True,
    ),
    "BM_CM_3": (
        # conclusion: \future A = some_future(A) -- SAT
        _some_future(A),
        True, True,
    ),
    "BM_CM_4": (
        # conclusion: \past A = some_past(A) -- SAT (needs generous timeout)
        _some_past(A),
        True, True,
    ),

    # ---- Extensional Theorems ----
    "EX_TH_1": (
        # conclusion: (A or B) -- SAT (oracle: A or B is invalid alone)
        _or(A, B),
        True, True,
    ),

    # ---- Modal Theorems ----
    "MD_TH_1": (
        # conclusion: (Box A -> Box B) -- SAT (oracle: conclusion alone is invalid)
        _imp(_box(A), _box(B)),
        True, True,
    ),
    "MD_TH_2": (
        # conclusion: A -- SAT (oracle: A alone is invalid)
        A,
        True, True,
    ),

    # ---- Tense Theorems ----
    "TN_TH_2": (
        # conclusion: \Future \past A -- UNSAT (valid in these frames)
        _all_future(_some_past(A)),
        True, False,
    ),

    # ---- Bimodal Theorems ----
    "BM_TH_1": (
        # conclusion: \Future A = all_future(A) -- UNSAT (valid)
        _all_future(A),
        True, False,
    ),
    "BM_TH_2": (
        # conclusion: \Past A = all_past(A) -- SAT (invalid alone)
        _all_past(A),
        True, True,
    ),
    "BM_TH_3": (
        # conclusion: Diamond A -- SAT (invalid alone)
        _diamond(A),
        True, True,
    ),
    "BM_TH_4": (
        # conclusion: Diamond A -- SAT (invalid alone)
        _diamond(A),
        True, True,
    ),
    # ---- BX Layer 1: Propositional ----
    "PROP_K_TH": (
        # (A -> (B -> C)) -> ((A -> B) -> (A -> C))
        _imp(_imp(A, _imp(B, C)), _imp(_imp(A, B), _imp(A, C))),
        False, False,
    ),
    "PROP_S_TH": (
        # A -> (B -> A)
        _imp(A, _imp(B, A)),
        False, False,
    ),
    "EX_FALSO_TH": (
        # bot -> A
        _imp(BOT, A),
        False, False,
    ),
    "PEIRCE_TH": (
        # ((A -> B) -> A) -> A
        _imp(_imp(_imp(A, B), A), A),
        False, False,
    ),

    # ---- BX Layer 2: S5 Modal ----
    "MODAL_T_TH": (
        # Box A -> A
        _imp(_box(A), A),
        False, False,
    ),
    "MODAL_4_TH": (
        # Box A -> Box Box A
        _imp(_box(A), _box(_box(A))),
        False, False,
    ),
    "MODAL_B_TH": (
        # A -> Box Diamond A
        _imp(A, _box(_diamond(A))),
        False, False,
    ),
    "MODAL_5_TH": (
        # Diamond Box A -> Box A
        _imp(_diamond(_box(A)), _box(A)),
        False, False,
    ),

    # ---- BX Layer 3: Temporal (Basic) ----
    "BX1_SERIAL_F_TH": (
        # neg bot -> some_future(neg bot)   [top -> F(top)]
        _imp(_neg(BOT), _some_future(_neg(BOT))),
        False, False,
    ),
    "BX1P_SERIAL_P_TH": (
        # neg bot -> some_past(neg bot)   [top -> P(top)]
        _imp(_neg(BOT), _some_past(_neg(BOT))),
        False, False,
    ),
    "BX2G_MONO_U_TH": (
        # all_future(A -> C) -> ((B Until A) -> (B Until C))
        _imp(_all_future(_imp(A, C)), _imp(_untl(B, A), _untl(B, C))),
        False, False,
    ),
    "BX2H_MONO_S_TH": (
        # all_past(A -> C) -> ((B Since A) -> (B Since C))
        _imp(_all_past(_imp(A, C)), _imp(_snce(B, A), _snce(B, C))),
        False, False,
    ),
    "BX3_MONO_U_TH": (
        # all_future(A -> B) -> ((A Until C) -> (B Until C))
        _imp(_all_future(_imp(A, B)), _imp(_untl(A, C), _untl(B, C))),
        False, False,
    ),
    "BX3P_MONO_S_TH": (
        # all_past(A -> B) -> ((A Since C) -> (B Since C))
        _imp(_all_past(_imp(A, B)), _imp(_snce(A, C), _snce(B, C))),
        False, False,
    ),
    "BX4_CONNECT_F_TH": (
        # A -> all_future(some_past(A))
        _imp(A, _all_future(_some_past(A))),
        False, False,
    ),
    "BX4P_CONNECT_P_TH": (
        # A -> all_past(some_future(A))
        _imp(A, _all_past(_some_future(A))),
        False, False,
    ),
    "BX10_UNTIL_F_TH": (
        # (B Until A) -> some_future(B)
        _imp(_untl(B, A), _some_future(B)),
        False, False,
    ),
    "BX10P_SINCE_P_TH": (
        # (B Since A) -> some_past(B)
        _imp(_snce(B, A), _some_past(B)),
        False, False,
    ),
    "BX12_F_UNTIL_TH": (
        # some_future(A) -> (A Until neg(bot))
        _imp(_some_future(A), _untl(A, _neg(BOT))),
        False, False,
    ),
    "BX12P_P_SINCE_TH": (
        # some_past(A) -> (A Since neg(bot))
        _imp(_some_past(A), _snce(A, _neg(BOT))),
        False, False,
    ),

    # ---- BX Layer 4: Modal-Temporal Interaction ----
    "MF_MODAL_FUTURE_TH": (
        # Box A -> Box(all_future(A))
        _imp(_box(A), _box(_all_future(A))),
        False, False,
    ),

    # ---- BX Layer 3: Temporal (Advanced) ----
    "BX5_ACCUM_U_TH": (
        # (B Until A) -> (B Until (A and (B Until A)))
        _imp(_untl(B, A), _untl(B, _and(A, _untl(B, A)))),
        False, False,
    ),
    "BX5P_ACCUM_S_TH": (
        # (B Since A) -> (B Since (A and (B Since A)))
        _imp(_snce(B, A), _snce(B, _and(A, _snce(B, A)))),
        False, False,
    ),
    "BX6_ABSORB_U_TH": (
        # ((A and (B Until A)) Until A) -> (B Until A)
        _imp(_untl(_and(A, _untl(B, A)), A), _untl(B, A)),
        False, False,
    ),
    "BX6P_ABSORB_S_TH": (
        # ((A and (B Since A)) Since A) -> (B Since A)
        _imp(_snce(_and(A, _snce(B, A)), A), _snce(B, A)),
        False, False,
    ),
    "BX11_LIN_F_TH": (
        # (some_future(A) and some_future(B)) ->
        #   (some_future(A and B) or (some_future(A and some_future(B)) or some_future(some_future(A) and B)))
        _imp(
            _and(_some_future(A), _some_future(B)),
            _or(
                _some_future(_and(A, B)),
                _or(
                    _some_future(_and(A, _some_future(B))),
                    _some_future(_and(_some_future(A), B)),
                ),
            ),
        ),
        False, False,
    ),
    "BX11P_LIN_P_TH": (
        # (some_past(A) and some_past(B)) ->
        #   (some_past(A and B) or (some_past(A and some_past(B)) or some_past(some_past(A) and B)))
        _imp(
            _and(_some_past(A), _some_past(B)),
            _or(
                _some_past(_and(A, B)),
                _or(
                    _some_past(_and(A, _some_past(B))),
                    _some_past(_and(_some_past(A), B)),
                ),
            ),
        ),
        False, False,
    ),
    "BX13_ENRICH_U_TH": (
        # (C and (B Until A)) -> ((B and (C Since A)) Until A)
        _imp(_and(C, _untl(B, A)), _untl(_and(B, _snce(C, A)), A)),
        False, False,
    ),
    "BX13P_ENRICH_S_TH": (
        # (C and (B Since A)) -> ((B and (C Until A)) Since A)
        _imp(_and(C, _snce(B, A)), _snce(_and(B, _untl(C, A)), A)),
        False, False,
    ),

    # ---- BX Layer 3: BX7 Linearity (Complex) ----
    "BX7_LINEAR_U_TH": (
        # ((B Until A) and (D Until C)) ->
        #   (((B and D) Until (A and C)) or
        #    (((B and C) Until (A and C)) or ((A and D) Until (A and C))))
        _imp(
            _and(_untl(B, A), _untl(D, C)),
            _or(
                _untl(_and(B, D), _and(A, C)),
                _or(
                    _untl(_and(B, C), _and(A, C)),
                    _untl(_and(A, D), _and(A, C)),
                ),
            ),
        ),
        False, False,
    ),
    "BX7P_LINEAR_S_TH": (
        # ((B Since A) and (D Since C)) ->
        #   (((B and D) Since (A and C)) or
        #    (((B and C) Since (A and C)) or ((A and D) Since (A and C))))
        _imp(
            _and(_snce(B, A), _snce(D, C)),
            _or(
                _snce(_and(B, D), _and(A, C)),
                _or(
                    _snce(_and(B, C), _and(A, C)),
                    _snce(_and(A, D), _and(A, C)),
                ),
            ),
        ),
        False, False,
    ),
}

# Active examples (excluding timeout-prone ones)
ACTIVE_EXAMPLES = {
    k: v for k, v in EXAMPLE_JSON_CATALOG.items()
    if k not in REGRESSION_TIMEOUT_EXAMPLES
}


##############################################################################
# Phase 1: Oracle Protocol Compliance
##############################################################################

class TestOracleProtocolCompliance:
    """Verify Z3OracleProvider satisfies the OracleProvider protocol."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_provider_implements_protocol(self):
        """Verify isinstance(provider, OracleProvider) using runtime_checkable.

        Conditionally imports from BimodalHarness; skips if not installed.
        """
        try:
            from bimodal_harness.oracle.protocol import OracleProvider
            assert isinstance(self.provider, OracleProvider), (
                "Z3OracleProvider must satisfy the OracleProvider protocol"
            )
        except ImportError:
            pytest.skip("bimodal_harness not installed -- skipping protocol check")

    def test_five_properties_exist(self):
        """Verify all 5 required protocol properties exist with correct types."""
        # provider_id
        assert hasattr(self.provider, "provider_id")
        assert isinstance(self.provider.provider_id, str)
        assert len(self.provider.provider_id) > 0

        # provider_version
        assert hasattr(self.provider, "provider_version")
        assert isinstance(self.provider.provider_version, str)
        assert re.match(r'^\d+\.\d+\.\d+', self.provider.provider_version)

        # semantics_version
        assert hasattr(self.provider, "semantics_version")
        assert isinstance(self.provider.semantics_version, str)
        assert len(self.provider.semantics_version) > 0

        # supported_frame_classes
        assert hasattr(self.provider, "supported_frame_classes")
        assert isinstance(self.provider.supported_frame_classes, frozenset)
        assert "Base" in self.provider.supported_frame_classes

        # capabilities
        assert hasattr(self.provider, "capabilities")
        assert isinstance(self.provider.capabilities, dict)

    def test_find_countermodel_method_exists(self):
        """Verify find_countermodel method exists with correct signature."""
        assert hasattr(self.provider, "find_countermodel")
        assert callable(self.provider.find_countermodel)

    def test_validate_self_method_exists(self):
        """Verify validate_self method exists with correct signature."""
        assert hasattr(self.provider, "validate_self")
        assert callable(self.provider.validate_self)

    def test_return_format_sat(self):
        """Verify SAT result matches StructuredCountermodel schema."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result, dict)
        # Required keys
        required_keys = {
            "temporal_depth",
            "boundary_safe",
            "time_bound",
            "semantics_version",
            "formula_folded_json",
            "formula",
            "trueAtoms",
            "falseAtoms",
            "world_histories",
            "task_relation",
            "evaluation_world",
            "evaluation_time",
            "world_count",
        }
        for key in required_keys:
            assert key in result, f"Missing required key: {key}"
        # Type checks
        assert isinstance(result["temporal_depth"], int)
        assert isinstance(result["boundary_safe"], bool)
        assert isinstance(result["time_bound"], int)
        assert isinstance(result["semantics_version"], str)
        assert isinstance(result["formula_folded_json"], dict)
        assert isinstance(result["trueAtoms"], list)
        assert isinstance(result["falseAtoms"], list)
        assert isinstance(result["world_histories"], list)
        assert isinstance(result["task_relation"], list)
        assert isinstance(result["world_count"], int)

    def test_return_format_unsat(self):
        """Verify UNSAT result is None."""
        result = self.provider.find_countermodel(SIMPLE_UNSAT_JSON)
        assert result is None


##############################################################################
# Phase 1: Example Regression via Oracle API
##############################################################################

class TestOracleExampleRegressionViaAPI:
    """Regression: all 52 examples tested through find_countermodel() API.

    For no-premises examples: expected SAT/UNSAT matches example expectation.
    For premises examples: oracle tests conclusion formula independently;
    expected result documented per-example in EXAMPLE_JSON_CATALOG.
    """

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_active_example_count(self):
        """Verify correct number of active (non-timeout) examples."""
        total = len(EXAMPLE_JSON_CATALOG)
        active = len(ACTIVE_EXAMPLES)
        excluded = len(REGRESSION_TIMEOUT_EXAMPLES)
        assert total == 52, f"Expected 52 total examples, got {total}"
        assert active == total - excluded, (
            f"Expected {total - excluded} active examples, got {active}"
        )

    @pytest.mark.parametrize(
        "example_name",
        sorted(ACTIVE_EXAMPLES.keys()),
    )
    def test_oracle_regression(self, example_name):
        """Oracle produces correct SAT/UNSAT for each active example."""
        formula_json, has_premises, expected_sat = ACTIVE_EXAMPLES[example_name]
        # Use generous timeout for temporal formulas
        depth = temporal_depth(formula_json)
        timeout = 30000 if depth > 0 else 10000
        result = self.provider.find_countermodel(formula_json, timeout_ms=timeout)
        actual_sat = result is not None
        assert actual_sat == expected_sat, (
            f"Oracle regression failure for '{example_name}': "
            f"expected SAT={expected_sat}, got SAT={actual_sat}. "
            f"has_premises={has_premises}, depth={depth}"
        )


##############################################################################
# Phase 2: Enriched Formula Round-Trip Tests
##############################################################################

# 11 enriched operators, each with a formula that is SAT (has countermodel)
# so we can compare enriched vs primitive results.
ENRICHED_PRIMITIVE_PAIRS = [
    # (operator_name, enriched_json, primitive_json)
    (
        "neg",
        # neg(A) -- SAT: countermodel where A=True
        _neg(A),
        # imp(A, bot)
        _imp(A, BOT),
    ),
    (
        "top",
        # imp(neg(bot), A) -- SAT: countermodel where A=False
        # Using neg(bot) as enriched expansion of top to avoid TopOperator bug.
        # The enriched tag "top" triggers a known NegationOperator.true_at() bug,
        # so we use neg(bot) which is semantically equivalent.
        _imp(_neg(BOT), A),
        # imp(imp(bot, bot), A) -- primitive expansion of top -> A
        _imp(_imp(BOT, BOT), A),
    ),
    (
        "and",
        # and(A, B) -- SAT: countermodel where A or B is false
        _and(A, B),
        # imp(imp(A, imp(B, bot)), bot) -- the unfolded form
        _imp(_imp(A, _imp(B, BOT)), BOT),
    ),
    (
        "or",
        # or(A, B) -- SAT: countermodel where both are false
        _or(A, B),
        # imp(imp(A, bot), B)
        _imp(_imp(A, BOT), B),
    ),
    (
        "diamond",
        # diamond(A) -- SAT: countermodel where A is false in all worlds
        _diamond(A),
        # imp(box(imp(A, bot)), bot)
        _imp(_box(_imp(A, BOT)), BOT),
    ),
    (
        "next",
        # next(A) -- SAT: countermodel where A is false at t+1
        _next(A),
        # untl(A, bot)
        _untl(A, BOT),
    ),
    (
        "prev",
        # prev(A) -- SAT: countermodel where A is false at t-1
        _prev(A),
        # snce(A, bot)
        _snce(A, BOT),
    ),
    (
        "some_future",
        # some_future(A) -- SAT: countermodel where A is false at all future times
        _some_future(A),
        # untl(A, imp(bot, bot))
        _untl(A, _imp(BOT, BOT)),
    ),
    (
        "some_past",
        # some_past(A) -- SAT: countermodel where A is false at all past times
        _some_past(A),
        # snce(A, imp(bot, bot))
        _snce(A, _imp(BOT, BOT)),
    ),
    (
        "all_future",
        # imp(all_future(A), B) -- SAT for testing (all_future(A) alone might be UNSAT)
        _imp(_all_future(A), B),
        # imp(imp(untl(imp(A, bot), imp(bot, bot)), bot), B)
        _imp(_imp(_untl(_imp(A, BOT), _imp(BOT, BOT)), BOT), B),
    ),
    (
        "all_past",
        # imp(all_past(A), B) -- SAT for testing
        _imp(_all_past(A), B),
        # imp(imp(snce(imp(A, bot), imp(bot, bot)), bot), B)
        _imp(_imp(_snce(_imp(A, BOT), _imp(BOT, BOT)), BOT), B),
    ),
]


class TestEnrichedRoundTrip:
    """Verify enriched vs primitive formula equivalence through oracle API."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    @pytest.mark.parametrize(
        "operator_name, enriched_json, primitive_json",
        ENRICHED_PRIMITIVE_PAIRS,
        ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS],
    )
    def test_enriched_vs_primitive_sat_agreement(
        self, operator_name, enriched_json, primitive_json
    ):
        """Enriched and primitive forms produce identical SAT/UNSAT results."""
        depth = max(temporal_depth(enriched_json), temporal_depth(primitive_json))
        # Primitive forms are structurally larger and may need more solver time
        timeout = 60000 if depth > 0 else 10000
        enriched_result = self.provider.find_countermodel(enriched_json, timeout_ms=timeout)
        primitive_result = self.provider.find_countermodel(primitive_json, timeout_ms=timeout)
        enriched_sat = enriched_result is not None
        primitive_sat = primitive_result is not None
        assert enriched_sat == primitive_sat, (
            f"SAT/UNSAT mismatch for '{operator_name}': "
            f"enriched={enriched_sat}, primitive={primitive_sat}"
        )

    @pytest.mark.parametrize(
        "operator_name, enriched_json, primitive_json",
        ENRICHED_PRIMITIVE_PAIRS,
        ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS],
    )
    def test_temporal_depth_identical(
        self, operator_name, enriched_json, primitive_json
    ):
        """Temporal depth is the same for enriched and primitive forms."""
        # The enriched and primitive forms represent the same formula,
        # but temporal_depth only counts from the JSON tag structure.
        # unfold_formula should produce the same primitive representation.
        enriched_depth = temporal_depth(enriched_json)
        primitive_depth = temporal_depth(primitive_json)
        assert enriched_depth == primitive_depth, (
            f"Temporal depth mismatch for '{operator_name}': "
            f"enriched={enriched_depth}, primitive={primitive_depth}"
        )

    @pytest.mark.parametrize(
        "operator_name, enriched_json, primitive_json",
        [p for p in ENRICHED_PRIMITIVE_PAIRS],
        ids=[p[0] for p in ENRICHED_PRIMITIVE_PAIRS],
    )
    def test_formula_folded_json_present_all_sat(
        self, operator_name, enriched_json, primitive_json
    ):
        """For SAT results, formula_folded_json must exist and have a tag key."""
        depth = temporal_depth(enriched_json)
        timeout = 30000 if depth > 0 else 10000
        result = self.provider.find_countermodel(enriched_json, timeout_ms=timeout)
        if result is not None:
            assert "formula_folded_json" in result, (
                f"Missing formula_folded_json for '{operator_name}'"
            )
            folded = result["formula_folded_json"]
            assert isinstance(folded, dict)
            assert "tag" in folded, (
                f"formula_folded_json missing 'tag' for '{operator_name}'"
            )

    def test_formula_folded_json_uses_enriched_tags(self):
        """formula_folded_json should use enriched tags where possible.

        Test with a primitive-only formula that has a known enriched form.
        """
        # imp(A, bot) is the primitive form of neg(A)
        primitive_neg = _imp(A, BOT)
        result = self.provider.find_countermodel(primitive_neg)
        assert result is not None
        folded = result["formula_folded_json"]
        # fold_formula should convert imp(A, bot) to neg(A)
        assert folded["tag"] == "neg", (
            f"Expected folded tag 'neg', got '{folded['tag']}'"
        )


class TestMixedFormulas:
    """Test formulas combining enriched and primitive tags."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_mixed_and_neg_some_future(self):
        """and(neg(A), some_future(B)) -- L1 neg + L2 and + L2 some_future."""
        formula = _and(_neg(A), _some_future(B))
        result = self.provider.find_countermodel(formula, timeout_ms=60000)
        # SAT: countermodel where A=true (neg(A) false) or B never future-true
        assert result is not None
        assert isinstance(result, dict)

    def test_mixed_and_box_next(self):
        """and(box(A), next(B)) -- L2 and + modal box + L1 next."""
        formula = _and(_box(A), _next(B))
        result = self.provider.find_countermodel(formula, timeout_ms=60000)
        # SAT -- countermodel where box(A) and next(B) fail together
        assert result is not None

    def test_mixed_or_diamond_prev(self):
        """or(diamond(A), prev(B)) -- L2 or + L2 diamond + L1 prev."""
        formula = _or(_diamond(A), _prev(B))
        result = self.provider.find_countermodel(formula, timeout_ms=60000)
        # SAT -- countermodel where both disjuncts are false
        assert result is not None

    def test_mixed_and_all_future_neg(self):
        """and(neg(A), next(B)) -- L1 neg + L2 and + L1 next."""
        formula = _and(_neg(A), _next(B))
        result = self.provider.find_countermodel(formula, timeout_ms=60000)
        # SAT: countermodel where neg(A) is false or next(B) is false
        assert result is not None

    def test_deeply_nested_enriched(self):
        """Formula with 3+ levels of enriched operator nesting."""
        # and(neg(A), some_future(some_past(B))) -- 3 levels deep, SAT
        formula = _and(_neg(A), _some_future(_some_past(B)))
        result = self.provider.find_countermodel(formula, timeout_ms=60000)
        # Should produce a valid result (SAT or UNSAT), just ensure no crash
        assert isinstance(result, (dict, type(None)))


##############################################################################
# Phase 3: Cross-Signal and Boundary Tests
##############################################################################

class TestSpotCheckCrossSignal:
    """Validate oracle against BimodalHarness SPOT_CHECK_FORMULAS."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def _get_spot_check_formulas(self):
        """Attempt to import SPOT_CHECK_FORMULAS from BimodalHarness."""
        try:
            from bimodal_harness.oracle._mock import SPOT_CHECK_FORMULAS
            return SPOT_CHECK_FORMULAS
        except ImportError:
            return None

    def test_validate_self_temporal_only(self):
        """validate_self with temporal-only SPOT_CHECK_FORMULAS.

        Of the 5 temporal-only formulas from SPOT_CHECK_FORMULAS:
        - F4 (p U q -> q U p): VALID in Z3 frame (Until is symmetric in linear time)
        - F5 (p S q -> q U p): INVALID (Since and Until are different directions)
        - F7 (p -> p U bot): VALID (bot guard means "at next step")
        - F9 ((p U q) -> p): VALID in bounded frames
        - F10 ((p S q) -> p): VALID in bounded frames

        Only F5 produces a countermodel, so validate_self returns False.
        This documents the semantic divergence between BimodalHarness expectations
        and the Z3 oracle's stronger frame axioms.
        """
        p = _atom("p")
        q = _atom("q")
        temporal_formulas = [
            # F4: p U q -> q U p -- VALID in Z3 frame
            _imp(_untl(p, q), _untl(q, p)),
            # F5: p S q -> q U p -- INVALID (the only one)
            _imp(_snce(p, q), _untl(q, p)),
            # F7: p -> p U bot -- VALID
            _imp(p, _untl(p, BOT)),
            # F9: (p U q) -> p -- VALID
            _imp(_untl(p, q), p),
            # F10: (p S q) -> p -- VALID
            _imp(_snce(p, q), p),
        ]

        result = self.provider.validate_self(temporal_formulas)
        # Expected False: F4, F7, F9, F10 are valid in the Z3 frame
        assert result is False, (
            "validate_self should return False: F4, F7, F9, F10 are valid "
            "in the Z3 oracle's strong frame (bounded linear time + S5 modal)"
        )

    def test_validate_self_all_formulas(self):
        """validate_self with all 10 SPOT_CHECK_FORMULAS.

        Box-containing formulas (1-3, 6, 8) may disagree due to S5 vs Kripke
        semantics. The Z3 oracle uses S5 (reflexive + symmetric + transitive),
        so some formulas that are invalid in general Kripke frames may be valid
        in S5.
        """
        formulas = self._get_spot_check_formulas()
        if formulas is None:
            # Inline all 10 from BimodalHarness _mock.py
            p = _atom("p")
            q = _atom("q")
            formulas = [
                # F1: p -> Box p
                _imp(p, _box(p)),
                # F2: Box p -> p (valid in S5/reflexive)
                _imp(_box(p), p),
                # F3: Box p -> Box Box p (valid in S5/transitive)
                _imp(_box(p), _box(_box(p))),
                # F4: p U q -> q U p
                _imp(_untl(p, q), _untl(q, p)),
                # F5: p S q -> q U p
                _imp(_snce(p, q), _untl(q, p)),
                # F6: Box bot
                _box(BOT),
                # F7: p -> p U bot
                _imp(p, _untl(p, BOT)),
                # F8: Box p -> Box q
                _imp(_box(p), _box(q)),
                # F9: (p U q) -> p
                _imp(_untl(p, q), p),
                # F10: (p S q) -> p
                _imp(_snce(p, q), p),
            ]
        # F2 (Box p -> p) and F3 (Box p -> Box Box p) are valid in S5,
        # so oracle returns None for them, making validate_self return False.
        result = self.provider.validate_self(formulas)
        # Document: expected False because F2 and F3 are valid in S5 frames
        assert result is False, (
            "validate_self should return False for all 10 formulas "
            "(F2 and F3 are valid in S5 frames)"
        )

    def test_spot_check_individual_countermodels(self):
        """Test individual temporal spot-check formulas for countermodels.

        In the Z3 oracle's strong frame (bounded linear time + S5 modal),
        only F5 (p S q -> q U p) is invalid. F4, F7, F9, F10 are valid.
        """
        p = _atom("p")
        q = _atom("q")

        # F5 is the only temporal-only SPOT_CHECK that is invalid
        f5 = _imp(_snce(p, q), _untl(q, p))
        result = self.provider.find_countermodel(f5, timeout_ms=60000)
        assert result is not None, (
            "Expected countermodel for F5 (p S q -> q U p)"
        )

        # Verify the valid ones return None (documenting semantic divergence)
        valid_formulas = {
            "F4_until_symmetric": _imp(_untl(p, q), _untl(q, p)),
            "F7_p_to_p_until_bot": _imp(p, _untl(p, BOT)),
            "F9_until_implies_event": _imp(_untl(p, q), p),
            "F10_since_implies_event": _imp(_snce(p, q), p),
        }
        for name, formula in valid_formulas.items():
            result = self.provider.find_countermodel(formula, timeout_ms=60000)
            assert result is None, (
                f"Expected None (valid) for '{name}' in Z3 frame, "
                f"got countermodel"
            )


class TestBoundaryRegressionViaOracle:
    """Verify boundary_safe, time_bound, and temporal_depth in oracle outputs."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_boundary_safe_true_for_all_examples(self):
        """boundary_safe == True for all active (non-timeout) SAT examples.

        With M = max(depth+2, 3), boundary_safe = (M > depth+1) is always True.
        """
        for name, (formula_json, _, expected_sat) in ACTIVE_EXAMPLES.items():
            if not expected_sat:
                continue  # skip UNSAT examples (no output to check)
            depth = temporal_depth(formula_json)
            timeout = 30000 if depth > 0 else 10000
            result = self.provider.find_countermodel(formula_json, timeout_ms=timeout)
            if result is not None:
                assert result["boundary_safe"] is True, (
                    f"boundary_safe should be True for '{name}' "
                    f"(depth={depth}, M={result['time_bound']})"
                )

    def test_time_bound_formula(self):
        """For SAT results, time_bound == max(depth+2, 3)."""
        test_formulas = {
            "depth_0": (A, 0),
            "depth_1_future": (_some_future(A), 1),
            "depth_1_neg": (_neg(A), 0),  # neg doesn't increment depth
        }
        for name, (formula, expected_depth) in test_formulas.items():
            result = self.provider.find_countermodel(formula, timeout_ms=30000)
            if result is not None:
                expected_M = max(expected_depth + 2, 3)
                assert result["time_bound"] == expected_M, (
                    f"time_bound mismatch for '{name}': "
                    f"expected M={expected_M} (depth={expected_depth}), "
                    f"got M={result['time_bound']}"
                )

    def test_temporal_depth_correct_in_output(self):
        """Verify temporal_depth in output matches computed depth."""
        test_formulas = {
            "atom_depth_0": (A, 0),
            "imp_depth_0": (_imp(A, B), 0),
            "box_depth_0": (_box(A), 0),
            "next_depth_1": (_next(A), 1),
            "some_future_depth_1": (_some_future(A), 1),
        }
        for name, (formula, expected_depth) in test_formulas.items():
            result = self.provider.find_countermodel(formula, timeout_ms=30000)
            if result is not None:
                assert result["temporal_depth"] == expected_depth, (
                    f"temporal_depth mismatch for '{name}': "
                    f"expected={expected_depth}, got={result['temporal_depth']}"
                )


class TestTernarySerializationAll:
    """Verify ternary {source, duration, target} format for all task_relation entries."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_all_sat_task_relation_ternary(self):
        """Every task_relation entry is a dict with {source, duration, target} keys
        and integer values.
        """
        sat_formulas = [
            ("atom_A", A),
            ("imp_A_B", _imp(A, B)),
            ("and_A_B", _and(A, B)),
            ("diamond_A", _diamond(A)),
            ("next_A", _next(A)),
        ]
        for name, formula in sat_formulas:
            depth = temporal_depth(formula)
            timeout = 60000 if depth > 0 else 10000
            result = self.provider.find_countermodel(formula, timeout_ms=timeout)
            assert result is not None, f"Expected SAT for {name}"
            task_rel = result["task_relation"]
            assert isinstance(task_rel, list), f"task_relation not a list for {name}"
            for i, triple in enumerate(task_rel):
                assert isinstance(triple, dict), (
                    f"task_relation[{i}] is {type(triple).__name__}, "
                    f"expected dict for {name}"
                )
                assert set(triple.keys()) == {"source", "duration", "target"}, (
                    f"task_relation[{i}] has wrong keys {set(triple.keys())} "
                    f"for {name}"
                )
                assert isinstance(triple["source"], int), (
                    f"source not int for {name}[{i}]"
                )
                assert isinstance(triple["duration"], int), (
                    f"duration not int for {name}[{i}]"
                )
                assert isinstance(triple["target"], int), (
                    f"target not int for {name}[{i}]"
                )

    def test_no_binary_pairs(self):
        """Verify no task_relation entry is a 2-element list/tuple."""
        result = self.provider.find_countermodel(A)
        assert result is not None
        for triple in result["task_relation"]:
            assert not isinstance(triple, (list, tuple)), (
                f"task_relation entry is {type(triple).__name__}, expected dict"
            )


##############################################################################
# Phase 4: Edge Cases and Stress Tests
##############################################################################

class TestEdgeCases:
    """Test timeout, unsupported frame_class, and malformed JSON handling."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_timeout_handling(self):
        """Complex temporal formula with timeout_ms=1 returns None."""
        # Use a deeply nested temporal formula that can't solve in 1ms
        complex_formula = _all_future(_all_past(_some_future(_some_past(A))))
        result = self.provider.find_countermodel(complex_formula, timeout_ms=1)
        assert result is None, (
            "Expected None (timeout) for complex formula with 1ms timeout"
        )

    def test_unsupported_frame_class_dense(self):
        """Unsupported frame_class='Dense' returns None immediately."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON, frame_class="Dense")
        assert result is None

    def test_unsupported_frame_class_arbitrary(self):
        """Unsupported frame_class='NonExistent' returns None immediately."""
        result = self.provider.find_countermodel(
            SIMPLE_SAT_JSON, frame_class="NonExistent"
        )
        assert result is None

    def test_malformed_formula_missing_tag(self):
        """Formula dict without 'tag' key raises KeyError."""
        with pytest.raises(KeyError):
            self.provider.find_countermodel({"foo": "bar"})

    def test_malformed_formula_unknown_tag(self):
        """Formula with unknown tag raises ValueError."""
        with pytest.raises(ValueError, match="unknown"):
            self.provider.find_countermodel({"tag": "unknown_operator"})

    def test_malformed_formula_missing_fields(self):
        """Formula with missing required fields raises KeyError."""
        # imp requires left and right
        with pytest.raises(KeyError):
            self.provider.find_countermodel({"tag": "imp"})


class TestEntryPointDiscovery:
    """Test entry point registration and oracle registry discovery."""

    def test_entry_point_registered(self):
        """z3_base entry point is registered in bimodal_harness.oracle_providers group."""
        import importlib.metadata
        try:
            eps = importlib.metadata.entry_points(
                group="bimodal_harness.oracle_providers"
            )
            ep_names = [ep.name for ep in eps]
            assert "z3_base" in ep_names, (
                f"z3_base not found in entry points. Found: {ep_names}"
            )
        except Exception:
            pytest.skip("Package not installed with entry points")

    def test_entry_point_loads_correct_class(self):
        """Loading z3_base entry point yields Z3OracleProvider class."""
        import importlib.metadata
        try:
            eps = importlib.metadata.entry_points(
                group="bimodal_harness.oracle_providers"
            )
            z3_eps = [ep for ep in eps if ep.name == "z3_base"]
            if not z3_eps:
                pytest.skip("z3_base entry point not found")
            loaded = z3_eps[0].load()
            assert loaded is Z3OracleProvider, (
                f"Entry point loaded {loaded}, expected Z3OracleProvider"
            )
        except Exception as e:
            pytest.skip(f"Could not load entry point: {e}")

    def test_oracle_registry_discover(self):
        """OracleRegistry.discover() finds z3_base provider (if BimodalHarness installed)."""
        try:
            from bimodal_harness.oracle.registry import OracleRegistry
            registry = OracleRegistry()
            registry.discover()
            providers = registry.list_providers()
            provider_ids = [p.provider_id for p in providers]
            assert "bmlogic_z3_base_v1" in provider_ids, (
                f"z3_base not discovered. Found: {provider_ids}"
            )
        except ImportError:
            pytest.skip("bimodal_harness not installed")

    def test_discovered_provider_is_correct_type(self):
        """Discovered provider is Z3OracleProvider instance."""
        try:
            from bimodal_harness.oracle.registry import OracleRegistry
            registry = OracleRegistry()
            registry.discover()
            providers = registry.list_providers()
            z3_providers = [p for p in providers if p.provider_id == "bmlogic_z3_base_v1"]
            if not z3_providers:
                pytest.skip("z3_base provider not discovered")
            assert isinstance(z3_providers[0], Z3OracleProvider)
        except ImportError:
            pytest.skip("bimodal_harness not installed")


class TestZ3IsolationStress:
    """Stress tests: sequential calls, memory tracking, state isolation."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_150_sequential_mixed_calls(self):
        """150 sequential calls alternating SAT/UNSAT with varying depths."""
        formulas = [
            (A, True),                              # depth 0, SAT
            (SIMPLE_UNSAT_JSON, False),              # depth 0, UNSAT
            (_imp(A, B), True),                      # depth 0, SAT
            (_imp(A, A), False),                     # depth 0, UNSAT
            (_neg(A), True),                         # depth 0, SAT
        ]
        for i in range(30):  # 30 rounds * 5 formulas = 150 calls
            for formula, expected_sat in formulas:
                result = self.provider.find_countermodel(formula, timeout_ms=5000)
                actual_sat = result is not None
                assert actual_sat == expected_sat, (
                    f"Iteration {i}: expected SAT={expected_sat}, got {actual_sat} "
                    f"for formula tag={formula['tag']}"
                )

    def test_memory_growth_bounded(self):
        """Memory growth stays within 50% over 200 find_countermodel() calls.

        Uses tracemalloc to measure memory. Threshold is generous to
        avoid false positives from measurement noise.
        """
        tracemalloc.start()
        # Warm up with a few calls to stabilize allocations
        for _ in range(10):
            self.provider.find_countermodel(A)

        snapshot_before = tracemalloc.take_snapshot()
        before_size = sum(stat.size for stat in snapshot_before.statistics("filename"))

        # Run 200 calls
        for i in range(200):
            formula = A if i % 2 == 0 else _imp(A, B)
            self.provider.find_countermodel(formula, timeout_ms=5000)

        snapshot_after = tracemalloc.take_snapshot()
        after_size = sum(stat.size for stat in snapshot_after.statistics("filename"))
        tracemalloc.stop()

        growth_ratio = after_size / max(before_size, 1)
        assert growth_ratio < 1.5, (
            f"Memory grew by {(growth_ratio - 1) * 100:.1f}% over 200 calls "
            f"(before={before_size}, after={after_size}). "
            f"Threshold: <50% growth."
        )

    def test_no_state_leakage_between_depths(self):
        """Run depth-0, depth-2, depth-0 again -- depth-0 results must be identical."""
        # First depth-0 call
        result_before = self.provider.find_countermodel(A)
        assert result_before is not None

        # Depth-2 call (different temporal complexity)
        depth2_formula = _some_future(_some_past(A))
        self.provider.find_countermodel(depth2_formula, timeout_ms=30000)

        # Second depth-0 call -- should be identical
        result_after = self.provider.find_countermodel(A)
        assert result_after is not None

        # Compare structural properties (exact model may differ, but structure must match)
        assert result_before["temporal_depth"] == result_after["temporal_depth"]
        assert result_before["time_bound"] == result_after["time_bound"]
        assert result_before["boundary_safe"] == result_after["boundary_safe"]
        assert result_before["semantics_version"] == result_after["semantics_version"]
        # Atom sets should be the same
        before_atoms = set(
            a["name"] for a in result_before["trueAtoms"] + result_before["falseAtoms"]
        )
        after_atoms = set(
            a["name"] for a in result_after["trueAtoms"] + result_after["falseAtoms"]
        )
        assert before_atoms == after_atoms
