"""Tests for Z3OracleProvider and bimodal oracle pipeline, rewritten against the
witness-family certificate encoding.

This module tests the Z3OracleProvider class from bimodal_logic, verifying:
1. Provider property contracts (provider_id, version, frame_classes, capabilities)
2. find_countermodel() output contract (keys, types, values) against the
   certificate-derived shape
3. State isolation (100 sequential calls produce consistent results)
4. formula_folded_json presence and validity
5. Example regression via the standard pipeline (all bimodal examples now
   decide correctly with no exclusion list -- see examples.py and
   test_bimodal.py's own empty KNOWN_TIMEOUT_EXAMPLES/UNSTABLE_EXAMPLES)
6. Never-claims-validity: a genuine timeout raises OracleTimeoutError, never a
   silent None

Test Classes:
    TestProviderProperties:    Static property contracts
    TestFindCountermodelContract:  Output structure contracts
    TestValidateSelf:              validate_self() behavior
    TestStateIsolation:            100-call isolation tests
    TestFormulaFoldedJson:         formula_folded_json output
    TestOracleExampleRegression:   Full-suite regression via the standard pipeline
    TestOracleOutputCompleteness:  Output completeness for SAT results
"""

from __future__ import annotations

import re

import pytest

from bimodal_logic import OracleTimeoutError, Z3OracleProvider
from model_checker.theory_lib.bimodal.examples import (
    countermodel_examples,
    theorem_examples,
)


##############################################################################
# Test fixtures: JSON formula helpers
##############################################################################

# A simple SAT formula: "A or B" -- negation has countermodel where both are false
# In the oracle, we check invalidity: find a countermodel for the formula itself.
# atom("A") is invalid (has countermodel where A is false).
SIMPLE_SAT_JSON = {"tag": "atom", "name": "A"}

# A tautology in JSON form: A => A -- no countermodel possible
# Note: {"tag": "top"} expands to (bot -> bot) which triggers a
# NegationOperator interface mismatch in BimodalSemantics, so we use
# the equivalent implication tautology instead.
SIMPLE_UNSAT_JSON = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "A"},
    "right": {"tag": "atom", "name": "A"},
}

# A SAT formula with temporal operators (depth=1): F(A) -- "some_future A"
# This has a countermodel: a model where A is false at all times.
FUTURE_SAT_JSON = {"tag": "some_future", "arg": {"tag": "atom", "name": "A"}}

# Another SAT formula: (A => B) -- has countermodel where A true, B false
IMP_SAT_JSON = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "A"},
    "right": {"tag": "atom", "name": "B"},
}

# A tautology: (A => A)
TAUTOLOGY_IMP_JSON = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "A"},
    "right": {"tag": "atom", "name": "A"},
}

# Already-enriched input (uses enriched "neg" tag directly)
ENRICHED_NEG_JSON = {
    "tag": "neg",
    "arg": {"tag": "atom", "name": "A"},
}

# Primitive-only atom formula
PRIMITIVE_ATOM_JSON = {"tag": "atom", "name": "p"}


##############################################################################
# Phase 1: Provider Properties
##############################################################################

class TestProviderProperties:
    """Tests for static Z3OracleProvider property contracts."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_provider_id(self):
        """provider_id must be exactly 'bmlogic_z3_base_v1'."""
        assert self.provider.provider_id == "bmlogic_z3_base_v1"

    def test_supported_frame_classes(self):
        """supported_frame_classes must be frozenset({'ZTime'}) -- the
        certificate encoding's own scope (discrete time only); "Base" (the
        retired encoding's TaskFrame-axiom label) is no longer meaningful and
        is no longer accepted."""
        assert self.provider.supported_frame_classes == frozenset({"ZTime"})

    def test_capabilities_dict(self):
        """capabilities must be a dict with required keys: back/mid/fwd caps
        in place of the retired encoding's max_N/max_M."""
        caps = self.provider.capabilities
        assert isinstance(caps, dict)
        required_keys = {
            "max_back", "max_mid", "max_fwd",
            "supports_enriched_tags", "z3_timeout_configurable",
        }
        for key in required_keys:
            assert key in caps, f"Missing capability key: {key}"

    def test_provider_version_semver(self):
        """provider_version must match semver pattern (X.Y.Z)."""
        version = self.provider.provider_version
        assert isinstance(version, str)
        assert re.match(r'^\d+\.\d+\.\d+', version), (
            f"provider_version '{version}' does not match semver pattern"
        )

    def test_semantics_version(self):
        """semantics_version must be a non-empty string."""
        sv = self.provider.semantics_version
        assert isinstance(sv, str)
        assert len(sv) > 0, "semantics_version must be non-empty"


##############################################################################
# Phase 1: find_countermodel Contract
##############################################################################

class TestFindCountermodelContract:
    """Tests for find_countermodel() output contract."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_unsupported_frame_class_returns_none(self):
        """Passing an unsupported frame_class (including the retired "Base")
        returns None immediately."""
        assert self.provider.find_countermodel(SIMPLE_SAT_JSON, frame_class="Foo") is None
        assert self.provider.find_countermodel(SIMPLE_SAT_JSON, frame_class="Base") is None

    def test_sat_formula_returns_dict(self):
        """A known-invalid (SAT) formula returns a dict."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result, dict)

    def test_unsat_formula_returns_none(self):
        """A tautology (no certificate found) returns None."""
        result = self.provider.find_countermodel(SIMPLE_UNSAT_JSON)
        assert result is None

    def test_result_has_required_keys(self):
        """SAT result must contain all required output keys."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        required_keys = {
            "temporal_depth",
            "segment_lengths",
            "semantics_version",
            "formula_folded_json",
            "trueAtoms",
            "falseAtoms",
            "certificate",
            "lasso_count",
        }
        for key in required_keys:
            assert key in result, f"Missing required key: {key}"

    def test_segment_lengths_shape(self):
        """segment_lengths must carry back/mid/fwd, all non-negative ints
        with back/fwd >= 1 (WitnessRegistry's own back_ne/fwd_ne invariant)."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        seg = result["segment_lengths"]
        assert set(seg.keys()) == {"back", "mid", "fwd"}
        assert seg["back"] >= 1
        assert seg["fwd"] >= 1
        assert seg["mid"] >= 0

    def test_formula_folded_json_present(self):
        """formula_folded_json must be a dict (not None, not missing)."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result["formula_folded_json"], dict)

    def test_certificate_has_wire_shape(self):
        """certificate must be the exact WitnessFamily.to_json wire shape
        (target/bx/lassos) -- the same shape BimodalLogic's own
        `lake exe check_certificate` accepts, so a caller can pass this field
        straight through with no translation layer."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        cert = result["certificate"]
        assert set(cert.keys()) == {"target", "bx", "lassos"}
        assert "premises" in cert["target"]
        assert "conclusions" in cert["target"]
        assert "time" in cert["target"]
        assert isinstance(cert["lassos"], list)
        assert len(cert["lassos"]) == result["lasso_count"]
        for lasso in cert["lassos"]:
            assert set(lasso.keys()) == {"back", "mid", "fwd"}

    def test_temporal_depth_is_nonneg_int(self):
        """temporal_depth in result must be a non-negative integer."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result["temporal_depth"], int)
        assert result["temporal_depth"] >= 0

    def test_trueAtoms_and_falseAtoms_are_lists(self):
        """trueAtoms and falseAtoms must be lists of dicts with 'name' key."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result["trueAtoms"], list)
        assert isinstance(result["falseAtoms"], list)
        for atom in result["trueAtoms"] + result["falseAtoms"]:
            assert "name" in atom, f"Atom dict missing 'name': {atom}"

    def test_lasso_count_is_positive(self):
        """lasso_count must be at least 1 (the main lasso) for SAT results."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result["lasso_count"], int)
        assert result["lasso_count"] >= 1

    def test_semantics_version_matches_provider(self):
        """result semantics_version must match provider.semantics_version."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert result["semantics_version"] == self.provider.semantics_version

    def test_imp_sat_returns_dict(self):
        """Implication A => B (SAT) returns a dict countermodel."""
        result = self.provider.find_countermodel(IMP_SAT_JSON)
        assert result is not None
        assert isinstance(result, dict)

    def test_tautology_imp_returns_none(self):
        """Tautology A => A returns None."""
        result = self.provider.find_countermodel(TAUTOLOGY_IMP_JSON)
        assert result is None

    def test_future_sat_returns_dict(self):
        """some_future(A) (SAT -- A false everywhere) returns a dict."""
        result = self.provider.find_countermodel(FUTURE_SAT_JSON)
        assert result is not None
        assert isinstance(result, dict)

    def test_rlimit_exhausted_raises_oracle_timeout_error(self):
        """A search that cannot complete within its deterministic resource
        budget raises OracleTimeoutError.

        This is the three-valued contract: `None` must mean exclusively
        "proven no countermodel" (no certificate found), never "the solver
        gave up". The certificate encoding is quantifier-free and decides
        every example in well under 100ms (measured directly), so a
        wall-clock `timeout_ms` budget can no longer be relied on to force a
        genuine timeout the way the retired encoding's deeply-nested-formula
        fixture did. `max_rlimit=1` (a near-zero, load-independent resource
        budget) is used instead: no search, however trivial, can complete in
        one Z3 resource unit.
        """
        with pytest.raises(OracleTimeoutError):
            self.provider.find_countermodel(SIMPLE_SAT_JSON, max_rlimit=1)


##############################################################################
# Phase 1: validate_self
##############################################################################

class TestValidateSelf:
    """Tests for validate_self() behavior."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_validate_self_with_known_invalid(self):
        """validate_self() with known-invalid formulas returns True."""
        spot_check = [SIMPLE_SAT_JSON, IMP_SAT_JSON]
        result = self.provider.validate_self(spot_check)
        assert result is True

    def test_validate_self_with_tautology_fails(self):
        """validate_self() with a tautology returns False (can't find countermodel)."""
        spot_check = [TAUTOLOGY_IMP_JSON]
        result = self.provider.validate_self(spot_check)
        assert result is False

    def test_validate_self_empty_list_returns_true(self):
        """validate_self() with empty list returns True (vacuously)."""
        result = self.provider.validate_self([])
        assert result is True

    def test_validate_self_mixed_returns_false(self):
        """validate_self() with mix of SAT and UNSAT returns False."""
        spot_check = [SIMPLE_SAT_JSON, TAUTOLOGY_IMP_JSON]
        result = self.provider.validate_self(spot_check)
        assert result is False


##############################################################################
# Phase 4: State Isolation
##############################################################################

class TestStateIsolation:
    """Tests that 100 sequential calls produce consistent, isolated results."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_100_sequential_sat_calls(self):
        """100 sequential SAT calls all return non-None with consistent structure."""
        first_result = None
        for i in range(100):
            result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
            assert result is not None, f"Call {i}: expected non-None for SAT formula"
            assert isinstance(result, dict), f"Call {i}: expected dict"
            # All calls should have same keys
            assert "temporal_depth" in result
            assert "certificate" in result
            if first_result is None:
                first_result = result
            # Atom sets should be consistent
            assert set(a["name"] for a in result["trueAtoms"] + result["falseAtoms"]) == \
                   set(a["name"] for a in first_result["trueAtoms"] + first_result["falseAtoms"]), \
                   f"Call {i}: atom sets differ"

    def test_100_sequential_unsat_calls(self):
        """100 sequential UNSAT calls all return None."""
        for i in range(100):
            result = self.provider.find_countermodel(SIMPLE_UNSAT_JSON)
            assert result is None, f"Call {i}: expected None for UNSAT formula"

    def test_100_mixed_calls(self):
        """Interleaved SAT and UNSAT calls return correct results."""
        formulas = [SIMPLE_SAT_JSON, SIMPLE_UNSAT_JSON, TAUTOLOGY_IMP_JSON, IMP_SAT_JSON]
        # first and last should be SAT, middle two UNSAT
        expected = [True, False, False, True]  # True=SAT (non-None), False=UNSAT (None)
        for i in range(25):  # 25 rounds = 100 total calls
            for formula, exp_sat in zip(formulas, expected):
                result = self.provider.find_countermodel(formula)
                if exp_sat:
                    assert result is not None, f"Round {i}: SAT formula returned None"
                else:
                    assert result is None, f"Round {i}: UNSAT formula returned non-None"

    def test_no_semantics_reference_leak(self):
        """After find_countermodel(), provider._semantics is None (no reference leak)."""
        self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert self.provider._semantics is None, (
            "provider._semantics should be None after find_countermodel() exits"
        )


##############################################################################
# Phase 4: formula_folded_json
##############################################################################

class TestFormulaFoldedJson:
    """Tests for formula_folded_json output in find_countermodel() results."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_folded_json_present_in_sat_result(self):
        """formula_folded_json key exists in SAT result."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert "formula_folded_json" in result

    def test_folded_json_is_valid_formula(self):
        """formula_folded_json must have a 'tag' key (valid formula dict)."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        folded = result["formula_folded_json"]
        assert isinstance(folded, dict)
        assert "tag" in folded, "formula_folded_json must have 'tag' key"

    def test_folded_json_for_primitive_input(self):
        """fold_formula on atom input returns atom (idempotent primitive)."""
        result = self.provider.find_countermodel(PRIMITIVE_ATOM_JSON)
        assert result is not None
        folded = result["formula_folded_json"]
        # atom passes through fold unchanged
        assert folded["tag"] == "atom"
        assert folded["name"] == "p"

    def test_folded_json_for_enriched_input(self):
        """fold_formula is idempotent: enriched input stays enriched."""
        # ENRICHED_NEG_JSON = neg(A) - already enriched, should pass through
        # neg(A) has a countermodel where A=True (neg(A) is false there), so
        # the oracle (checking invalidity of neg(A)) should find one.
        result = self.provider.find_countermodel(ENRICHED_NEG_JSON)
        assert result is not None, "Expected a countermodel for neg(A) (documented SAT), got None"
        folded = result["formula_folded_json"]
        assert isinstance(folded, dict)
        assert "tag" in folded


##############################################################################
# Phase 5: Full-Suite Regression via the Standard Pipeline
##############################################################################
#
# The retired encoding excluded ten examples from this regression (solver-cost
# and boundary-vacuity reasons). The certificate encoding has no exclusion
# list at all -- test_bimodal.py's own KNOWN_TIMEOUT_EXAMPLES/UNSTABLE_EXAMPLES
# are both empty sets -- so this regression now covers every example
# unconditionally.

_all_examples = {**countermodel_examples, **theorem_examples}


def _run_oracle_on_example(example_case: list) -> bool | None:
    """Run the standard pipeline on an example and check if result matches expectation.

    Returns True if z3_model_status == settings['expectation'] (correct result),
    False if they disagree, None if not solved.
    """
    from model_checker import Syntax, ModelConstraints, run_test
    from model_checker.theory_lib.bimodal import (
        BimodalSemantics, BimodalProposition, BimodalStructure, bimodal_operators
    )
    from model_checker.utils.context import isolated_z3_context

    with isolated_z3_context():
        result = run_test(
            example_case,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )
    return result


class TestOracleExampleRegression:
    """Regression test: every active example passes through the standard pipeline
    with no exclusions."""

    def test_active_example_count(self):
        """The full corpus is 53 examples (confirm at implementation time rather
        than trusting this number to stay fixed as examples are added)."""
        assert len(_all_examples) == 53, (
            f"Expected 53 examples in the full corpus, got {len(_all_examples)}. "
            f"Update this count if examples were added/removed."
        )

    @pytest.mark.parametrize(
        "example_name, example_case",
        list(_all_examples.items()),
    )
    def test_regression_standard_pipeline(self, example_name, example_case):
        """Standard pipeline produces correct SAT/UNSAT for every active example.

        run_test() returns True when z3_model_status matches the expected
        'expectation' setting (both SAT when expectation=True, or both UNSAT
        when expectation=False).
        """
        result = _run_oracle_on_example(example_case)
        assert result is True, (
            f"Standard pipeline regression failure for '{example_name}': "
            f"expected expectation={example_case[2]['expectation']}, run_test returned {result}"
        )


class TestOracleOutputCompleteness:
    """Tests for completeness of oracle output for SAT results."""

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_all_sat_results_have_complete_output(self):
        """SAT results must have all required output keys."""
        required_keys = {
            "temporal_depth", "segment_lengths",
            "semantics_version", "formula_folded_json",
            "trueAtoms", "falseAtoms", "certificate", "lasso_count",
        }
        sat_formulas = [SIMPLE_SAT_JSON, IMP_SAT_JSON, FUTURE_SAT_JSON]
        for formula in sat_formulas:
            result = self.provider.find_countermodel(formula)
            assert result is not None, f"Expected SAT result for {formula}"
            for key in required_keys:
                assert key in result, (
                    f"SAT result missing key '{key}' for formula {formula}"
                )

    def test_temporal_depth_in_output(self):
        """temporal_depth in output is a non-negative integer."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert isinstance(result["temporal_depth"], int)
        assert result["temporal_depth"] >= 0

    def test_certificate_nonempty_lassos(self):
        """certificate must contain at least one lasso for SAT results."""
        result = self.provider.find_countermodel(SIMPLE_SAT_JSON)
        assert result is not None
        assert len(result["certificate"]["lassos"]) >= 1, (
            "SAT result certificate must have at least one lasso"
        )
