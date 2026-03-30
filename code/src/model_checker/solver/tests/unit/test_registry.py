"""Tests for solver registry and backend selection."""

import os
import pytest

from model_checker.solver import (
    get_active_backend,
    set_cli_backend,
    clear_cli_backend,
    detect_z3,
    detect_cvc5,
    validate_backend,
    list_available_backends,
)
from model_checker.solver.registry import reset_registry


@pytest.fixture(autouse=True)
def reset_state():
    """Reset registry state before and after each test."""
    reset_registry()
    yield
    reset_registry()


class TestBackendDetection:
    """Tests for backend availability detection."""

    def test_detect_z3_returns_true(self):
        """Z3 should always be available in test environment."""
        assert detect_z3() is True

    def test_detect_cvc5_returns_bool(self):
        """detect_cvc5 should return a boolean."""
        result = detect_cvc5()
        assert isinstance(result, bool)

    def test_list_available_backends(self):
        """list_available_backends should return dict with z3 and cvc5."""
        backends = list_available_backends()
        assert "z3" in backends
        assert "cvc5" in backends
        assert backends["z3"] is True  # Z3 should be available


class TestBackendSelection:
    """Tests for backend selection priority."""

    def test_default_backend_is_z3(self):
        """Default backend should be z3 when no overrides."""
        assert get_active_backend() == "z3"

    def test_cli_override_takes_priority(self):
        """CLI flag should override all other settings."""
        set_cli_backend("z3")
        assert get_active_backend() == "z3"

        # Even with different settings, CLI takes priority
        assert get_active_backend({"solver": "cvc5"}) == "z3"

    def test_settings_used_when_no_cli_override(self):
        """Settings should be used when no CLI override."""
        clear_cli_backend()
        assert get_active_backend({"solver": "cvc5"}) == "cvc5"

    def test_environment_variable_override(self, monkeypatch):
        """Environment variable should override settings but not CLI."""
        clear_cli_backend()
        monkeypatch.setenv("MODEL_CHECKER_SOLVER", "cvc5")

        # Env var overrides settings
        assert get_active_backend({"solver": "z3"}) == "cvc5"

        # But CLI still takes priority
        set_cli_backend("z3")
        assert get_active_backend() == "z3"

    def test_invalid_cli_backend_raises(self):
        """Invalid backend name should raise ValueError."""
        with pytest.raises(ValueError, match="Unknown solver backend"):
            set_cli_backend("invalid")


class TestBackendValidation:
    """Tests for backend validation."""

    def test_validate_z3_succeeds(self):
        """Validating z3 should succeed."""
        validate_backend("z3")  # Should not raise

    def test_validate_unknown_backend_raises(self):
        """Unknown backend should raise ValueError."""
        with pytest.raises(ValueError, match="Unknown solver backend"):
            validate_backend("invalid")

    @pytest.mark.skipif(detect_cvc5(), reason="cvc5 is installed")
    def test_validate_missing_cvc5_raises(self):
        """Validating cvc5 when not installed should raise ImportError."""
        with pytest.raises(ImportError, match="cvc5 not installed"):
            validate_backend("cvc5")


class TestClearCliBackend:
    """Tests for clearing CLI backend override."""

    def test_clear_cli_backend(self):
        """Clearing CLI backend should allow other settings to take effect."""
        set_cli_backend("z3")
        assert get_active_backend({"solver": "cvc5"}) == "z3"

        clear_cli_backend()
        assert get_active_backend({"solver": "cvc5"}) == "cvc5"
