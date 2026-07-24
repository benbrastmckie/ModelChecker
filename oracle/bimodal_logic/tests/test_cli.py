"""Tests for bimodal_logic.cli - thin CLI entry point.

Task 104 Phase 4: TDD tests for bimodal-logic check command.

This module tests:
1. CLI module can be imported
2. main() with valid formula JSON produces JSON output with "result" key
3. main() with no arguments exits non-zero and prints help
4. main() with invalid JSON exits with error
5. Known countermodel formula returns {"result": "invalid", "countermodel": {...}}
6. Known valid formula returns {"result": "valid", "countermodel": null}
"""

from __future__ import annotations

import json
import subprocess
import sys

import pytest


class TestCLIImport:
    """Test that CLI module can be imported."""

    def test_cli_module_importable(self):
        """CLI module imports without error."""
        from bimodal_logic import cli
        assert cli is not None

    def test_run_function_exists(self):
        """CLI module exposes a run() entry point function."""
        from bimodal_logic.cli import run
        assert callable(run)

    def test_main_function_exists(self):
        """CLI module exposes a main() function."""
        from bimodal_logic.cli import main
        assert callable(main)


class TestCLINoArguments:
    """Test CLI behavior with no arguments."""

    def test_no_arguments_exits_nonzero(self, capsys):
        """main() with no subcommand exits non-zero."""
        from bimodal_logic.cli import main
        with pytest.raises(SystemExit) as exc_info:
            main([])
        assert exc_info.value.code != 0

    def test_no_arguments_prints_help(self, capsys):
        """main() with no subcommand prints usage information."""
        from bimodal_logic.cli import main
        with pytest.raises(SystemExit):
            main([])
        captured = capsys.readouterr()
        # Help output goes to stdout or stderr
        combined = captured.out + captured.err
        assert "check" in combined or "bimodal" in combined or "usage" in combined.lower()


class TestCLIInvalidInput:
    """Test CLI behavior with invalid inputs."""

    def test_invalid_json_exits_nonzero(self, capsys):
        """main() with invalid JSON string exits non-zero."""
        from bimodal_logic.cli import main
        with pytest.raises(SystemExit) as exc_info:
            main(["check", "not-valid-json{"])
        assert exc_info.value.code != 0

    def test_invalid_json_prints_error(self, capsys):
        """main() with invalid JSON prints an error message."""
        from bimodal_logic.cli import main
        with pytest.raises(SystemExit):
            main(["check", "not-valid-json{"])
        captured = capsys.readouterr()
        combined = captured.out + captured.err
        assert "error" in combined.lower() or "invalid" in combined.lower() or "json" in combined.lower()

    def test_unsupported_frame_class_exits_nonzero(self, capsys):
        """main() with unsupported --frame-class exits non-zero."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula, "--frame-class", "Unsupported"])
        assert exc_info.value.code != 0


class TestCLICountermodelFormula:
    """Test CLI behavior with a formula that has a countermodel (invalid)."""

    def test_invalid_formula_returns_result_key(self, capsys):
        """check command on SAT formula produces JSON with 'result' key."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert "result" in output

    def test_invalid_formula_result_is_invalid(self, capsys):
        """check command on atom formula returns result='invalid'."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert output["result"] == "invalid"

    def test_invalid_formula_has_countermodel_key(self, capsys):
        """check command on SAT formula has 'countermodel' key."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert "countermodel" in output

    def test_invalid_formula_countermodel_is_dict(self, capsys):
        """check command on SAT formula has countermodel as dict (not null)."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert output["countermodel"] is not None
        assert isinstance(output["countermodel"], dict)


class TestCLIValidFormula:
    """Test CLI behavior with a tautology (valid formula)."""

    def test_valid_formula_returns_result_key(self, capsys):
        """check command on tautology produces JSON with 'result' key."""
        from bimodal_logic.cli import main
        # A => A is a tautology (no countermodel)
        formula = json.dumps({
            "tag": "imp",
            "left": {"tag": "atom", "name": "A"},
            "right": {"tag": "atom", "name": "A"},
        })
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert "result" in output

    def test_valid_formula_result_is_valid(self, capsys):
        """check command on tautology returns result='valid'."""
        from bimodal_logic.cli import main
        formula = json.dumps({
            "tag": "imp",
            "left": {"tag": "atom", "name": "A"},
            "right": {"tag": "atom", "name": "A"},
        })
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert output["result"] == "valid"

    def test_valid_formula_countermodel_is_null(self, capsys):
        """check command on tautology has countermodel=null."""
        from bimodal_logic.cli import main
        formula = json.dumps({
            "tag": "imp",
            "left": {"tag": "atom", "name": "A"},
            "right": {"tag": "atom", "name": "A"},
        })
        with pytest.raises(SystemExit) as exc_info:
            main(["check", formula])
        assert exc_info.value.code == 0
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert output["countermodel"] is None


class TestCLIOutputFormat:
    """Test CLI JSON output format requirements."""

    def test_output_is_valid_json(self, capsys):
        """check command output is valid JSON on stdout."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit):
            main(["check", formula])
        captured = capsys.readouterr()
        # Should be parseable JSON
        output = json.loads(captured.out.strip())
        assert isinstance(output, dict)

    def test_output_has_exactly_two_keys(self, capsys):
        """check command output has exactly 'result' and 'countermodel' keys."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit):
            main(["check", formula])
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert set(output.keys()) == {"result", "countermodel"}

    def test_result_is_string(self, capsys):
        """'result' field is always a string."""
        from bimodal_logic.cli import main
        formula = json.dumps({"tag": "atom", "name": "A"})
        with pytest.raises(SystemExit):
            main(["check", formula])
        captured = capsys.readouterr()
        output = json.loads(captured.out.strip())
        assert isinstance(output["result"], str)
        assert output["result"] in ("valid", "invalid")
