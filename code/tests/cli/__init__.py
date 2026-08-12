"""CLI end-to-end verification test package.

Fast, in-process-free coverage of the `model-checker` CLI surface: `ParseFileFlags`
parsing/mapping behavior (`test_parse_file_flags.py`) and the registered flag table exercised
through `python -m model_checker` subprocess invocations (`test_flag_matrix.py`).

Real installed-console-script behavior and registry-driven generate-then-execute coverage live
in `code/tests/packaging/` instead, layered onto the existing wheel-build-and-venv-install
fixture there (see `code/tests/packaging/conftest.py`).
"""
