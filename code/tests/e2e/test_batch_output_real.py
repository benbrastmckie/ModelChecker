"""Real end-to-end test of batch output.

Rewritten: the previous version asserted only `returncode == 0` for a single-example run --
identical in substance to coverage `code/tests/cli/test_flag_matrix.py` now provides, and its
comment ("Use -l for load_theory (correct flag)") was simply wrong: the subprocess call it
preceded passed no `-l` at all, and `-l` could not have been used that way regardless -- at
`__main__.py`, `--load_theory` dispatches to `BuildProject.ask_generate()` and blocks on
`input()`, so it never runs an example file.

This version earns the "batch" in its name: it runs **multiple examples in one invocation**
through `--save` and asserts the batch-specific output shape -- one entry per example in the
combined `MODELS.json`'s `"models"` list, and a `---` separator between examples in the combined
`EXAMPLES.md` -- rather than merely that the process exited 0.
"""

from tests.utils.helpers import run_cli_command

_BATCH_EXAMPLE_CONTENT = '''"""Multi-example bimodal module for batch-output testing."""

from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
semantic_theories = {"batch_test": theory}

example_range = {
    "BATCH_EX_ONE": [[], ["A"], {"N": 2}],
    "BATCH_EX_TWO": [[], ["B"], {"N": 2}],
}
'''


def test_bimodal_batch_output_saves_one_model_entry_per_example(tmp_path):
    """--save with a two-example module produces a combined MODELS.json whose "models" list has
    exactly one entry per example, each identifiable by name -- the batch-specific behavior this
    file's name promises, not just a bare successful exit.
    """
    import json

    example_path = tmp_path / "batch_example.py"
    example_path.write_text(_BATCH_EXAMPLE_CONTENT)

    # file_path precedes --save so argparse's nargs='*' greedy consumption doesn't swallow the
    # positional file_path as a --save value.
    result = run_cli_command([str(example_path), '--save'], check=False, cwd=tmp_path)
    assert result.returncode == 0, (
        f"CLI command failed.\nstdout: {result.stdout}\nstderr: {result.stderr}"
    )

    output_dirs = list(tmp_path.glob("output_*"))
    assert len(output_dirs) == 1, f"expected exactly one output_* dir, found {output_dirs}"

    models_path = output_dirs[0] / "MODELS.json"
    assert models_path.exists(), "batch --save did not produce MODELS.json"
    data = json.loads(models_path.read_text())

    assert len(data["models"]) == 2, (
        f"expected one model entry per example (2), got {len(data['models'])}: {data['models']}"
    )
    example_names = {model["example"] for model in data["models"]}
    assert example_names == {"BATCH_EX_ONE", "BATCH_EX_TWO"}


def test_bimodal_batch_output_combines_markdown_with_separator(tmp_path):
    """The combined EXAMPLES.md joins per-example output with a '---' separator, proving both
    examples' formatted output actually landed in the same file rather than only the first (or
    only a single-example smoke check, which the previous version of this test provided)."""
    example_path = tmp_path / "batch_example.py"
    example_path.write_text(_BATCH_EXAMPLE_CONTENT)

    result = run_cli_command([str(example_path), '--save', 'markdown'], check=False, cwd=tmp_path)
    assert result.returncode == 0

    output_dirs = list(tmp_path.glob("output_*"))
    assert len(output_dirs) == 1
    examples_md = (output_dirs[0] / "EXAMPLES.md").read_text()

    assert 'BATCH_EX_ONE' in examples_md
    assert 'BATCH_EX_TWO' in examples_md
    assert '---' in examples_md, "combined markdown should join per-example sections with '---'"
