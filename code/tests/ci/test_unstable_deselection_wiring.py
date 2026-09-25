"""Executable contract: every gating pytest invocation across the repository's CI drivers
carries `and not unstable` in its `-m` marker expression, so a test marked
`@pytest.mark.unstable` is deselected from every release-gating run rather than merely from the
ones an author remembered to update by hand.

**No longer also enforces `and not development`.** This contract previously enforced a second,
sibling marker in the same expressions; `development` is retired (see
`code/docs/core/TESTING_GUIDE.md` section 8.14) now that bimodal has exited development, so this
file's assertions were narrowed back to `unstable` alone. `EXPECTED_GATING_MARKER_INVOCATIONS`
stays `10`: the retirement changed what each `-m` expression contains, not how many `-m`-bearing
invocations exist.

Seven drivers are in scope: `.github/workflows/tests.yml`, `flake.nix`,
`.github/workflows/differential-tests.yml`, `oracle/run-oracle-suite.sh`,
`.github/workflows/packaging.yml`, `.github/workflows/release.yml`, and
`.github/workflows/pypi-smoke.yml`. This is the first oracle-tree `unstable` marking (see
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan`), so
`run-oracle-suite.sh` is a newly in-scope driver that TESTING_GUIDE.md section 8.9's "Where the
deselection is wired" paragraph did not previously need to name. `packaging.yml`, `release.yml`,
and `pypi-smoke.yml` are newly in scope: all three run `code/tests/packaging/` gated on
`packaging`, and their selector previously needed a defensive `and not unstable` even though no
packaging test is or should ever be `unstable`-marked.

`.github/workflows/unstable-watch.yml` is DELIBERATELY EXCLUDED from the files scanned below:
it selects `-m unstable` by design (it is the non-gating observer, not a gating run) and must
never carry `not unstable`.

`.github/workflows/differential-tests.yml`'s "Run CI gate tests explicitly" step is node-id
selecting (six explicit `::TestClassName` arguments) and carries no `-m` expression at all --
that shape is explicitly ALLOWED by this contract, not required to carry `not unstable`,
because it can never collect an `unstable`-marked test: none of the six named classes is
`TestGatingConclusiveScan`.

Extraction is regex-based, not `yaml.safe_load`/shell-parsed, mirroring
`code/tests/ci/test_workflow_parity.py`'s own module docstring: PyYAML is not an installed
dependency in either CI toolchain, and `run-oracle-suite.sh` is not YAML at all. Backslash-line
continuations (used throughout `differential-tests.yml`'s `run: |` blocks and
`run-oracle-suite.sh`'s two pytest invocations) are joined into one logical line before
scanning, since a marker expression can span the continuation boundary.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TESTS_YML = REPO_ROOT / ".github" / "workflows" / "tests.yml"
FLAKE_NIX = REPO_ROOT / "flake.nix"
DIFFERENTIAL_TESTS_YML = REPO_ROOT / ".github" / "workflows" / "differential-tests.yml"
RUN_ORACLE_SUITE_SH = REPO_ROOT / "oracle" / "run-oracle-suite.sh"
PACKAGING_YML = REPO_ROOT / ".github" / "workflows" / "packaging.yml"
RELEASE_YML = REPO_ROOT / ".github" / "workflows" / "release.yml"
PYPI_SMOKE_YML = REPO_ROOT / ".github" / "workflows" / "pypi-smoke.yml"

_SCANNED_FILES = [
    TESTS_YML,
    FLAKE_NIX,
    DIFFERENTIAL_TESTS_YML,
    RUN_ORACLE_SUITE_SH,
    PACKAGING_YML,
    RELEASE_YML,
    PYPI_SMOKE_YML,
]

# The true aggregate count of `-m`-bearing gating invocations across all seven scanned drivers:
# tests.yml (2) + flake.nix (2) + differential-tests.yml (0, since its former broad `-m` step was
# removed as a proven-duplicate of the node-id "Run CI gate tests explicitly" step -- both
# selected the byte-identical same 49 node ids, confirmed by a `--collect-only` diff) +
# run-oracle-suite.sh (2) + packaging.yml (1) + release.yml (2) + pypi-smoke.yml (1) = 10. This
# constant has drifted stale in multiple directions across this repository's history: it was once
# undercounted as "six" in seven documentation anchors before this constant existed to enforce it
# executably; it was corrected to six (from seven) once differential-tests.yml's redundant `-m`
# step was removed; it is now ten, following the addition of packaging.yml, release.yml (both
# packaging-suite steps), and pypi-smoke.yml to the scanned set. The retirement of the
# `development` marker (see code/docs/core/TESTING_GUIDE.md section 8.14) changed what each of
# these ten `-m` expressions contains, not how many `-m`-bearing invocations exist -- this
# constant is unaffected by that retirement. See
# test_total_gating_marker_expression_count_matches_constant below.
EXPECTED_GATING_MARKER_INVOCATIONS = 10

TESTING_GUIDE_MD = REPO_ROOT / "code" / "docs" / "core" / "TESTING_GUIDE.md"

_MISSING_REPO_ROOT_FILES = [p for p in _SCANNED_FILES if not p.exists()]
if _MISSING_REPO_ROOT_FILES:
    pytest.skip(
        "Repo-root files not present in this sandbox (expected under `nix flake check`'s "
        "checks.default, whose `src = ./code` excludes the repo root): "
        + ", ".join(str(p) for p in _MISSING_REPO_ROOT_FILES)
        + ". This guard runs in .github/workflows/tests.yml's general-tests job instead, where "
        "actions/checkout@v4 provides the full repository.",
        allow_module_level=True,
    )

# Joins a `\`-terminated line with the next line (shell/YAML block-scalar continuation) into
# one logical line, so a marker expression split across lines is scanned as a whole.
_CONTINUATION_RE = re.compile(r"\\\n[ \t]*")

# Matches the `pytest` command token itself (not `pytest-xdist`, not `pytest_terminal_summary`,
# not the bare `pytest`/`pytest-timeout` dependency-list entries in flake.nix's `devPython`
# package list, and not prose mentions like "pytest invocations" inside a `#` comment --
# comment lines are filtered out separately before this regex runs). Requires whitespace
# immediately before and after so partial-word matches inside a longer identifier or a
# hyphenated package name are excluded by construction.
_PYTEST_TOKEN_RE = re.compile(r"(?<![\w.-])pytest(?=[ \t]+\S)")

_MARKER_EXPR_RE = re.compile(r'-m\s+"([^"]*)"')


def _extract_pytest_invocations(text: str) -> list[str]:
    """Return the tail-of-line text (from the `pytest` token to end of its logical line) for
    every real pytest invocation in `text`, after joining backslash continuations and
    dropping comment lines and dependency-install lines."""
    joined = _CONTINUATION_RE.sub(" ", text)
    invocations = []
    for line in joined.split("\n"):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "pip install" in stripped:
            continue
        match = _PYTEST_TOKEN_RE.search(stripped)
        if match is None:
            continue
        invocations.append(stripped[match.start() :])
    return invocations


def _invocations_for(path: Path) -> list[str]:
    return _extract_pytest_invocations(path.read_text())


class TestGatingInvocationsDeselectQuarantineMarkers:
    """Every invocation carrying an `-m` expression must include `not unstable`."""

    @pytest.mark.parametrize(
        "path",
        [
            TESTS_YML,
            FLAKE_NIX,
            DIFFERENTIAL_TESTS_YML,
            RUN_ORACLE_SUITE_SH,
            PACKAGING_YML,
            RELEASE_YML,
            PYPI_SMOKE_YML,
        ],
    )
    def test_every_marker_expression_excludes_unstable(self, path):
        invocations = _invocations_for(path)
        assert invocations, f"expected at least one pytest invocation in {path}, found none"

        checked_any_marker_expr = False
        for invocation in invocations:
            marker_match = _MARKER_EXPR_RE.search(invocation)
            if marker_match is None:
                # Explicitly allowed: a node-id-selecting invocation with no `-m` at all
                # (differential-tests.yml's "Run CI gate tests explicitly" step is the one
                # instance of this shape today).
                continue
            checked_any_marker_expr = True
            marker_expr = marker_match.group(1)
            assert "not unstable" in marker_expr, (
                f"{path}: pytest invocation's -m expression {marker_expr!r} does not "
                f"exclude `unstable` -- an unstable-marked test would run in this gating "
                f"invocation. Full invocation: {invocation!r}"
            )

        if path in (
            TESTS_YML,
            FLAKE_NIX,
            RUN_ORACLE_SUITE_SH,
            PACKAGING_YML,
            RELEASE_YML,
            PYPI_SMOKE_YML,
        ):
            # These six drivers are known to carry at least one `-m`-bearing invocation
            # (tests.yml/flake.nix/run-oracle-suite.sh each run exactly two -- parallel +
            # serial; packaging.yml and pypi-smoke.yml one each; release.yml two). A file
            # with zero `-m`-bearing invocations found means the extraction itself broke,
            # not that the file legitimately has none.
            assert checked_any_marker_expr, (
                f"{path}: found pytest invocation(s) but none carried an -m expression -- "
                f"extraction likely broke, since this driver is known to use -m"
            )

    def test_scanned_invocation_counts_match_known_shape(self):
        """Sanity check on the extraction itself: the expected invocation count per file,
        confirmed by reading each file directly (per this contract's own Pre-Edit
        Verification Gate obligation) rather than assumed. A mismatch here means the
        regex extraction diverged from the files' real shape, which would silently make
        the assertions above vacuous."""
        assert len(_invocations_for(TESTS_YML)) == 2
        assert len(_invocations_for(FLAKE_NIX)) == 2
        assert len(_invocations_for(DIFFERENTIAL_TESTS_YML)) == 1
        assert len(_invocations_for(RUN_ORACLE_SUITE_SH)) == 2
        assert len(_invocations_for(PACKAGING_YML)) == 1
        assert len(_invocations_for(RELEASE_YML)) == 2
        assert len(_invocations_for(PYPI_SMOKE_YML)) == 1

    def test_total_gating_marker_expression_count_matches_constant(self):
        """The aggregate count of `-m`-bearing gating invocations across all seven scanned
        drivers is fixed at EXPECTED_GATING_MARKER_INVOCATIONS. An uncaught drift here is
        exactly how "six" went stale before this constant existed to enforce it executably."""
        total = sum(
            1
            for path in _SCANNED_FILES
            for inv in _invocations_for(path)
            if _MARKER_EXPR_RE.search(inv) is not None
        )
        assert total == EXPECTED_GATING_MARKER_INVOCATIONS, (
            f"expected {EXPECTED_GATING_MARKER_INVOCATIONS} `-m`-bearing gating invocations "
            f"across {[str(p) for p in _SCANNED_FILES]}, found {total}"
        )

    def test_differential_tests_yml_gate_step_has_no_marker_expression(self):
        """Documents, explicitly, WHY differential-tests.yml's second invocation is allowed
        to carry no `-m` at all: it node-id-selects six specific classes, none of which is
        TestGatingConclusiveScan, so it can never collect an unstable-marked test."""
        invocations = _invocations_for(DIFFERENTIAL_TESTS_YML)
        node_id_selecting = [inv for inv in invocations if _MARKER_EXPR_RE.search(inv) is None]
        assert len(node_id_selecting) == 1
        assert "TestGatingConclusiveScan" not in node_id_selecting[0]

    def test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable(self):
        """`unstable-watch.yml` is excluded from `_SCANNED_FILES` above by design -- confirm,
        as a documentation-grade sanity check, that its own two pytest invocations select
        `-m unstable` (the observer's job) rather than deselecting it, so a future edit
        accidentally aligning it with the gating drivers is caught here rather than silently
        breaking the observer.

        Uses a narrower, dedicated regex (not `_extract_pytest_invocations`) because this
        workflow's classify step embeds a Python docstring containing the prose
        "pytest never ran, rather than exit-5's ..." -- a real false-positive match for the
        general extractor's comment-line filter (it is not a `#`-prefixed shell/YAML comment,
        it is prose inside a Python triple-quoted string), which is exactly why this
        assertion is scoped to the precise `-m unstable` shape rather than reusing the
        general-purpose extraction this test intentionally does not exercise here."""
        unstable_watch_yml = REPO_ROOT / ".github" / "workflows" / "unstable-watch.yml"
        text = unstable_watch_yml.read_text()
        matches = re.findall(r'pytest\s+\S.*?-m\s+unstable\b', text)
        assert len(matches) == 2

    def test_watch_development_step_selects_development_and_writes_junit(self):
        """The producing step for the classifier's DEV_STATUS path (8.14's GAP 3): a third
        watch step, alongside `watch_code` and `watch_oracle`, that selects `-m development`,
        writes `/tmp/watch-development.xml` (`DEFAULT_DEV_JUNIT_PATH` in
        `.github/scripts/unstable_watch_classify.py`), is `continue-on-error: true`, and
        tolerates exit codes 0 and 5 exactly like its two siblings.

        Uses a narrow, dedicated extraction (split on `- name:` step boundaries, not
        `_extract_pytest_invocations`) for the same reason
        `test_unstable_watch_workflow_is_deliberately_excluded_and_selects_unstable` does:
        this workflow's classify step embeds Python prose the general extractor
        false-positives on."""
        unstable_watch_yml = REPO_ROOT / ".github" / "workflows" / "unstable-watch.yml"
        text = unstable_watch_yml.read_text()
        steps = re.split(r"\n(?=      - name:)", text)
        matches = [s for s in steps if "id: watch_development" in s]
        assert len(matches) == 1, (
            f"expected exactly one step carrying `id: watch_development`, found {len(matches)}"
        )
        step = matches[0]

        assert "continue-on-error: true" in step, (
            "the watch_development step must be continue-on-error: true, like watch_code and "
            "watch_oracle"
        )
        assert re.search(r"-m\s+development\b", step) is not None, (
            "the watch_development step must select `-m development`"
        )
        assert "--junitxml=/tmp/watch-development.xml" in step, (
            "the watch_development step must write /tmp/watch-development.xml, the classifier's "
            "DEFAULT_DEV_JUNIT_PATH"
        )
        assert re.search(
            r'\[\s*"\$code"\s*-eq\s*0\s*\]\s*\|\|\s*\[\s*"\$code"\s*-eq\s*5\s*\]', step
        ) is not None, (
            "the watch_development step must tolerate exit codes 0 and 5, like watch_code and "
            "watch_oracle"
        )


def _gate_step_block(text: str) -> str:
    """Return the text of differential-tests.yml's "Run CI gate tests explicitly" step, from
    its `- name:` line up to (but not including) the next `- name:` line or end of file. Regex/
    text extraction, not `yaml.safe_load`, per this module's own docstring: PyYAML is not an
    installed dependency in either CI toolchain."""
    match = re.search(
        r"- name: Run CI gate tests explicitly\n(?P<block>(?:.*\n)*?)(?=\n\s*- name:|\Z)",
        text,
    )
    assert match is not None, "could not locate the 'Run CI gate tests explicitly' step block"
    return match.group("block")


def _trigger_block(text: str, trigger: str) -> str:
    """Return the text of a top-level `on:` trigger block (`push:` or `pull_request:`), from
    its own line up to the next same-or-lower-indentation top-level key or end of the `on:`
    section."""
    match = re.search(
        rf"^  {trigger}:\n(?P<block>(?:    .*\n|\n)*)",
        text,
        re.MULTILINE,
    )
    assert match is not None, f"could not locate the top-level `{trigger}:` trigger block"
    return match.group("block")


class TestOracleSoundnessGateStaysUnconditionallyGating:
    """Pins the decision, recorded in `differential-tests.yml`'s own comment block and in
    `code/docs/core/TESTING_GUIDE.md` section 8.14, that the "Run CI gate tests explicitly"
    step stays unconditionally gating for bimodal edits BY DESIGN: it is a soundness check
    (TestCIGate::test_oracle_baseline_agreement fails only on a real semantic disagreement,
    never on a timeout), distinct from the `development` blanket that quarantines only
    completeness claims. Three properties, each independently falsifiable by a single
    targeted mutation (see this task's RED-evidence transcript): no `continue-on-error`, the
    `TestCIGate` node id still present, and the `paths:` trigger unnarrowed on both `push` and
    `pull_request`."""

    def test_gate_step_has_no_continue_on_error(self):
        block = _gate_step_block(DIFFERENTIAL_TESTS_YML.read_text())
        assert "continue-on-error" not in block, (
            "the 'Run CI gate tests explicitly' step must never gain `continue-on-error` -- "
            "see code/docs/core/TESTING_GUIDE.md section 8.14"
        )

    def test_gate_step_still_selects_test_ci_gate(self):
        block = _gate_step_block(DIFFERENTIAL_TESTS_YML.read_text())
        assert "::TestCIGate" in block, (
            "the 'Run CI gate tests explicitly' step must keep node-id-selecting TestCIGate -- "
            "it is the soundness assertion this gate exists to enforce"
        )

    @pytest.mark.parametrize("trigger", ["push", "pull_request"])
    def test_paths_trigger_unnarrowed(self, trigger):
        block = _trigger_block(DIFFERENTIAL_TESTS_YML.read_text(), trigger)
        assert "oracle/bimodal_logic/**" in block, (
            f"the `{trigger}:` trigger's `paths:` must still include `oracle/bimodal_logic/**`"
        )
        assert "code/src/model_checker/theory_lib/bimodal/**" in block, (
            f"the `{trigger}:` trigger's `paths:` must still include "
            f"`code/src/model_checker/theory_lib/bimodal/**`"
        )
