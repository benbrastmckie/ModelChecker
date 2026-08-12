"""Regression guard: every CLI flag token named in a documented shell invocation must be a flag
the tooling actually accepts.

The allowed-token set is derived programmatically from `ParseFileFlags().parser._actions`
(`_registered_option_strings()`), never hand-transcribed -- a flag removed from the parser must
make this guard fail loudly rather than silently keeping a stale allowlist entry. It is unioned
with `_DEV_CLI_WRAPPER_FLAGS`, the small, explicitly-enumerated set of flags `code/dev_cli.py`
consumes and rewrites *before* argparse ever sees them (`--iso-debug`, `--load`, `-load`); those
are real, working flags for `dev_cli.py` invocations even though `ParseFileFlags` itself has no
matching `add_argument` call.

Declared blind spot: this guard only scans shell invocation lines inside fenced code blocks
(``` ```bash ```/``` ```sh ```/``` ```shell ```/``` ```console ```/untagged). Prose sentences and
ASCII diagram boxes that merely *mention* a flag (e.g. a comment, a "Debug messages (with
--verbose)" aside, a diagram bullet) are not invocation lines and are not scanned -- those sites
must be caught by hand during doc review, not by this test.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from model_checker.__main__ import ParseFileFlags

# ---------------------------------------------------------------------------------------------
# Allowed-token derivation
# ---------------------------------------------------------------------------------------------

# code/dev_cli.py's `if __name__ == "__main__":` block rewrites these tokens out of sys.argv
# *before* ParseFileFlags._create_parser()'s argparse ever runs, so they are real, accepted
# tokens for a `./dev_cli.py ...` invocation despite never being registered on the parser itself:
#   --iso-debug : consumed and stripped; enables isomorphism-check debug logging
#   -load, --load : rewritten in place to -l (the registered --load_theory/-l short form)
_DEV_CLI_WRAPPER_FLAGS = {'--iso-debug', '--load', '-load'}


def _registered_option_strings() -> set[str]:
    """Every `opt` string the parser itself registers, derived from `parser._actions` -- never a
    hand-transcribed list. Includes argparse's automatic `-h`/`--help`."""
    parser = ParseFileFlags().parser
    registered: set[str] = {'-h', '--help'}
    for action in parser._actions:
        registered.update(action.option_strings)
    return registered


def _allowed_tokens() -> set[str]:
    """The full allowlist a documented invocation line's flag tokens are checked against."""
    return _registered_option_strings() | _DEV_CLI_WRAPPER_FLAGS


def test_dev_cli_wrapper_flags_still_exist():
    """Each `_DEV_CLI_WRAPPER_FLAGS` literal must still appear in `code/dev_cli.py`'s source, so
    allowlist drift (the wrapper flag being removed or renamed) fails this test loudly instead of
    silently widening the doc-flag allowlist forever."""
    dev_cli_path = Path(__file__).resolve().parents[2] / 'dev_cli.py'
    source = dev_cli_path.read_text()
    for flag in sorted(_DEV_CLI_WRAPPER_FLAGS):
        assert flag in source, (
            f"{flag!r} is declared in _DEV_CLI_WRAPPER_FLAGS but no longer appears in "
            f"{dev_cli_path} -- update the wrapper-flag allowlist"
        )


# ---------------------------------------------------------------------------------------------
# Fenced-code-block invocation extraction
# ---------------------------------------------------------------------------------------------

# Fenced-block language tags whose content may contain real shell invocations. An untagged
# fence (bare ``` ```` ```) is also admitted -- many docs in this tree fence shell examples with
# no language tag at all.
_SHELL_BLOCK_TAGS = {'bash', 'sh', 'shell', 'console', ''}

# A fence line: three or more backticks, optionally followed by a language tag.
_FENCE_RE = re.compile(r'^```+\s*([A-Za-z0-9_+-]*)\s*$')

# Invocation-line prefixes this guard treats as a `model-checker` / `dev_cli.py` command.
_INVOCATION_PREFIXES = (
    'model-checker',
    './dev_cli.py',
    'dev_cli.py',
    'python -m model_checker',
)

# Truncate a matched invocation line at the first shell control/redirection operator, so flags
# belonging to a *downstream* command (`| grep -E ...`) are never attributed to model-checker.
# Longest-first so `>>` is not mistakenly matched as a lone `>` occurring earlier in the pass.
_TRUNCATE_OPERATORS = ('&&', '||', '>>', '|', ';', '>', '<')

# A leading shell prompt.
_PROMPT_RE = re.compile(r'^\$\s+')

# A leading environment-variable-assignment prefix, e.g. `PYTHONPATH=code/src `.
_ENV_PREFIX_RE = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*=\S+\s+')


def _iter_fenced_blocks(text: str):
    """Yield (start_line_number, tag, block_lines) for every fenced code block in `text`.

    `start_line_number` is the 1-indexed line number of the fence's opening line; `block_lines`
    are the raw lines strictly between the opening and closing fence (exclusive of both).
    """
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        match = _FENCE_RE.match(lines[i])
        if match:
            tag = match.group(1).lower()
            start_line = i + 1
            body_start = i + 1
            j = body_start
            while j < len(lines) and not _FENCE_RE.match(lines[j]):
                j += 1
            yield start_line, tag, lines[body_start:j]
            i = j + 1
        else:
            i += 1


def _truncate_at_operator(line: str) -> str:
    """Cut `line` at the earliest occurrence of any shell control/redirection operator."""
    cut_at = len(line)
    for op in _TRUNCATE_OPERATORS:
        idx = line.find(op)
        if idx != -1 and idx < cut_at:
            cut_at = idx
    return line[:cut_at].rstrip()


def _iter_invocations(text: str):
    """Yield (line_number, command) for every recognized model-checker/dev_cli.py invocation in
    fenced shell (or untagged) code blocks within `text`. `line_number` is 1-indexed and points
    at the physical line the (possibly backslash-joined) invocation starts on.
    """
    for fence_start, tag, block_lines in _iter_fenced_blocks(text):
        if tag not in _SHELL_BLOCK_TAGS:
            continue

        k = 0
        while k < len(block_lines):
            raw_line = block_lines[k]
            physical_line_number = fence_start + 1 + k

            # Join trailing-backslash continuations before any other processing.
            joined = raw_line
            consumed = 1
            while joined.rstrip().endswith('\\'):
                next_idx = k + consumed
                if next_idx >= len(block_lines):
                    break
                joined = joined.rstrip()[:-1].rstrip() + ' ' + block_lines[next_idx].strip()
                consumed += 1

            candidate = joined.strip()
            candidate = _PROMPT_RE.sub('', candidate)
            candidate = _ENV_PREFIX_RE.sub('', candidate)

            if candidate.startswith(_INVOCATION_PREFIXES):
                truncated = _truncate_at_operator(candidate)
                yield physical_line_number, truncated

            k += consumed


# ---------------------------------------------------------------------------------------------
# Flag-token extraction
# ---------------------------------------------------------------------------------------------

# A long flag, e.g. --save, --print_constraints. Value after `=` (if any) is not part of the
# token.
_LONG_FLAG_RE = re.compile(r'^(--[A-Za-z][A-Za-z0-9_-]*)')

# A single-letter short flag, e.g. -c, -l.
_SHORT_FLAG_RE = re.compile(r'^(-[A-Za-z])$')

# A multi-letter single-hyphen token, e.g. -st, -load. This parser registers no multi-letter
# short options (every short flag is exactly one letter), so any token matching this shape is
# unconditionally an invalid/fabricated flag -- this is what catches `-st`.
_INVALID_SHORT_RE = re.compile(r'^(-[A-Za-z]{2,})')


def _extract_flag_tokens(command: str):
    """Yield every `-`-prefixed token in `command` (skipping the leading executable token),
    normalized to its bare flag form (no `=value` suffix). Multi-letter single-hyphen tokens
    (e.g. `-st`) are yielded as-is; the caller compares against the allowlist, which never
    contains such a token, so they are always reported as violations.
    """
    import shlex

    try:
        tokens = shlex.split(command)
    except ValueError:
        # Unbalanced quotes in a doc example -- nothing this guard can safely tokenize.
        return
    for token in tokens[1:]:
        if not token.startswith('-') or token == '-':
            continue
        long_match = _LONG_FLAG_RE.match(token)
        if long_match:
            yield long_match.group(1)
            continue
        short_match = _SHORT_FLAG_RE.match(token)
        if short_match:
            yield short_match.group(1)
            continue
        invalid_match = _INVALID_SHORT_RE.match(token)
        if invalid_match:
            yield invalid_match.group(1)


# ---------------------------------------------------------------------------------------------
# Extractor unit tests (fixture strings only -- no real documentation is scanned here)
# ---------------------------------------------------------------------------------------------


def test_valid_invocation_is_extracted_and_registered():
    text = """
```bash
model-checker examples.py --save markdown
```
"""
    invocations = list(_iter_invocations(text))
    assert len(invocations) == 1
    line_number, command = invocations[0]
    assert command == 'model-checker examples.py --save markdown'
    tokens = list(_extract_flag_tokens(command))
    assert tokens == ['--save']
    assert set(tokens) <= _allowed_tokens()


def test_python_blocks_are_skipped():
    """The `settings/README.md` `parser.add_argument('--your-setting', ...)` illustration lives
    in a ```python block and must never be treated as an invocation."""
    text = """
```python
parser.add_argument('--your-setting', action='store_true')
model-checker examples.py --your-setting
```
"""
    assert list(_iter_invocations(text)) == []


def test_pip_install_is_not_an_invocation():
    text = """
```bash
pip install --user model-checker
```
"""
    assert list(_iter_invocations(text)) == []


def test_ls_and_apt_are_not_invocations():
    text = """
```bash
ls -la
apt install -y python3
```
"""
    assert list(_iter_invocations(text)) == []


def test_piped_grep_truncates_before_downstream_flags():
    text = """
```bash
./dev_cli.py examples.py --save | grep -E "some pattern"
```
"""
    invocations = list(_iter_invocations(text))
    assert len(invocations) == 1
    _, command = invocations[0]
    assert command == './dev_cli.py examples.py --save'
    assert '-E' not in list(_extract_flag_tokens(command))


def test_cprofile_wrapped_invocation_is_not_an_invocation():
    text = """
```bash
python -m cProfile -o profile.stats dev_cli.py examples/slow.py
```
"""
    assert list(_iter_invocations(text)) == []


def test_backslash_continued_invocation_is_joined():
    text = """
```bash
model-checker examples.py \\
    --save markdown \\
    --contingent
```
"""
    invocations = list(_iter_invocations(text))
    assert len(invocations) == 1
    _, command = invocations[0]
    tokens = list(_extract_flag_tokens(command))
    assert tokens == ['--save', '--contingent']


def test_multiletter_short_flag_is_reported():
    text = """
```bash
model-checker examples.py -st modal
```
"""
    invocations = list(_iter_invocations(text))
    assert len(invocations) == 1
    _, command = invocations[0]
    tokens = list(_extract_flag_tokens(command))
    assert '-st' in tokens
    assert '-st' not in _allowed_tokens()


def test_iso_debug_and_load_wrapper_flags_are_allowed():
    text = """
```bash
./dev_cli.py --iso-debug examples.py
./dev_cli.py -load bimodal examples.py
./dev_cli.py --load bimodal examples.py
```
"""
    for _, command in _iter_invocations(text):
        for token in _extract_flag_tokens(command):
            assert token in _allowed_tokens(), (
                f"{token!r} from {command!r} should be an allowed dev_cli wrapper flag"
            )


# ---------------------------------------------------------------------------------------------
# Doc-scan test: the real documentation tree
# ---------------------------------------------------------------------------------------------

# Repository root, derived from this file's own location rather than cwd, so the glob set is
# correct regardless of where pytest is invoked from.
_REPO_ROOT = Path(__file__).resolve().parents[3]

# Markdown globs scanned by the doc-flag lint. `specs/**` and `.claude/**` are deliberately
# excluded: task artifacts under those trees intentionally quote broken/fabricated flags while
# describing or planning this very fix, and scanning them would make the guard permanently
# unsatisfiable.
_DOC_GLOBS = (
    'docs/**/*.md',
    'code/docs/**/*.md',
    'code/src/model_checker/**/*.md',
    'code/README.md',
    'README.md',
)


def _iter_doc_files():
    """Yield every markdown file matched by `_DOC_GLOBS`, relative to `_REPO_ROOT`."""
    seen: set[Path] = set()
    for pattern in _DOC_GLOBS:
        for path in _REPO_ROOT.glob(pattern):
            if path in seen:
                continue
            seen.add(path)
            yield path


def _scan_doc_violations():
    """Return a sorted list of (relative_path, line_number, token) triples for every
    documented invocation-line flag token that is neither registered on the parser nor a known
    dev_cli.py wrapper flag."""
    allowed = _allowed_tokens()
    violations = []
    files_scanned = 0
    for doc_path in _iter_doc_files():
        files_scanned += 1
        text = doc_path.read_text(errors='replace')
        rel_path = doc_path.relative_to(_REPO_ROOT)
        for line_number, command in _iter_invocations(text):
            for token in _extract_flag_tokens(command):
                if token not in allowed:
                    violations.append((str(rel_path), line_number, token))
    violations.sort()
    return violations, files_scanned


@pytest.mark.xfail(strict=True, reason="RED until docs are fixed; xfail removed in Phase 8")
def test_documented_flags_are_registered():
    """Every flag token named in a documented shell invocation line must be registered on the
    parser or be a known `dev_cli.py` wrapper flag. See the module docstring for the declared
    prose/diagram blind spot.
    """
    violations, files_scanned = _scan_doc_violations()

    # Sanity: a broken glob (e.g. a typo'd pattern matching nothing) must not produce a vacuous
    # pass. The declared doc globs cover 200+ markdown files in this tree as of this writing.
    assert files_scanned > 50, (
        f"only {files_scanned} files scanned -- _DOC_GLOBS may be broken (too narrow)"
    )

    if violations:
        report_lines = [f"{path}:{line}: {token}" for path, line, token in violations]
        pytest.fail(
            f"{len(violations)} fabricated/unregistered flag token(s) found in documented "
            f"invocation lines:\n" + "\n".join(report_lines)
        )
