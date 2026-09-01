# Research Report: Windows `UnicodeEncodeError` in Model Output

**Task**: 182 — Fix the `UnicodeEncodeError` that crashes model output on Windows, and adopt a
deliberate policy on non-ASCII characters in printed output.

## 1. Confirmed Mechanism (why it only fails on Windows, and only in packaging)

- On a *real, interactive* Windows console, Python 3.6+ (PEP 528) talks to the console via
  `WriteConsoleW`, which is UTF-8-safe regardless of the active codepage. The crash reported in
  run 33502990193 is **not** that case.
- `tests/packaging/test_generate_then_execute.py` runs the installed `model-checker` console
  script via `subprocess.run([...], capture_output=True, text=True)`. Redirecting/piping stdout
  takes Python off the PEP-528 console path entirely; on Windows it falls back to
  `locale.getpreferredencoding()`, which is the ANSI codepage — `cp1252` on the GitHub
  `windows-latest` runner's default locale. That is exactly the `cp1252` codec named in the
  traceback.
- Confirmed no mitigation exists anywhere in the source: `grep -rn "reconfigure\|PYTHONIOENCODING\|PYTHONUTF8"` across `code/src/model_checker` returns nothing outside this report, and
  `code/tests/packaging/conftest.py`'s `installed_venv` fixture builds its subprocess `env` from
  `os.environ` verbatim (`env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}`,
  `installed_venv` around line 470) — no `PYTHONIOENCODING`/`PYTHONUTF8` is injected, so the
  child inherits the runner's ambient (cp1252-on-Windows) encoding.
- The gating test selection (`-m "not packaging and ..."`, used by `pypi-smoke.yml` line 85 and
  `release.yml` line 250 as `packaging and not unstable`) deselects `tests/packaging/` from the
  pre-publish "Test on windows-latest" job, so only the post-publish "Verify PyPI install" e2e
  legs exercise real subprocess-captured console output on Windows. This matches the task's
  "why the pre-publish tests did not catch it" note precisely — confirmed independently by
  reading `.github/workflows/release.yml` and `code/tests/packaging/test_generate_then_execute.py`'s own docstring/marker (`pytestmark = [pytest.mark.packaging, pytest.mark.slow]`).

## 2. Complete inventory of non-ASCII *print-path* defects (not docstrings/operator names)

A repo-wide `grep -rnP '[^\x00-\x7F]' code/src/model_checker --include='*.py'` returns ~632
hits across ~76 files, but the overwhelming majority are docstrings, comments, and mathematical
prose (e.g. `theory_lib/logos/subtheories/*/operators.py` — `□`, `◇`, `∧` appear only in
docstrings; the actual `Operator.name` values used for formula rendering are already ASCII,
e.g. `name = "\\Box"`, `name = "\\Diamond"` in `theory_lib/logos/subtheories/modal/operators.py:41,112`). Filtering to files that actually `print(..., file=output)` non-ASCII
characters to a caller-supplied stream yields:

| File:line | Character(s) | Context |
|---|---|---|
| `theory_lib/bimodal/semantic/model.py:210` | `⟹` (U+27F9) | `print_evaluation` — single world-history transition arrow |
| `theory_lib/bimodal/semantic/model.py:228-229` | `₀-₉`, `₋` (U+2080-2089, U+208B) | `_to_subscript` — duration subscript digits |
| `theory_lib/bimodal/semantic/model.py:352` | `⟹` | `_create_world_line` (feeds `print_world_histories`) — **columnar-aligned** transition arrow |
| `theory_lib/bimodal/semantic/model.py:537` | `↓` (U+2193) | `print_world_histories_vertical` — inter-row arrow, placed at a computed column offset |
| `models/structure.py:762` | `→` (U+2192) | `_print_sentence_letter_differences` (theory-agnostic, shared by all 4 theories) |
| `models/structure.py:781` | `→` | `_print_semantic_function_differences` |
| `models/structure.py:798` | `→` | `_print_model_structure_differences` |
| `theory_lib/exclusion/semantic/model.py:536` | `→` | witness-function difference printing — **not named in the traceback, found via sweep** |
| `theory_lib/imposition/semantic/model.py:172` | `→` | imposition-relation printing (`a →_w u`) — **not named in the traceback, found via sweep** |

`theory_lib/logos/semantic/model.py` has **zero** non-ASCII print hits — logos crashes only via
the shared `models/structure.py` difference-reporting path, confirming the task's framing that
`structure.py` is the reason all four theories fail, not just bimodal.

**Adjacent but currently non-triggering risk (found during the sweep, outside the traceback):**
`output/progress/display.py`'s `TerminalDisplay.enabled` is hardcoded `True` ("Always enabled
for testing"; the `stream.isatty()` gate is commented out at line 66), and
`output/progress/animated.py`'s `_generate_bar` unconditionally builds block characters
(`█`/`░`) regardless of color/tty state — only the *color* codes are isatty-gated
(`animated.py:195-198`), not the glyphs themselves. `TerminalDisplay.update()` would `write()`
these glyphs to a piped Windows stdout exactly as unguarded as the model-output path. It does
not fire in `test_generate_then_execute` because the generated default `examples.py` does not
invoke multi-model iteration, so `UnifiedProgress`/`AnimatedProgressBar` is never constructed in
this test. This is not required to make the named tests pass, but it is the same defect class
and should be covered by whatever policy is adopted, as a fast-follow if not in this task's
diff.

**Confirmed already-safe by explicit encoding:** `builder/example.py:310,331` (`--save`
file-writing paths) already `open(..., encoding="utf-8")` explicitly — this precedent (force
UTF-8 on files we own) already exists in the codebase; it just was never extended to the
stdout/console path.

## 3. Evidence the codebase's own alignment math was written for ASCII arrows

`bimodal/semantic/model.py`'s `_create_time_positions` (feeding `_create_world_line`, which
builds the columnar `print_world_histories` display) reserves a fixed budget per time column:

```python
current_pos += column_widths[time] + 4  # Width + space for " ==> "
```

The comment literally describes a 5-character ASCII arrow (`" ==> "`), but the code that fills
that slot renders `f" ⟹{self._to_subscript(dur)} "` — a Unicode arrow. For a single-digit
duration this is 4 characters (space + `⟹` + 1 subscript digit + space), which happens to fit
the reserved 4-char budget; for a two-digit duration (`⟹₁₂`) it is 5 characters and already
silently overflows into the next column's reserved space today, unrelated to encoding. This is
independent, pre-existing evidence that the alignment arithmetic was designed around an
ASCII-width arrow and the glyph was swapped to Unicode later without updating the width
accounting or the comment. `imposition/semantic/model.py:171`'s comment (`"Print in format: a
->_w u"`) shows the same pattern: ASCII arrow in the comment, Unicode `→_` in the code.

This is directly relevant to the "alignment must survive ASCII fallback" non-goal: substituting
ASCII digits for the subscript digits is **width-neutral** (each subscript digit is already
exactly 1 character, same as its ASCII equivalent), so only the arrow glyph itself
(`⟹` → e.g. `=>`) changes width, and the existing budget was already sized for something
ASCII-shaped, not smaller than an ASCII replacement would need. `print_world_histories_vertical`'s
`↓` → `v` substitution is exactly 1-for-1 width-neutral with no caveats — it is placed at a
single computed column offset with no multi-character slot to overflow.

## 4. The existing stream-sensitivity precedent

Every render method already takes this shape (e.g. `bimodal/semantic/model.py`
`print_world_histories`, `print_evaluation`, `print_world_histories_vertical`; `models/structure.py`'s `_print_sentence_letters` via `use_colors = output is sys.__stdout__`):

```python
GRAY = ""
RESET = ""
if output is sys.__stdout__:
    GRAY = "\033[37m"
    RESET = "\033[0m"
```

This branches on `output is sys.__stdout__` (identity, not `isatty()`) purely to decide whether
ANSI color codes are safe to emit — real consoles get color, anything else (files, StringIO,
pipes) gets plain text. It is *not* an encoding check today (a real Windows console piped through
`subprocess.run` is not `sys.__stdout__` inside the child either way, but that identity check was
never about encoding safety). The task's framing that "a precedent for stream-sensitive
rendering exists in exactly the function that crashes" is accurate as an architectural pattern to
extend, though the exact predicate (`is sys.__stdout__`) is the wrong one to reuse verbatim for
an encoding decision — see options below.

## 5. Testability constraint that most affects the design choice

The task requires: "an encoding-constrained test is runnable on Linux by writing to a stream
opened with `encoding='cp1252'`... this does NOT require a Windows runner." Concretely this
means a test can do:

```python
buf = io.BytesIO()
stream = io.TextIOWrapper(buf, encoding="cp1252")
structure.print_to(settings, name, theory_name, output=stream)
stream.flush()
```

This stream is **not** `sys.stdout`/`sys.__stdout__`, and it is **not** the process's real
console — it is an arbitrary caller-supplied `TextIOWrapper` with a restrictive `.encoding`.
Any fix strategy must therefore work correctly against `output`, the parameter actually threaded
through every `print(..., file=output)` call, not just against the process-global `sys.stdout`.
That constraint has direct consequences for each of the three remedies:

- **(a) Force UTF-8 on the stream** (`output.reconfigure(encoding="utf-8")`, or
  `PYTHONIOENCODING`/`PYTHONUTF8`): a `PYTHONIOENCODING`/`PYTHONUTF8` env-var approach affects
  only `sys.stdout`/`sys.stderr` at interpreter start — it cannot be exercised by a test that
  constructs its own `cp1252` `TextIOWrapper` and passes it as `output=`, and it does nothing for
  the `--save`-to-arbitrary-file path (which is already independently UTF-8 via explicit `open()`
  calls). A `.reconfigure(encoding="utf-8")` call on `output` itself *can* target the
  test's stream and would make the test pass, but it mutates a stream the caller constructed and
  owns — surprising if a caller deliberately wanted `cp1252` output (e.g. writing into a Windows
  batch script that must stay in the system codepage), and `.reconfigure()` is not guaranteed to
  exist on every object handed in as `output` (not all file-likes are `TextIOWrapper`).
- **(b) ASCII fallback keyed off stream encoding**: probe `getattr(output, "encoding", None)`
  and try/except-encode the candidate glyph against it (or maintain a small
  known-safe/known-unsafe glyph table); render Unicode when the stream can represent it,
  ASCII when it cannot, defaulting to Unicode when `.encoding` is absent (e.g. `io.StringIO`,
  which never encodes at all, preserving current test expectations that construct `StringIO()` to
  capture output as text). This directly matches the test harness's `cp1252`-`TextIOWrapper`
  scenario without touching `sys.stdout` globally, extends the `is sys.__stdout__` branch pattern
  already used for color, and does not mutate the caller's stream. Cost: two rendering paths
  (Unicode glyph, ASCII glyph) must be kept in sync per glyph — but the inventory in §2 above is
  short (5 glyph classes: `⟹`, subscript digits, `↓`, `→`, and none needed for `_to_subscript`'s
  already-width-neutral digits).
- **(c) ASCII-only unconditionally**: simplest, and trivially passes the same
  `cp1252`-`TextIOWrapper` test since the glyphs are just never emitted. Removes the branch
  entirely (no encoding probe needed at print time). Cost, as the task states, is dropping the
  Unicode presentation quality on every platform, not just Windows, and it changes reference
  output most colored/documented examples currently show — a larger surface of doc/example
  churn than (b).

## 6. Recommendation (for the planning stage to ratify or override)

Given §3 (alignment math already assumes ASCII-width glyphs) and §5 (the test harness targets
`output`, not `sys.stdout`), **option (b), stream-encoding-aware ASCII fallback**, is the
better-fitting remedy: it is directly testable via the prescribed `cp1252`-stream technique
without touching global interpreter state, it extends the codebase's own existing
`if output is sys.__stdout__` stream-sensitivity pattern (generalized from an identity check to
an encoding-capability check), and it does not mutate a caller-owned stream. A single shared
helper (e.g. in `models/structure.py` or a small new `models/`-level or `utils/`-level module,
since both `models/structure.py` and all four theories' `semantic/model.py` need it) that maps
each of the ~5 glyphs to an ASCII equivalent and picks per-call based on
`getattr(output, "encoding", None)` would cover every site in §2's table with one shared
utility rather than a bespoke branch per print site. `_to_subscript`'s digit mapping needs no
change (already width-neutral); only the arrow/down-arrow substitution needs the new helper.

This report intentionally stops short of writing the helper or its call sites — that is
plan/implementation work — but flags the concrete shape a plan should specify: (1) one shared
"can this stream render this glyph" predicate, (2) a glyph→ASCII table covering `⟹` → e.g. `=>`,
`↓` → `v`, `→` → `->`, (3) call-site updates at the 9 locations in §2's table, (4) the same
predicate optionally applied to `output/progress/display.py`/`animated.py` as a documented
fast-follow rather than blocking this fix, and (5) a TESTING_GUIDE.md / theory-docs note
recording the choice, since the task explicitly asks for a recorded policy, not just a patch.

## 7. Where to record the policy

- `code/docs/core/TESTING_GUIDE.md` has no existing section on output encoding; a new numbered
  subsection (after §8, "Best Practices and Patterns", which already documents other testing
  conventions like the `development`/`unstable` markers) is the natural home for "how to test an
  encoding-constrained output stream on Linux."
- The task specifically calls out documenting the choice "in the theory's docs" — bimodal is the
  theory whose renderer is most affected (aligned world histories); `theory_lib/bimodal/docs/ARCHITECTURE.md` or `USER_GUIDE.md` would be the natural per-theory location, since bimodal
  already has a `docs/` directory with `API_REFERENCE.md`, `ARCHITECTURE.md`, `ITERATE.md`,
  `SETTINGS.md`, `USER_GUIDE.md`. No repo currently documents an ASCII/Unicode output policy
  anywhere (confirmed: no `*conventions*`/`*rendering*`/`*output*`-named doc exists under
  `theory_lib/`, and `code/docs/core/CODE_STANDARDS.md`'s table of contents has no such
  section either) — this is a genuinely new convention, not an update to an existing one.

## 8. Verification path

- The four `test_generate_then_execute` cases must be exercised through a `cp1252`-constrained
  stream (per §5) as new/updated unit or integration coverage — not just against `StringIO`,
  which never raises `UnicodeEncodeError` because it performs no encoding at all.
- The packaging suite (`code/tests/packaging/test_generate_then_execute.py`) itself cannot be
  made to fail today on Linux/macOS (it never hits `cp1252`), so it does not serve as the
  regression test directly; the new coverage must be a separate test that constructs the
  restrictive-encoding stream directly, then the packaging suite continues to serve as the
  crash-class canary (staying green, unweakened) rather than the reproducer.
- `PYTHONPATH=code/src pytest code/tests/packaging/ -v -m packaging` and the existing gating
  suite (`PYTHONPATH=code/src pytest code/tests/ -v`) are both the standard verification commands
  per `CLAUDE.md`.
