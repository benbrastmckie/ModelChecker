# Implementation Summary: Stream-Encoding-Aware ASCII Fallback for Printed Output

- **Task**: 182 - Fix the Windows `UnicodeEncodeError` in model output and establish a deliberate non-ASCII output policy
- **Status**: [COMPLETED]
- **Started**: 2026-09-01T00:00:00Z
- **Completed**: 2026-09-01T00:00:00Z
- **Effort**: ~9.5 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_stream-aware-ascii-fallback.md, reports/01_windows-unicode-encode-error.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Printed model output wrote raw non-ASCII glyphs (`⟹`, `→`, `↓`, subscript digits, the `□`
null-state symbol, `∅`, progress-bar block characters) directly to a caller-supplied `output`
stream. On a Windows pipe (any `subprocess.run(..., capture_output=True)` context, including the
packaging test suite and any real end-user redirect), Python falls off the PEP-528
`WriteConsoleW` console path and encodes with the ANSI codepage (`cp1252`), which cannot
represent those glyphs, crashing every theory's `print_to`/`print_all` with
`UnicodeEncodeError`. This plan adopted the research report's recommended remedy — a single
shared, stream-encoding-aware ASCII-fallback helper (`model_checker.utils.glyphs`) — and routed
every printed-output path across all four theories through it, while preserving bimodal's
aligned world-history columnar layout under substitution.

## What Changed

- New `model_checker.utils.glyphs` module: `glyph(name, output)` and `to_subscript(n, output)`
  resolve Unicode-vs-ASCII per glyph, keyed off `getattr(output, "encoding", None)`, memoized via
  `functools.lru_cache`. Substitution table: `DOUBLE_ARROW` (`⟹`/`=>`), `ARROW` (`→`/`->`),
  `DOWN_ARROW` (`↓`/`v`), `BLOCK_FULL` (`█`/`#`), `BLOCK_LIGHT` (`░`/`-`), `NULL_STATE` (`□`/`_`),
  `EMPTY_SET` (`∅`/`{}`).
- Routed through the helper: `models/structure.py`'s three difference-reporting arrow sites;
  `bimodal/semantic/model.py`'s double-arrow/subscript/down-arrow sites (`_to_subscript` changed
  from a `@staticmethod` to an instance method taking `output`); `exclusion/semantic/model.py`'s
  witness-function arrow plus 9 `bitvec_to_substates` call sites; `imposition/semantic/model.py`'s
  imposition-relation arrow plus 13 `bitvec_to_substates` call sites; `logos/semantic/model.py`'s
  6 `bitvec_to_substates` call sites; `output/progress/animated.py`'s progress-bar block glyphs.
- `model_checker.utils.bitvector.bitvec_to_substates` gained an optional `output=None` parameter
  (backward compatible — unset stays Unicode) so its null-state glyph (`□`) can be resolved
  per-caller.
- Each theory's `semantic/proposition.py` (`bimodal`, `exclusion`, `logos` — imposition reuses
  logos's `Proposition`) resolves its bare-`print()`-reachable glyphs (`world_state`, the
  `EMPTY_SET` fallback, and both `__repr__` methods' verifier/falsifier set display) against
  `sys.stdout` directly, since that print path never threads the `output` parameter at all.
- `bimodal/semantic/model.py`'s `_create_time_positions` now derives its per-column width budget
  from the actually-rendered arrow string (`_max_arrow_width_for_time`) instead of a hard-coded
  `+ 4`, fixing a latent two-digit-duration column overflow (report §3) as a byproduct.
- New regression coverage: `utils/tests/unit/test_glyphs.py` (28 tests), `models/tests/unit/
  test_structure_print_encoding.py`, four per-theory `tests/unit/test_print_encoding.py`,
  `bimodal/tests/unit/test_world_history_alignment.py` (8 tests), `output/tests/unit/
  test_progress_encoding.py`, and `code/tests/packaging/test_generate_then_execute.py`'s new
  `test_generate_then_execute_cp1252` (parametrized over all four registered theories).
- Policy documented in `code/docs/core/TESTING_GUIDE.md` §9 (Output-Encoding Testing, with
  subsections on why `StringIO` is not a valid encoding test, the `cp1252` `TextIOWrapper`
  recipe, the `PYTHONIOENCODING` subprocess recipe, and recorded scope boundaries), a new
  "Rendering and Output-Encoding Policy" section in `theory_lib/bimodal/docs/ARCHITECTURE.md`,
  and a pointer in `code/docs/core/CODE_STANDARDS.md`.

## Decisions

- Adopted option (b), stream-encoding-aware ASCII fallback, as the research report recommended —
  not a global `PYTHONIOENCODING`/`PYTHONUTF8` reconfiguration (invisible to a caller-constructed
  `TextIOWrapper` passed as `output=`) and not an ASCII-only mode (would discard Unicode
  presentation quality on every platform).
- Departed from the report's illustrative `⟹` → `=>` substitution being treated as a fixed-width
  replacement: derived the bimodal column budget from the actually-rendered arrow string instead,
  since a naive fixed 4-character budget overflows for both the 5-character ASCII form and
  two-digit durations.
- `output/progress`'s `TerminalDisplay.enabled`/isatty gate is explicitly left untouched — a
  progress-display behavior change, unrelated to encoding safety, out of this task's scope.
- `__repr__`'s verifier/falsifier glyph resolution is coupled to `sys.stdout` rather than left on
  the `output=None` default, once the end-to-end packaging leg proved that boundary was live
  (logos's own default example set embeds the null state in a verifier set) rather than
  theoretical — see Plan Deviations.

## Plan Deviations

- **Widened scope (found via execution, not grep)**: the report's 9-site inventory and 4-file
  blast radius were literal-character-grep-derived and missed `bitvec_to_substates`'s runtime
  -only `□` (null-state) glyph — invisible to a grep over theory source because the character is
  produced dynamically, not present as a literal in any calling file. This affected `logos`
  (previously believed clean) plus additional call sites in `exclusion`/`imposition`. Fixed by
  threading an optional `output` parameter through `bitvec_to_substates` itself (Phase 3), with a
  corrected Scope Hypothesis record left in place in the plan rather than silently rewritten.
- **Widened scope again (found via the end-to-end packaging leg, Phase 5)**: `WitnessProposition.
  __repr__` (exclusion) and `LogosProposition.__repr__` (logos) build their verifier/falsifier
  set display via `bitvec_to_substates` calls Phase 3 had deliberately left on the Unicode-only
  default, reasoning `__repr__` cannot receive a stream parameter. The real end-to-end
  `test_generate_then_execute_cp1252` leg proved that boundary live, not academic — logos's
  default `MOD_CM_1` example embeds the null state in a verifier set. Both `__repr__` methods now
  resolve against `sys.stdout` (the one stream they can ever reach, since they are only invoked
  through `print_proposition`'s own bare `print()`).
- **A concurrent, unrelated task (181, "decouple gating tests from bimodal solve cost") landed
  commits to two files this task also touched** (`code/tests/packaging/
  test_generate_then_execute.py` and `code/docs/core/TESTING_GUIDE.md`), in the same shared
  working tree. Both diffs compose cleanly and non-conflictingly (confirmed via read-through);
  committed together per-file since the changes are not separable via partial staging without
  risk. No hard constraint of this task was affected by that concurrent work.
- No plan phase was skipped, descoped, or completed with exclusions in the load-bearing sense —
  all 8 phases closed `[COMPLETED]`.

## Impacts

- All four theories (bimodal, logos, exclusion, imposition) can now print a countermodel to a
  `cp1252`-constrained stream (the real Windows pipe condition) without raising
  `UnicodeEncodeError` — verified end-to-end through the real installed console script for every
  registered theory.
- Bimodal's aligned world-history columnar renderer preserves alignment under ASCII substitution
  in both single- and two-digit-duration cases, and a pre-existing two-digit-duration overflow
  bug is fixed as a consequence.
- A new, durable non-ASCII output convention is recorded (`TESTING_GUIDE.md` §9,
  `theory_lib/bimodal/docs/ARCHITECTURE.md`, `CODE_STANDARDS.md` pointer): any future non-ASCII
  glyph on a print path must route through `model_checker.utils.glyphs` and carry a `cp1252`
  regression test in the same commit.
- No theory semantics, constraint generation, or solver behavior was touched — this is a
  print/display-layer fix only.

## Follow-ups

- The `TerminalDisplay.enabled`/`stream.isatty()` gate in `output/progress/display.py` remains
  hardcoded `True` ("Always enabled for testing") — explicitly out of scope, recorded in
  `TESTING_GUIDE.md` §9.4. A future task could re-enable it as its own, separately-scoped
  behavior change.
- The ~50 remaining non-ASCII `print(...)` sites in `theory_lib/meta_data.py`,
  `builder/project.py`'s `ask_generate()`-only `_print_success_message`, and standalone
  `jupyter/debug/*.py` diagnostic scripts are confirmed unreachable via the packaged CLI's piped
  output path (they are either interactive-`input()`-gated or run directly by a human, never
  through `subprocess.run(..., capture_output=True)`) and were left untouched as genuinely out of
  the report's own original scope. No action needed unless a future change routes one of these
  through a piped/redirected context.

## References

- `specs/182_fix_windows_unicode_encode_error_in_output/reports/01_windows-unicode-encode-error.md`
- `specs/182_fix_windows_unicode_encode_error_in_output/plans/01_stream-aware-ascii-fallback.md`
- `code/src/model_checker/utils/glyphs.py`
- `code/docs/core/TESTING_GUIDE.md` (§9)
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
