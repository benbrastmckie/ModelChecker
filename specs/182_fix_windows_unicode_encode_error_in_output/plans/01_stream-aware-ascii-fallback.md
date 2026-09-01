# Implementation Plan: Stream-Encoding-Aware ASCII Fallback for Printed Output

- **Task**: 182 - Fix the Windows `UnicodeEncodeError` in model output and establish a deliberate non-ASCII output policy
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/182_fix_windows_unicode_encode_error_in_output/reports/01_windows-unicode-encode-error.md`
- **Artifacts**: plans/01_stream-aware-ascii-fallback.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Printed model output writes raw non-ASCII glyphs (`⟹`, `→`, `↓`, subscript digits) to a
caller-supplied `output` stream. When that stream is a Windows pipe, Python falls off the
PEP-528 `WriteConsoleW` path and encodes with the ANSI codepage (`cp1252`), which cannot
represent those glyphs — every theory's `print_to`/`print_all` then dies with
`UnicodeEncodeError`. This plan adopts the research report's recommended remedy, **option (b):
a stream-encoding-aware ASCII fallback** — a single shared helper that probes
`getattr(output, "encoding", None)`, test-encodes the preferred glyph, and substitutes an ASCII
equivalent only when the target codec cannot represent it. Done means: all nine inventoried
print sites route through the helper, columnar alignment in bimodal's aligned renderers is
provably preserved under substitution, new regression coverage fails on today's code and passes
after the fix without a Windows runner, the packaging suite stays green with every existing
assertion unweakened, and the chosen policy is recorded as a durable convention.

### Research Integration

The plan is built directly on `reports/01_windows-unicode-encode-error.md` and does not
re-derive its findings. Specifically integrated:

- **The mechanism** (§1): `subprocess.run(..., capture_output=True)` in
  `code/tests/packaging/test_generate_then_execute.py` takes Windows stdout off the PEP-528
  console path; no `PYTHONIOENCODING`/`PYTHONUTF8` mitigation exists anywhere in the source or
  in `code/tests/packaging/conftest.py`'s `installed_venv` env construction. Phase 5 exploits
  the same lever *as a test harness* (`PYTHONIOENCODING=cp1252` on Linux reproduces the exact
  child-process condition); Phase 5 explicitly forbids adding it as a *mitigation* to the
  fixture env, which would mask the defect rather than fix it.
- **The 9-site inventory** (§2), including the two sites the traceback never named —
  `theory_lib/exclusion/semantic/model.py:536` and `theory_lib/imposition/semantic/model.py:172`.
  Phase 3 is scoped to that table, and Phase 2 asserts on it site-by-site.
- **The alignment evidence** (§3): `_create_time_positions`'s `+ 4  # Width + space for " ==> "`
  reserves a budget whose comment describes a 5-character ASCII arrow while the code renders a
  4-character Unicode one, and already overflows silently for two-digit durations. Phase 4 acts
  on this directly.
- **The testability constraint** (§5): the mandated technique passes a `cp1252`-encoded
  `TextIOWrapper` as the `output` **parameter**, not as `sys.stdout`. Every design element here
  targets `output`; nothing touches process-global interpreter state.
- **The adjacent progress-bar risk** (§2, "Adjacent but currently non-triggering"). See
  "Decision: `output/progress` is IN scope" below.

### Adopted Option and Rationale

**Option (b), stream-encoding-aware ASCII fallback, is adopted as recommended.** No defect was
found in the report's reasoning; the two supporting grounds were re-verified against the source
while planning:

- `bimodal/semantic/model.py`'s `_create_time_positions` does reserve a fixed per-column budget
  sized for an ASCII-shaped arrow, confirming the layout was not designed around the Unicode
  glyph (report §3).
- Option (a) is not exercisable by the mandated test: a `PYTHONIOENCODING`/`PYTHONUTF8` fix
  affects only `sys.stdout`/`sys.stderr` at interpreter start and is invisible to a
  caller-constructed `TextIOWrapper` passed as `output=`; and `output.reconfigure()` mutates a
  stream the caller owns and is not guaranteed to exist on arbitrary file-likes.
- Option (c) would discard the aligned-renderer presentation quality on every platform, which
  the task lists as a non-goal to protect.

**One departure from the report's illustrative glyph table is recorded here, with reason.** The
report suggests `⟹` → `=>`. Naively substituting a 2-character ASCII arrow into bimodal's
columnar renderer *widens* the arrow slot: `" ⟹₁ "` is 4 characters, `" =>1 "` is 5, which
overruns the reserved 4-character budget and would break the alignment the task's hard
constraints require to survive. This plan therefore does not treat the reserved width as a
constant at all: Phase 4 derives the column budget from the **actually rendered** arrow string,
so both the Unicode and the ASCII rendering are correctly reserved for, and the pre-existing
two-digit-duration overflow (report §3) is fixed as a consequence rather than left latent. The
substitution table stays readable (`=>`, `->`, `v`, plain digits) instead of being distorted
into a lossy one-character arrow purely to satisfy a hard-coded constant.

### Decision: `output/progress` is IN scope

The report flagged `output/progress/display.py` (`TerminalDisplay.enabled` hardcoded `True`,
isatty gate commented out) and `output/progress/animated.py`'s `_generate_bar` (unconditional
`█`/`░`) as the same defect class, currently non-triggering only because the generated default
`examples.py` never constructs a progress bar. **This plan fixes the glyphs (Phase 6) rather
than deferring them.** Grounds: the task's SCOPE directive is to *sweep the printed-output
paths*, not to patch the traceback; the block characters are equally absent from cp1252, so a
Windows user running any multi-model iteration would hit the identical crash immediately after
this task declares the crash fixed. The fix is confined to glyph selection.

**Explicitly still out of scope, and recorded as such in Phase 7's documentation:** re-enabling
the commented-out `stream.isatty()` gate on `TerminalDisplay.enabled`. That is a
progress-display *behavior* change with its own test-visibility consequences ("Always enabled
for testing"), unrelated to encoding safety, and it must not ride along in this diff.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only and is not modified by this plan (no `roadmap_flag`
was set, so no roadmap review/update phases are included). The relevant open item is Phase 1's
**"Merge and publish 1.3.0"**: the `Verify PyPI install (windows-latest)` matrix that surfaced
this defect is a release-gating leg, so every Windows leg of the release workflow is red until
this task lands. This work is a prerequisite for that roadmap item rather than an advance of it
in its own right; no roadmap item is completed by this plan.

## Goals & Non-Goals

**Goals**:
- Eliminate `UnicodeEncodeError` from every printed-output path for all four theories
  (bimodal, logos, exclusion, imposition) when the destination stream cannot encode the
  preferred glyph.
- Introduce exactly one shared glyph-resolution helper, keyed off the `output` parameter, and
  route all nine inventoried sites through it — no bespoke per-site branching.
- Preserve columnar alignment in bimodal's aligned world-history renderers under ASCII
  substitution, verified by an explicit alignment-invariant test, not by inspection.
- Add regression coverage that **fails on current code**, runs on Linux, and never requires a
  Windows runner.
- Keep the packaging suite green on Linux and macOS with every existing assertion intact.
- Record the non-ASCII output policy as a durable convention in `TESTING_GUIDE.md` and in the
  bimodal theory docs.

**Non-Goals**:
- Changing any theory's semantics, constraint generation, or solver behavior.
- Removing, replacing, or restructuring the aligned world-history renderer.
- Weakening, skipping, `xfail`-ing, or `continue-on-error`-ing any packaging assertion or any
  Windows CI leg.
- Global interpreter reconfiguration (`PYTHONUTF8`, `PYTHONIOENCODING`, `sys.stdout.reconfigure`)
  as the *fix* — including adding either to the packaging fixture env.
- Purging non-ASCII characters from docstrings, comments, operator documentation, or source
  prose. The policy governs the print path only.
- Re-enabling the commented-out `TerminalDisplay` isatty gate.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| ASCII arrow is wider than the Unicode arrow, breaking columnar alignment | H | H (certain with a naive `=>` substitution) | Phase 4 derives the column budget from the rendered arrow string instead of a constant; Phase 4's alignment-invariant test asserts per-column start indices agree across all rows in *both* renderings |
| Per-glyph `str.encode()` probing on every print call is hot-path expensive | M | M | Memoize the `(encoding, glyph) -> bool` predicate with `functools.lru_cache`; the glyph set is ~5 entries and encodings are few |
| `getattr(output, "encoding", None)` is absent (`io.StringIO`) and the default choice silently changes existing expected output | M | M | Default to the Unicode glyph when `.encoding` is `None`, exactly as the report specifies; Phase 2 pins this with a `StringIO` test asserting Unicode is still emitted |
| A print site exists that the 9-site inventory missed | M | M | Phase 5's end-to-end `PYTHONIOENCODING=cp1252` leg exercises the real CLI for all four theories and would surface any missed site as a nonzero exit; Phase 8 re-runs the repo-wide `grep -rnP '[^\x00-\x7F]'` sweep filtered to `print(`/`.write(` lines |
| `_to_subscript` is a `@staticmethod` with no access to `output`, so threading the stream through is an internal signature change | L | H (certain) | Confined to `bimodal/semantic/model.py`; both call sites are in the same class. Phase 3 updates signature and callers together and its verification enumerates them |
| Doubling the packaging suite's slowest test (bimodal ~100s) inflates CI time | L | H | The new leg reuses the existing `packaging`+`slow` markers and the 180s timeout, so it stays deselected from the gating selection exactly as the original is |
| Fixing the latent two-digit-duration overflow changes Unicode reference output | L | M | This is a bug fix, not a regression; Phase 4 records it in the summary and updates any expected-output fixture it breaks rather than reverting the width derivation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 6 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5, 7 | 3, 4, 6 |
| 5 | 8 | 5, 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Shared glyph-fallback helper [COMPLETED]

**Goal**: One shared, tested utility that decides whether a given stream can render a given
glyph and returns the appropriate Unicode-or-ASCII string. No call site is modified in this
phase.

**Tasks**:
- [x] Write `code/src/model_checker/utils/tests/unit/test_glyphs.py` FIRST (RED), covering:
  stream with `encoding="cp1252"` yields ASCII; stream with `encoding="utf-8"` yields Unicode;
  `io.StringIO` (no `.encoding` attribute) yields Unicode; an object whose `.encoding` is a
  bogus/unknown codec name yields ASCII rather than raising; `None` passed as the stream yields
  Unicode.
- [x] Create `code/src/model_checker/utils/glyphs.py` with:
  - A module-level substitution table mapping a semantic name to `(unicode, ascii)`:
    `DOUBLE_ARROW` (`⟹` / `=>`), `ARROW` (`→` / `->`), `DOWN_ARROW` (`↓` / `v`),
    `BLOCK_FULL` (`█` / `#`), `BLOCK_LIGHT` (`░` / `-`), and the subscript-digit map.
  - `stream_can_encode(encoding: str | None, text: str) -> bool`, `lru_cache`-memoized, returning
    `True` when `encoding` is `None`, else `text.encode(encoding)` succeeding; returns `False`
    on `UnicodeEncodeError` **and** on `LookupError` (unknown codec name).
  - `glyph(name: str, output) -> str` — resolves via `getattr(output, "encoding", None)`.
  - `to_subscript(n: int, output) -> str` — Unicode subscripts when encodable, plain ASCII
    digits (and `-`) otherwise. Both forms are exactly one character per digit, so this is
    width-neutral by construction.
- [x] Export the public names from `code/src/model_checker/utils/__init__.py` alongside the
  existing `from .formatting import ...` line.
- [x] Confirm the new unit tests go GREEN.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This plan asserts the substitution table needs exactly 5 glyph classes
plus the subscript-digit map, derived from report §2's 9-site table plus the progress-bar
glyphs. Confirm at implementation time by re-running
`grep -rnP '[^\x00-\x7F]' code/src/model_checker --include='*.py'` filtered to lines containing
`print(` or `.write(`; if a class outside this set appears, add it to the table in this phase
rather than branching at the call site.

**Files to modify**:
- `code/src/model_checker/utils/glyphs.py` - new module: substitution table, encodability
  predicate, `glyph()`, `to_subscript()`
- `code/src/model_checker/utils/__init__.py` - re-export the new public names
- `code/src/model_checker/utils/tests/unit/test_glyphs.py` - new unit tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/utils/tests/unit/test_glyphs.py -v` passes.
- The RED-then-GREEN transition is recorded (tests demonstrably failed before `glyphs.py`
  existed).
- `from model_checker.utils import glyph, to_subscript` resolves.

---

### Phase 2: Failing cp1252 regression coverage for the 9 print sites [COMPLETED]

**Goal**: Regression tests that reproduce the crash on Linux, one per inventoried site, and that
**fail on current code**. This phase deliberately lands red assertions before any call site is
touched, per the project's mandatory TDD requirement.

**Scope-Hypothesis correction, recorded per the pre-edit-verification-gate contract**: while
building the exclusion/imposition/logos regression tests below, `test_cp1252_via_print_all_does_not_raise`
surfaced a print-path defect the report's literal-character `grep` could not see: `→`/`Ō`-style
glyph
literals live in theory source, but `model_checker.utils.bitvector.bitvec_to_substates` returns
the literal `□` (U+25A1, "null state") glyph *at runtime* for bitvector 0 — invisible to a grep
over theory `.py` files because the character never appears in their source text. `all_states`
always includes state 0, so `print_states` (exclusion, imposition, logos) and several other
`bitvec_to_substates(...)` call sites in `exclusion/semantic/model.py` and
`imposition/semantic/model.py` hit this on nearly every model. This directly contradicts the
Phase 2 logos task item below ("assert logos is clean") and the report's §2 claim of zero
logos-local print hits — logos DOES have a print-path defect, just one a literal-character sweep
cannot find. A second, narrower instance of the same discovery-by-execution pattern was found in
`theory_lib/bimodal/semantic/proposition.py`'s `∅` fallback (reachable only via a bare `print()`
targeting `sys.stdout` directly, independent of the `output` parameter — see that file's own
comment, added in Phase 3, for the documented scope boundary this implies). Both glyphs
(`NULL_STATE` / `EMPTY_SET`) were added to Phase 1's `utils/glyphs.py` substitution table as part
of this phase's work (Phase 1 itself stays closed; this is an additive amendment to its already-
committed artifact, matching the "extend it here" instruction this phase's own Scope Hypothesis
below anticipates). The exclusion, imposition, and logos test files below were written with this
correction already applied (their `print_all`-level assertions exercise the null-state defect,
not just the report's originally named arrow site), so no rewrite was needed after the
discovery — see the implementation summary's Plan Deviations section for the full account.

**Tasks**:
- [x] Add a shared test helper that builds the constrained stream:
  `io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")`, plus a UTF-8 counterpart and
  a `StringIO` counterpart, so each site is asserted under all three. (Landed as
  `model_checker.utils.testing.make_encoding_test_streams`/`read_encoding_test_stream`, exported
  via `model_checker.utils`, rather than a bare local helper, so all five test files below share
  one implementation.)
- [x] `code/src/model_checker/models/tests/unit/test_structure_print_encoding.py`: exercise
  `_print_sentence_letter_differences`, `_print_semantic_function_differences`, and
  `_print_model_structure_differences` (report §2 lines 762 / 781 / 798) against the cp1252
  stream, following the existing `Mock(spec=ModelDefaults)` pattern already established in
  `models/tests/unit/test_structure_print.py`. Assert no `UnicodeEncodeError` and that `->`
  appears in the cp1252 rendering while `→` appears in the UTF-8 and `StringIO` renderings.
- [x] `code/src/model_checker/theory_lib/bimodal/tests/unit/test_print_encoding.py`: exercise
  `print_evaluation` (`⟹` + subscripts), `_create_world_line` / `print_world_histories`
  (columnar `⟹`), and `print_world_histories_vertical` (`↓`).
- [x] `code/src/model_checker/theory_lib/exclusion/tests/unit/test_print_encoding.py`: exercise
  the witness-function difference printing at report §2's `semantic/model.py:536`, plus (per the
  Scope-Hypothesis correction above) the `print_states`/`print_all`-level `□` null-state defect.
- [x] `code/src/model_checker/theory_lib/imposition/tests/unit/test_print_encoding.py`: exercise
  the imposition-relation printing at report §2's `semantic/model.py:172`, plus the same `□`
  null-state defect (imposed/world/outcome states include state 0 in the IM_TR_0 countermodel).
- [x] `code/src/model_checker/theory_lib/logos/tests/unit/test_print_encoding.py`: corrected per
  the Scope-Hypothesis note above -- logos is NOT clean. Pins the report's literal-grep claim
  (zero literal `→`/`⟹`/`↓` in `logos/semantic/model.py`, asserted via `inspect.getsource`) as
  still true, while separately exercising the real `print_states`/`print_all` null-state defect
  the grep could not see.
- [x] Run the new suite and **record the failures**; every cp1252 assertion must be red at this
  point. A green run here means the test does not reach the glyph and must be reworked before
  proceeding. (20 failed / 20 passed across all five files combined; every cp1252 assertion in the
  original 9-site + null-state scope failed with `UnicodeEncodeError` or a missing-ASCII-substitute
  `AssertionError`, and every UTF-8/StringIO control passed. One additional latent finding,
  recorded as a pre-existing separate defect and left untouched: `exclusion/semantic/model.py`'s
  `print_witness_functions` wraps its `print(...)` in a bare `except Exception: pass`, which
  silently swallows `UnicodeEncodeError` too -- `test_cp1252_stream_does_not_raise` therefore
  passes trivially for that one method; the load-bearing regression signal for it is
  `test_cp1252_stream_uses_ascii_arrow`, which correctly failed.)

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly 9 print sites across 5 files, taken from report
§2's table. Confirm at implementation time by checking each cited line still contains the cited
glyph (line numbers may have drifted); if a site has moved or a tenth exists, extend this
phase's coverage rather than deferring it to Phase 3.

**Files to modify**:
- `code/src/model_checker/models/tests/unit/test_structure_print_encoding.py` - new
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_print_encoding.py` - new
- `code/src/model_checker/theory_lib/exclusion/tests/unit/test_print_encoding.py` - new
- `code/src/model_checker/theory_lib/imposition/tests/unit/test_print_encoding.py` - new
- `code/src/model_checker/theory_lib/logos/tests/unit/test_print_encoding.py` - new

**Verification**:
- Every new cp1252 test FAILS with `UnicodeEncodeError` (or an assertion on the missing ASCII
  substitute) against unmodified source. Capture the failing output in the phase commit message.
- The UTF-8 and `StringIO` variants pass already, proving the tests exercise a live code path
  rather than erroring for an unrelated reason.

---

### Phase 3: Route the 9 print sites through the helper [COMPLETED]

**Goal**: Turn Phase 2's red tests green by resolving every inventoried glyph through the
Phase 1 helper. Alignment arithmetic is deliberately NOT touched here — that is Phase 4.

**Scope-Hypothesis correction (carried forward from Phase 2)**: this phase's file list is widened
beyond the plan's original 4 files. `theory_lib/logos/semantic/model.py` is NOT untouched, as the
Scope Hypothesis below originally predicted — `print_states`/`print_evaluation` there embed
`bitvec_to_substates`'s runtime-only `□` literal. Additionally, `model_checker/utils/bitvector.py`
(`bitvec_to_substates` itself) gained an optional `output=None` parameter (backward compatible:
unset stays Unicode) so every theory's `□` call sites can opt in without a bespoke per-theory
substitution; and each theory's `semantic/proposition.py` (`bimodal`, `exclusion`, `logos` --
imposition reuses logos's `Proposition`) needed a narrower, explicitly-commented fix for the
`EMPTY_SET`/`NULL_STATE` glyphs reachable through their bare `print()` (`print_proposition` does
not thread `output` at all -- see the in-line "NOTE (scope boundary)" comments landed at each
site, and the `__repr__` methods left deliberately unfixed for the reason recorded there).

**Tasks**:
- [x] `models/structure.py`: replace the three literal `→` occurrences in
  `_print_sentence_letter_differences`, `_print_semantic_function_differences`, and
  `_print_model_structure_differences` with `glyph("ARROW", output)`. These methods already
  receive `output: TextIO`, so no signature change is needed.
- [x] `theory_lib/exclusion/semantic/model.py`: replace the `→` in the witness-function
  difference print with `glyph("ARROW", output)`. Also routes 9 `bitvec_to_substates(...)` call
  sites through `output` (print_states/print_negation/print_witness_functions/print_evaluation)
  per the Scope-Hypothesis correction above.
- [x] `theory_lib/imposition/semantic/model.py`: replace the `→_` in the imposition-relation
  print with `glyph("ARROW", output) + "_"`, preserving the surrounding colour codes verbatim.
  Also routes 13 `bitvec_to_substates(...)` call sites through `output`.
- [x] `theory_lib/bimodal/semantic/model.py`:
  - `print_evaluation`: `f" {glyph('DOUBLE_ARROW', output)}{self._to_subscript(dur, output)} "`.
  - `_to_subscript`: change from `@staticmethod` to accept the output stream and delegate to
    `utils.glyphs.to_subscript`. Update BOTH call sites in the same edit.
  - `_create_world_line`: resolve the arrow through the helper (width handling in Phase 4).
    Gained an `output` parameter (threaded from its one caller, `print_world_histories`) since
    it did not previously receive one at all.
  - `print_world_histories_vertical`: replace `↓` with `glyph("DOWN_ARROW", output)`.
- [x] `theory_lib/logos/semantic/model.py` (added, per the Scope-Hypothesis correction): routes 6
  `bitvec_to_substates(...)` call sites (`print_model_differences`, `print_evaluation`,
  `print_states`) through `output`.
- [x] `model_checker/utils/bitvector.py` (added): `bitvec_to_substates` gains `output=None`,
  resolving `glyph("NULL_STATE", output)` for the null-state branch instead of the hardcoded `□`
  literal.
- [x] `theory_lib/{bimodal,exclusion,logos}/semantic/proposition.py` (added): each theory's
  `print_proposition` computes its `world_state`/warning-message glyphs against `sys.stdout`
  explicitly (`bitvec_to_substates(..., sys.stdout)` / `glyph("EMPTY_SET", sys.stdout)`), since
  the enclosing `print()` call is bare (no `file=output`) and always targets `sys.stdout`
  regardless of what stream the caller passed. `__repr__`'s own `bitvec_to_substates` calls
  (verifier/falsifier set display) are left on the `output=None` default and documented in-line
  as a known, deliberately out-of-scope boundary -- `__repr__` cannot receive a stream parameter
  through Python's string-formatting protocol.
- [x] Confirm no `output is sys.__stdout__` colour branch is altered — the encoding decision is
  a new, independent predicate layered beside the existing colour predicate, not a replacement
  for it. (Confirmed via diff read-through: every edit is additive around the existing colour
  branches, none of which changed.)
- [x] Run Phase 2's suite: all cp1252 assertions now GREEN, UTF-8 and `StringIO` assertions
  unchanged. (40/40 across all five `test_print_encoding.py`/`test_structure_print_encoding.py`
  files; the broader exclusion/imposition/logos `tests/unit/` suites -- 231 tests -- also pass,
  confirming no collateral breakage from the `bitvec_to_substates` signature change across its
  ~28 newly-threaded call sites.)

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the edit is confined to 4 source files
(`models/structure.py`, and `bimodal`/`exclusion`/`imposition` `semantic/model.py`) and that
`theory_lib/logos/semantic/model.py` needs no change. Confirm at implementation time with
`grep -nP '[^\x00-\x7F]' <file>` on each of the four theories' `semantic/model.py` restricted to
lines containing `print(`; logos must return zero such lines. If it does not, this phase's file
list is wrong and must be widened before the phase closes.

**Files to modify**:
- `code/src/model_checker/models/structure.py` - 3 arrow sites -> helper
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - 2 double-arrow sites,
  `_to_subscript` signature + both callers, 1 down-arrow site, `_create_world_line` gains `output`
- `code/src/model_checker/theory_lib/exclusion/semantic/model.py` - 1 arrow site + 9
  `bitvec_to_substates` call sites
- `code/src/model_checker/theory_lib/imposition/semantic/model.py` - 1 arrow site + 13
  `bitvec_to_substates` call sites
- `code/src/model_checker/theory_lib/logos/semantic/model.py` (added) - 6 `bitvec_to_substates`
  call sites
- `code/src/model_checker/utils/bitvector.py` (added) - `bitvec_to_substates` gains `output=None`
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` (added) - `EMPTY_SET`
  fallback resolved against `sys.stdout`
- `code/src/model_checker/theory_lib/exclusion/semantic/proposition.py` (added) -
  `bitvec_to_substates` resolved against `sys.stdout`; `__repr__` boundary documented
- `code/src/model_checker/theory_lib/logos/semantic/proposition.py` (added) -
  `bitvec_to_substates` resolved against `sys.stdout` (both the WARNING branch and
  `print_proposition`); `__repr__` boundary documented

**Verification**:
- All Phase 2 tests pass under cp1252, UTF-8, and `StringIO`. CONFIRMED: 40/40 green.
- `PYTHONPATH=code/src pytest code/src/model_checker/models code/src/model_checker/theory_lib -m "not packaging" -q` is green (no collateral breakage in existing print/format tests). Partially
  confirmed at phase-close time: exclusion (231 tests incl. imposition/logos unit dirs) green in
  16s; the bimodal-inclusive superset of this exact command was still running in the background
  past this phase's verification window (bimodal's solver is independently known-slow in this
  environment -- see task 181's decoupling work) and is re-run to completion as part of Phase 8's
  full-gate pass, which is this same command's authoritative closure point.
- `grep -nP '[^\x00-\x7F]' ` over the modified files shows remaining hits only in
  docstrings and comments, never on a `print(` line. CONFIRMED across all 10 modified files.

---

### Phase 4: Preserve columnar alignment under substitution [NOT STARTED]

**Goal**: Make bimodal's aligned world-history renderers compute their column budget from the
arrow actually rendered for the target stream, so alignment holds identically in Unicode and
ASCII mode — and prove it with an invariant test rather than by inspection.

**Tasks**:
- [ ] Thread the output stream into `_create_time_positions` so it can resolve the same arrow
  string `_create_world_line` will write.
- [ ] Replace the hard-coded `current_pos += column_widths[time] + 4  # Width + space for " ==> "`
  with a budget derived from `len(rendered_arrow)` for the arrow that will occupy that slot
  (including its duration subscript). Update the now-stale comment to describe the derivation,
  not a literal arrow.
- [ ] Confirm the vertical renderer's `↓` -> `v` substitution needs no width change (both are
  one character at a single computed offset) and record that in a comment so a future editor
  does not "fix" it.
- [ ] Add `code/src/model_checker/theory_lib/bimodal/tests/unit/test_world_history_alignment.py`
  asserting the **alignment invariant**: within a single rendering, the start column of each
  time-column's state token is identical across every world-history row, and the vertical
  renderer's arrow sits at the column centre of its own column. Assert this separately for the
  UTF-8 rendering and the cp1252 rendering. Do NOT assert that the two renderings have identical
  absolute columns — they legitimately differ because the arrow widths differ; the invariant is
  internal consistency within each.
- [ ] Include a two-digit-duration case, which overflows today (report §3), so the latent bug is
  covered by the new invariant rather than silently preserved.
- [ ] Update any existing expected-output fixture that the corrected width arithmetic shifts;
  record each such update in the phase commit message. Do not revert the derivation to keep an
  old fixture passing.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the only width-sensitive slot is the bimodal
world-history arrow column, and that the down-arrow and subscript substitutions are
width-neutral. Confirm at implementation time by running the new alignment invariant against
both renderings; a failure on the down-arrow or subscript case falsifies the hypothesis and
requires widening this phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - `_create_time_positions`
  budget derivation and stale comment; `_create_world_line` arrow plumbing
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_world_history_alignment.py` - new
- Any expected-output fixture the corrected arithmetic shifts (enumerate when found)

**Verification**:
- The alignment invariant test passes for the UTF-8 rendering AND the cp1252 rendering, single-
  and two-digit durations.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` is green.
- Visual spot-check of one bimodal world-history rendering under each encoding, pasted into the
  phase commit message, showing columns line up.

---

### Phase 5: End-to-end cp1252 coverage for all four theories [NOT STARTED]

**Goal**: Prove the four `test_generate_then_execute` cases pass under a cp1252-constrained
stream, using the real installed console script, on Linux, with no Windows runner — and without
touching a single existing assertion.

**Tasks**:
- [ ] Add a second parametrized test to
  `code/tests/packaging/test_generate_then_execute.py`, alongside (never replacing)
  `test_generate_then_execute`, that copies `installed_venv["env"]`, sets
  `PYTHONIOENCODING=cp1252`, and runs the same generated project through the same console
  script with `capture_output=True`. This reproduces the Windows child-process condition
  exactly: a piped stdout whose encoding is cp1252.
- [ ] Assert the same contract as the original: `returncode == 0`, no `Traceback` in stdout or
  stderr, and the `_MIN_OUTPUT_LINES` floor. Additionally assert the stdout contains no
  replacement character (`�`) — i.e. the fallback substituted rather than mangled.
- [ ] Reuse the existing `packaging` + `slow` markers and the 180s timeout, and reuse
  `handle_known_venv_libz3_link_failure`, so the new leg is deselected by the gating selection
  exactly as the original is.
- [ ] Verify the new leg FAILS if Phase 3/4 are reverted (sanity-check that it is a real
  reproducer, not a vacuous pass), then restore.
- [ ] Do NOT add `PYTHONIOENCODING` or `PYTHONUTF8` to `code/tests/packaging/conftest.py`'s
  `installed_venv` fixture env. Doing so would mask the defect in the original leg and make the
  new leg untestable.

**Timing**: 1 hour

**Depends on**: 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the parametrization covers exactly four theories via
`registry.get_registered()`. Confirm at implementation time from the live registry — the
existing `test_parametrization_count_matches_live_registry` guard already enforces this and
must be extended to cover the new test or shown to already cover it.

**Files to modify**:
- `code/tests/packaging/test_generate_then_execute.py` - add the cp1252 parametrized leg;
  existing tests and assertions untouched

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/packaging/test_generate_then_execute.py -v -m packaging`
  is green for all theories on both the ambient and the cp1252 leg.
- `git diff` on this file shows only additions — no existing assertion is modified, relaxed,
  marked `xfail`, or skipped.
- No `continue-on-error`, no marker change, and no CI workflow file is touched in this phase.

---

### Phase 6: Progress-bar glyph sweep [NOT STARTED]

**Goal**: Close the same defect class in `output/progress` so the fix is not immediately
re-broken by the first multi-model iteration a Windows user runs.

**Tasks**:
- [ ] Write the failing test first:
  `code/src/model_checker/output/tests/unit/test_progress_encoding.py`, constructing the
  progress display over a cp1252 `TextIOWrapper` and driving an update that renders a bar.
  Assert no `UnicodeEncodeError` and that ASCII `#`/`-` appear.
- [ ] `output/progress/animated.py`: resolve `█`/`░` in `_generate_bar` through
  `glyph("BLOCK_FULL", ...)` / `glyph("BLOCK_LIGHT", ...)` keyed off the display's stream.
  Both substitutes are one character, so the `BAR_WIDTH` arithmetic is unaffected.
- [ ] `output/progress/display.py`: expose the stream to the bar renderer if it is not already
  reachable, keeping `TerminalDisplay.__init__`'s `stream=sys.stdout` default.
- [ ] Leave `self.enabled = True` and the commented-out `stream.isatty()` line exactly as they
  are. Add a short comment marking the isatty question as deliberately out of this task's scope,
  pointing at the policy section Phase 7 writes.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - `_generate_bar` glyph resolution
- `code/src/model_checker/output/progress/display.py` - stream access for the renderer;
  out-of-scope comment on the isatty gate
- `code/src/model_checker/output/tests/unit/test_progress_encoding.py` - new

**Verification**:
- The new test is RED before the source edit and GREEN after.
- `PYTHONPATH=code/src pytest code/src/model_checker/output -q` and
  `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/test_progress.py code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py -q` are green — existing
  progress tests still see the Unicode bar under `StringIO`.
- `git diff` shows `TerminalDisplay.enabled` unchanged.

---

### Phase 7: Record the non-ASCII output policy [NOT STARTED]

**Goal**: Turn the choice into a durable, discoverable convention, as the task explicitly
requires — not just a patch.

**Tasks**:
- [ ] Add a new numbered section to `code/docs/core/TESTING_GUIDE.md` after §8 ("Best Practices
  and Patterns") and before the Quick Reference, titled for output-encoding testing. Content:
  why `io.StringIO` is NOT a valid encoding test (it never encodes, so it can never raise);
  the canonical `io.TextIOWrapper(io.BytesIO(), encoding="cp1252")` recipe; the
  `PYTHONIOENCODING=cp1252` subprocess recipe for end-to-end legs; and the standing rule that
  any new non-ASCII glyph on a print path requires a cp1252 test in the same commit.
- [ ] Add a rendering/output-encoding policy subsection to
  `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` (bimodal owns the aligned
  renderer most affected): state the adopted option (b), the substitution table, the rule that
  the arrow column budget is derived from the rendered arrow rather than hard-coded, and the
  alignment invariant that any future renderer change must preserve.
- [ ] Add a short pointer in `code/docs/core/CODE_STANDARDS.md` so the convention is reachable
  from the coding-standards entry point, linking to the two sections above rather than
  duplicating them.
- [ ] Record the two explicitly deferred items in the TESTING_GUIDE section: the
  `TerminalDisplay` isatty gate, and the standing prohibition on adding
  `PYTHONIOENCODING`/`PYTHONUTF8` to the packaging fixture env as a mitigation.
- [ ] Cite durable anchors only (file names, section headings). Per
  `.claude/rules/no-task-references-in-deliverables.md`, no task numbers appear in any file
  outside `specs/**`.

**Timing**: 1 hour

**Depends on**: 3, 4, 6

**Verification Tier**: prose

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` - new output-encoding testing section
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - rendering policy subsection
- `code/docs/core/CODE_STANDARDS.md` - pointer to the above

**Verification**:
- Diff read-through confirms every changed hunk is prose/markdown with no code surface.
- `TESTING_GUIDE.md`'s table of contents is updated to include the new section, and its numbering
  is consistent with the existing §1-§8.
- `grep -nEi 'task [0-9]' ` over the three modified files returns nothing.

---

### Phase 8: Full-gate verification and hard-constraint audit [NOT STARTED]

**Goal**: Confirm the whole gate set is green and that none of the task's hard constraints were
traded away to get there.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -m "not packaging" -q` —
  full gating suite green.
- [ ] `PYTHONPATH=code/src pytest code/tests/packaging/ -v -m packaging` — packaging suite green
  on Linux, both the ambient and the new cp1252 leg.
- [ ] Re-run the inventory sweep:
  `grep -rnP '[^\x00-\x7F]' code/src/model_checker --include='*.py'` filtered to lines containing
  `print(` or `.write(`. Every remaining hit must be inside a docstring/comment, or must be a
  helper-resolved glyph literal inside `utils/glyphs.py` itself. Any other hit is an unfixed site.
- [ ] Hard-constraint audit against the full diff:
  - No packaging assertion weakened, deleted, relaxed, `xfail`-ed, or skipped.
  - No CI workflow file modified; no `continue-on-error` anywhere.
  - No theory semantics or solver behavior touched — diff contains no change to constraint
    generation, operator definitions, or Z3 interaction.
  - The aligned world-history renderer still exists and its alignment invariant test passes.
- [ ] Confirm the macOS leg's expectations are unchanged: nothing in the diff is
  platform-conditional, so macOS behavior is identical to Linux by construction. State this
  explicitly in the summary rather than claiming a macOS run that was not performed.

**Timing**: 0.75 hours

**Depends on**: 5, 7

**Verification Tier**: full

**Verification**:
- Both pytest invocations above exit 0, with counts recorded in the implementation summary.
- The sweep produces zero unresolved print-path hits.
- Each of the four hard-constraint audit bullets is answered with concrete diff evidence, not an
  assertion.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/utils/tests/unit/test_glyphs.py -v`
- [ ] All five new per-theory/shared `test_print_encoding` modules pass under cp1252, UTF-8, and
      `StringIO`; each was demonstrably RED before Phase 3.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_world_history_alignment.py -v` — alignment invariant holds in both encodings, single- and
      two-digit durations.
- [ ] `PYTHONPATH=code/src pytest code/tests/packaging/test_generate_then_execute.py -v -m packaging` — four theories x two encoding legs, all green.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/output -q` — progress-bar coverage green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -m "not packaging" -q` — full
      gating suite green, no regressions.
- [ ] Repo-wide non-ASCII print-path sweep returns zero unresolved sites.

## Artifacts & Outputs

- `code/src/model_checker/utils/glyphs.py` — new shared glyph-fallback helper
- `code/src/model_checker/utils/__init__.py` — updated exports
- Updated print paths: `models/structure.py`, `theory_lib/bimodal/semantic/model.py`,
  `theory_lib/exclusion/semantic/model.py`, `theory_lib/imposition/semantic/model.py`
- Updated progress rendering: `output/progress/animated.py`, `output/progress/display.py`
- New tests: `utils/tests/unit/test_glyphs.py`,
  `models/tests/unit/test_structure_print_encoding.py`, four per-theory
  `tests/unit/test_print_encoding.py`,
  `theory_lib/bimodal/tests/unit/test_world_history_alignment.py`,
  `output/tests/unit/test_progress_encoding.py`
- Extended `code/tests/packaging/test_generate_then_execute.py` (cp1252 leg, additive only)
- Policy documentation: `code/docs/core/TESTING_GUIDE.md`,
  `theory_lib/bimodal/docs/ARCHITECTURE.md`, `code/docs/core/CODE_STANDARDS.md`
- Implementation summary at
  `specs/182_fix_windows_unicode_encode_error_in_output/summaries/01_*-summary.md`

## Rollback/Contingency

- Every phase is an independent commit, so a single phase can be reverted with
  `git revert <sha>` without unwinding the rest. Phases 1, 2, 6, and 7 are additive and safe to
  revert in isolation.
- If Phase 4's derived column budget proves unworkable (e.g. a fixture surface too large to
  update within the phase's timebox), the contingency is a **width-neutral one-character ASCII
  arrow** (`⟹` -> `>`) for the columnar renderer only, keeping the two-character `=>` for the
  non-columnar `print_evaluation` path. This preserves alignment with zero arithmetic change.
  It is the fallback, not the default, because it leaves the pre-existing two-digit-duration
  overflow unfixed — and if taken, that must be recorded as a known-remaining defect in the
  summary rather than passed over silently.
- If Phase 6 destabilizes existing progress tests beyond its timebox, revert Phase 6 alone and
  re-record `output/progress` as out of scope in Phase 7's documentation, with a follow-up task
  spawned. The core crash fix (Phases 1-5) stands independently.
- Under no contingency is a packaging assertion weakened, a Windows CI leg marked
  `continue-on-error`, or `PYTHONIOENCODING`/`PYTHONUTF8` added to the fixture env to reach
  green. If the fix cannot be made to work, the task is reported blocked with the crash intact.
