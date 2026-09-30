# Research Report: Improve Printed Model Display and Colors

## Scope

Display/formatting only. Certificate/lasso semantics are untouched; only `print_*` methods,
formatting helpers, and their tests are in scope, per the dispatch's `CONTEXT` note.

Primary target: `code/src/model_checker/theory_lib/bimodal/semantic/model.py` (720 lines),
`semantic/proposition.py`, `semantic/render.py`. Cross-theory scope: `theory_lib/{logos,
exclusion,imposition}/semantic/model.py`.

## Method

- Read all of `bimodal/semantic/model.py`, `proposition.py`, `render.py`,
  `utils/glyphs.py`, `output/color.py` in full.
- Ran `code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py` both plainly
  and under `script -qec ... /tmp/...` (pty capture, live colors), with and without `-a`.
- Cloned comparison: read and ran the benchmark
  (`/home/benjamin/Projects/Logos/ModelChecker`, branch `practice`,
  `code/src/model_checker/theory_lib/bimodal/semantic.py`) under the same pty capture, same
  example file, for a byte-for-byte SGR-code and line-width comparison.
- Grepped all three sibling theories' `print_evaluation`/`print_all` for the legacy
  `output is sys.__stdout__` color test.
- Confirmed no existing test locks the string shapes this task must change (`repr` of
  `BimodalProposition`, the `Verification:`/`Evaluation point:` line text) before proposing
  changes to them.

## Findings

### 1. Line-width blowout — confirmed, two independent causes

Measured directly (non-`-a` default view, full `examples.py` run):
- Longest line: 234 chars (the `Verification:` line — present in **every** example, `-a` or
  not; `-a` only changes the `Histories:` block, so this defect is orthogonal to
  `align_vertically`).
- 6 of 34 history rows exceed 80 cols (max 98) — caused by `_print_history_lines`
  (`model.py:445-460`) padding every row's prefix to `role_width =
  max(len(role) for role in roles.values())` (`model.py:453`). A role like `witness for
  \Box \neg A, \Box \neg (A \vee B)` (measured live, 49 chars including the prefix content)
  right-shoves every row's arrow chain, including `L0  main`.
- Benchmark's longest line (pty-captured, same example file): 80 chars exactly.

Both root causes are independently fixable:
- `_verification_label` (`model.py:556-583`) builds one unwrapped sentence, consumed by
  `print_evaluation` (`model.py:637`) as a single `print(f"Verification: {...}\n")`. No
  wrapping infrastructure exists in this module today (no textwrap import, no line-break
  logic anywhere in `model.py`).
- The role-width padding is local to `_print_history_lines`; `_print_history_table`
  (the `-a` view, `model.py:490-531`) already avoids the per-row repetition by putting the
  role once in the column header (`f"L{index} {roles[index]}"`, `model.py:502`) rather than
  on every row — but a single very long role name still elongates that header: with the
  `witness for \Box \neg A, \Box \neg (A \vee B)` example, `-a`'s header line reached 119
  chars (still far under the default view's 234, but not itself under 80). **`-a` mitigates
  but does not eliminate the long-role problem**; a full fix (truncation, folding into `Box
  guesses:`, or a verbosity flag) is needed independent of which view is default.
- `_print_box_guesses` (`model.py:533-554`) already prints `falsified at L{i}, t=±t` for
  every false box — this is exactly the information a `witness for □χ` role conveys, just
  keyed the opposite direction (by formula rather than by lasso). Folding the role into that
  table (dispatch's suggestion) would need a formula-or-lasso-keyed cross-reference, e.g.
  annotating each `Box guesses:` row's falsifier as `falsified at L{i} (below), t=±t` while
  the history row becomes a bare `L{i}  witness` (no formula list) or drops the role column
  entirely and instead numbers/cross-refs it from the table. This is a genuine design choice,
  not a mechanical fix — flagging as an open question for the plan phase (see below).

### 2. Ambiguous lasso-index reprs — confirmed, isolated, low-risk fix

`BimodalProposition.__repr__` (`proposition.py:108-109`):
```python
def __repr__(self) -> str:
    return f"< {pretty_set_print(self.truth_set)}, {pretty_set_print(self.false_set)} >"
```
`self.truth_set`/`self.false_set` are `Set[int]` of **lasso indices** (set in `__init__` via
`_find_proposition_at`, `proposition.py:103,162-179`), so `pretty_set_print({0})` renders the
bare string `{0}` — confirmed live: `|A| = < {0}, {} >` next to `t=-2` on the same printed
line (`print_proposition`, `proposition.py:201-204`).

Both sibling theories already avoid this ambiguity: `logos/semantic/proposition.py:401` and
`exclusion/semantic/proposition.py:104` both pass the result of `bitvec_to_substates` (named
world states, `a`/`b`/...) through `pretty_set_print`, never bare indices — bimodal is the
outlier, not the norm.

**Fix is low-risk and localized.** Grepped every test referencing `truth_set`/`false_set`
(`code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py:62-63,165-166`):
all assertions are against the raw `Set[int]` attributes (e.g. `proposition.truth_set ==
{0}`), never against `__repr__`'s string output — and the one test that does check printed
text (`test_print_proposition_does_not_raise`, line 168-181) asserts only `"|A|" in
captured.out` and `"(True at L0, t=0)" in captured.out`, neither of which pins the `< {0}, {}
>` shape. Changing `__repr__` to map indices through `f"L{i}"` before `pretty_set_print`
(matching the `L{i}` naming already used everywhere else in the block) requires no change to
`truth_set`/`false_set` themselves and breaks no existing assertion.

### 3. Evaluation point — confirmed terse; benchmark's shape is concrete and portable

Current (`print_evaluation`, `model.py:621-638`): exactly two lines, `Evaluation point: L0 at
t=-2` (only `L0 at t=-2` is colored blue) and `Verification: ...`.

Benchmark (`semantic.py:2391-2435`, method name `print_evaluation` there too) prints a
4-line, fully-blue block, confirmed live for `TN_CM_1`:
```
Evaluation Point:
  World History W_0: a ⟹₁ b
  Time: 0
  World State: a
```
All three inner lines opened with their own `\033[34m...\033[0m` (3 separate BLUE/RESET
pairs, not one wrapping the whole block) — confirmed by the pty capture's SGR tally (`3` `[34m`
occurrences for this example, see Finding 5). For bimodal's certificate encoding, the
structurally equivalent inputs are already all on `self` at print time: `self.certificate`
(the lasso chain, reusable via the same `_history_cells`/`_join_history` helpers already used
in the `Histories:` block — including duration subscripts once Finding 4 is done),
`self.target_time`, and `self.main_point` (`{"lasso": i, "position": t}`). A 4-line block
naming the lasso, its arrow chain, the time, and the state-at-that-position is a mechanical
transcription of data already computed for `_print_history_lines`; no new certificate-reading
logic is needed, only new print statements (possibly a small `_history_line_for(index)`
helper factored out of the loop body in `_print_history_lines` so both call sites share it).

### 4. No arrow duration — confirmed; benchmark's `_to_subscript` is a 6-line static method

Benchmark (`semantic.py:2437-2442`):
```python
@staticmethod
def _to_subscript(n):
    sub = {'0': '₀', ..., '-': '₋'}
    return ''.join(sub.get(c, c) for c in str(n))
```
used as `f" ⟹{self._to_subscript(dur)} "` where `dur = sorted_times[i+1] - time`.

This repository already has the exact functional equivalent, encoding-aware and tested:
`utils/glyphs.py::to_subscript(n, output)` (lines 153-172), which the module docstring notes
is "width-neutral by construction" and needs no extra column-budget handling (unlike the
arrow glyphs). **No new glyph entry is needed** — `to_subscript` already exists and is
unused by bimodal's `_join_history` (`model.py:424-443`) today. Adding a
duration-subscripted arrow is: compute the gap between adjacent representative positions
(always `1` under the current `target_window()`, since `back`/`mid`/`fwd` positions are
consecutive integers — so today this would always render `₁`; the visible benefit only shows
up if/when the window ever skips positions) — needs `to_subscript` imported into `model.py`
and threaded through `_join_history`'s arrow construction. Per `TESTING_GUIDE.md` section 9,
any print path is covered under the existing `cp1252` regression discipline: since
`to_subscript` is itself already unit-tested (implied by its docstring contract) and the
existing `TestGlyphFallbacks`/`test_table_cp1252_leg_does_not_raise` pattern in
`test_structure.py` shows the sanctioned recipe (`make_encoding_test_streams` +
`read_encoding_test_stream`), the new call site needs one additional assertion in that
existing style, not a new test module.

### 5. Color coverage — confirmed narrower, but exact counts differ from the dispatch's figures

Directly measured via pty capture (`script -qec`) of the identical `TN_CM_1` example in both
repos:

| | non-reset SGR occurrences | distinct SGR values used |
|---|---|---|
| Benchmark (`practice` branch) | 13 | `31`,`32`,`33`,`34`,`37` (5 values) |
| Here (current) | 10 | `31`,`32`,`33`,`34`,`37`,`90`,`1;34` (7 values) |

The dispatch's "5 distinct SGR codes" for the current repo does not match what I measured
(10 occurrences / 7 values) — likely the dispatch's screenshot used a different example or
counted differently (e.g. only `model.py`'s own palette constants, excluding the
`print_proposition`/`set_colors` green/red/white/yellow that come from
`models/structure.py`'s framework code, not from `model.py`). Either way, the **direction**
the dispatch names is confirmed: this repo's total colored-span count is measurably lower
than the benchmark's (10 vs 13) for the same example, even though both use materially the
same five-color vocabulary (blue/white-gray/green/red/yellow — bimodal's `_GRAY` at `90` is a
brighter/different ANSI code than the benchmark's plain `37`, and bimodal additionally has
`_HILITE` at `1;34` for the bracketed evaluation cell, which the benchmark's `Histories`
block does not bold). The declared palette in `model.py` (`_BLUE`/`_HILITE`/`_GRAY`/`_GREEN`/
`_RED`, `model.py:353-358`) is sound per `CODE_STANDARDS.md`'s "Printed Output Conventions"
(color never carries information alone, plain fallback always present) — the benchmark's
extra coverage comes from wrapping every one of the 4 `Evaluation Point:` lines' *labels* in
blue (not just the value), and from the nested nested-nested subsentence lines under
`INTERPRETED PREMISE`/`CONCLUSION` alternating white(37)/yellow(33) at each recursion depth —
a `models/structure.py`-level convention (`set_colors`) already shared by every theory, not
bimodal-specific. Extending bimodal's own coverage (the `Evaluation point:`/new multi-line
block, per Finding 3) to color the label text as well as the value, matching the benchmark's
"every line of the block is blue" convention, is the concrete, in-scope lever; nothing here
suggests inventing a new color meaning.

### Cross-theory scope: `sys.__stdout__` audit — no defect found, all three already correct

Read all three named `sys.__stdout__` sites in full:
- `logos/semantic/model.py:141`
- `exclusion/semantic/model.py:338`
- `imposition/semantic/model.py:120`

**All three are the `Total Run Time` footer gate inside `print_all`**, structurally identical
to bimodal's own legitimate case at `model.py:676`:
```python
if output is sys.__stdout__:
    total_time = round(time.time() - self.start_time, 4)
    print(f"Total Run Time: {total_time} seconds...", file=output)
```
None of the three is a color-gating use. Each theory's own `print_evaluation` already calls
`use_colors(output)` correctly (`logos/semantic/model.py:266`,
`exclusion/semantic/model.py:548`; imposition's `print_imposition` similarly at
`imposition/semantic/model.py:139` — its own `print_evaluation` was not located as a separate
override, meaning imposition likely inherits `print_evaluation` from a shared base or defines
it elsewhere; worth a plan-phase Grep across `imposition/` specifically for `print_evaluation`
to confirm scope, since this report did not exhaustively locate it). **No fix is needed for
the `sys.__stdout__` audit itself** — the dispatch's "audit each" instruction is satisfied by
this finding: the pattern is already compliant everywhere it was flagged.

### Cross-theory scope: `The evaluation world is:` single-line block

`logos/semantic/model.py:270` and `exclusion/semantic/model.py:552` both print:
```python
f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N, output)}{RESET}\n"
```
one line, colored value only (matching bimodal's current terse `Evaluation point:` line,
Finding 3's "before" state). These two (and imposition's presumed equivalent, not located in
this pass) are candidates for the same multi-line-block treatment once bimodal's shape is
decided — but they have no lasso/history chain to reproduce (their model is a single
bitvector world, not a certified lasso family), so "the same treatment" cannot mean a literal
copy of bimodal's block; it means matching visual weight/color convention. This is a plan-time
design decision, not a mechanical port.

### Existing test infrastructure (for the plan phase)

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_render.py` (163 lines) — pins
  `render`/`build_names`'s two rendering routes and their `cp1252` fallbacks. No changes
  needed here unless `render.py` itself changes (it is not modified by any finding above).
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` (149+
  lines) — the dispatch's acceptance criteria names this as `tests/integration/
  test_output_gate.py`; the actual path is
  `theory_lib/bimodal/tests/integration/test_output_gate.py` (there is no
  `code/tests/integration/test_output_gate.py`). It already asserts `out.count("Verification:")
  == 1` and a `FORBIDDEN_OVERCLAIM` string-absence check across all four `verify` scenarios —
  any change to `_verification_label`'s wrapping (Finding 1) or the `Evaluation point:` block
  shape (Finding 3) must keep these assertions passing (the count-1 and forbidden-phrase
  checks do not care about line-wrapping, so they should survive unchanged) and is the natural
  home for new max-line-width / golden-output assertions per the dispatch's ACCEPTANCE
  section, since it already exercises `print_certificate` + `print_evaluation` together
  across representative examples.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — `TestAlignedHistoryTable` (line 585+) and `TestColorGating` (line 659+) are the closest existing
  precedent for the new tests this task needs: `TestColorGating.test_tty_output_carries_colors_and_pipes_do_not`
  is the sanctioned pattern for asserting `"\033[" in`/`not in` output under a fake-tty
  `io.StringIO` subclass, and `test_table_cp1252_leg_does_not_raise` is the sanctioned pattern
  for the new glyph's regression test (Finding 4).
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` — confirmed
  above (Finding 2) that no assertion needs updating for the `__repr__` fix, but a new
  assertion (`"< {L0}, {} >" in repr(proposition)` or equivalent) should be added here to pin
  the new unambiguous shape.

### Documentation that also names the current (soon-to-change) shapes

`bimodal/semantic/model.py`'s own module docstring (lines 69-85, "Printed output") and
`bimodal/docs/ARCHITECTURE.md`'s "Rendering Policy" section (lines 276-314) are both a
**durable, explicit description of the current printed shapes** — e.g. "exactly one
`Verification:` line", "a `Histories:` row is `L{i}  {role}  …`". Either of these is directly
invalidated by Findings 1 and 3's proposed changes and will need updating in the same
implementation pass — `docs/SETTINGS.md`'s `align_vertically` row (`SETTINGS.md:167`) is a
third location describing the same arrow-chain shape and should be checked too. This is not
optional cleanup: `utils/glyphs.py`'s own docstring calls `ARCHITECTURE.md`'s "Rendering
Policy" section "the durable record of this convention", so leaving it stale after a print-
shape change would contradict this repository's own stated documentation discipline.

### No existing 80-column standard is written down

Grepped `CODE_STANDARDS.md` and `TESTING_GUIDE.md` for "80 col"/"line width"/"line length":
no hits. The ~80-column target this task pursues comes entirely from the benchmark
comparison (its measured max of 80), not from a pre-existing written repository standard. The
plan should either (a) treat 80 as an empirically-derived target tied to this task's
acceptance test only, or (b) additionally propose codifying it in `CODE_STANDARDS.md`'s
"Printed Output Conventions" section — a scope decision for the plan phase, not something
this research can decide unilaterally.

## Open Questions for the Plan Phase

1. **Role-column strategy** (Finding 1): truncate/abbreviate long role names in
   `_print_history_lines`, move roles onto their own line, or fold role provenance entirely
   into `Box guesses:` and drop the per-row role column from the default view. Each has
   different test and documentation impact.
2. **Verbosity flag vs. always-wrap** for `_verification_label` (Finding 1): wrap the existing
   long sentence at a column budget, or shorten the default text and gate the long form behind
   a new setting/flag (the dispatch's own suggested alternative). A new setting requires
   `settings/types.py` and `SETTINGS.md` updates.
3. **Exact shape of bimodal's new multi-line evaluation block** (Finding 3): the benchmark's
   4-line block names `World History`, `Time`, `World State` for a single non-periodic
   timeline; bimodal's certificate has a periodic lasso with back/mid/fwd segments plus a
   named role (`main`) — the plan should specify the exact line contents (e.g. reuse
   `_history_cells`/`_join_history` for the "arrow chain" line verbatim, or render only the
   representative window around `target_time`).
4. **Whether/how to extend the identical treatment to logos/exclusion/imposition's one-line
   `The evaluation world is:`** (Cross-theory scope): these theories have no lasso chain, so
   "same treatment" must be reinterpreted as "same visual weight and full-block coloring", not
   a literal structural copy.
5. **imposition's `print_evaluation`** was not located in this pass (only `print_imposition`
   and the `sys.__stdout__` footer site were confirmed) — the plan phase should Grep
   `imposition/semantic/model.py` (and any imported base class) specifically for
   `print_evaluation` before writing cross-theory changes.

## Files Read (for plan-phase reference, no line-number drift expected)

- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` (720 lines, read in full)
- `code/src/model_checker/theory_lib/bimodal/semantic/proposition.py` (204 lines, read in full)
- `code/src/model_checker/theory_lib/bimodal/semantic/render.py` (185 lines, read in full)
- `code/src/model_checker/utils/glyphs.py` (172 lines, read in full)
- `code/src/model_checker/output/color.py` (47 lines, read in full)
- `code/docs/core/CODE_STANDARDS.md` lines 609-631 ("Printed Output Conventions")
- `code/docs/core/TESTING_GUIDE.md` lines 1450-1543 (section 9, output-encoding testing)
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` lines 276-314 (Rendering
  Policy)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_render.py` (full)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` (full)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` lines 580-720
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_proposition.py` lines 140-182
- `code/src/model_checker/utils/formatting.py` (`pretty_set_print`, lines 12-32)
- Benchmark: `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py` lines 2229-2660 (`print_evaluation`, `_to_subscript`,
  `print_world_histories`, `print_world_histories_vertical`)
- `theory_lib/{logos,exclusion,imposition}/semantic/model.py` — grepped for
  `sys.__stdout__`/`print_evaluation`, read the matching regions in full for logos and
  exclusion; imposition's `print_evaluation` not located (see Open Question 5)
