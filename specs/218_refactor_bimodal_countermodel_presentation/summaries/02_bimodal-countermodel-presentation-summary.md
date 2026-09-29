# Implementation Summary: Arrow-Chain Histories as the Default (Round 2)

- **Task**: 218 - Refactor bimodal/ theory countermodel presentation
- **Plan**: plans/01_bimodal-countermodel-presentation.md (revised; Phases 8-9 of 9, both COMPLETED;
  Phases 1-7 were closed in round 1, see summaries/01_bimodal-countermodel-presentation-summary.md)
- **Session**: sess_1790656279_e5bb8c (dispatch 5)

## What Changed

The default bimodal history block is now a time-labelled arrow chain in the old Logos style,
under a `Histories:` heading with a one-line legend, one aligned row per lasso:

```
Histories:  (one row per lasso: (t:atoms) states joined by ⟹, … marks the periodic back/fwd segments, | separates back | mid | fwd, [ ] marks the evaluation point)
  L0  main                … [-2:B] ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L1  witness for \Box A  … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L2  reserved, unused    … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:B) …
  L3  witness for \Box B  … (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ (+2:A) …
```

Every state is `(t:atoms)` (signed time via `render.signed_time`, atoms via `_format_label`:
`A`, `{A,B}`, `∅`); `⟹` joins adjacent states within the periodic back/fwd segments; `|`
separates back | mid | fwd (an empty `mid` collapses to one `|`); `…` brackets the periodic
segments; `[ ]` replaces `( )` on the evaluation point of the main lasso; each position's column
is padded to its widest cell over all lassos so times align across rows. `⟹` and `…` go through
`utils/glyphs.py` (`DOUBLE_ARROW` existed; `ELLIPSIS` is new: `…` survives cp1252 as 0x85, `...`
only on `ascii`); the `OMEGA` entry and the `(back)^ω | mid | (fwd)^ω` one-liner are gone. The
heading is `Histories:` on the default, `-a`, and no-certificate paths; `Certificate:` is printed
nowhere. The role column, `Box guesses:` table, `Search bounds:` line, `Evaluation point:`, the
single `Verification:` line, and the `-a` table body are unchanged. Semantics untouched
(`witness_constraints.py`, `formula.py` not in the diff).

## Files

- `code/src/model_checker/utils/glyphs.py` -- `ELLIPSIS` added, `OMEGA` removed, docstring/comment
- `code/src/model_checker/utils/tests/unit/test_glyphs.py` -- ELLIPSIS cp1252/ascii/utf-8 legs; OMEGA-retired test
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` -- `_format_state`, `_history_cells`
  (fail-fast on segment-length mismatch), `_join_history`, rewritten `_print_history_lines`;
  `_format_lasso` deleted; `Histories:` headings/legends; module docstring
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` --
  `TestGoldenOutputHistoriesFormat` (shape regex, joiner-column alignment, hand-built
  differing-width family, cp1252 + ascii + utf-8 legs), `TestPrintingDoesNotClaimValidity`
  and `TestAlignedHistoryTable` pins
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py`,
  `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` -- `Histories:` pins
- `code/src/model_checker/theory_lib/bimodal/README.md`, `docs/SETTINGS.md`, `docs/ARCHITECTURE.md`,
  `docs/USER_GUIDE.md` -- samples regenerated from live captures; prose updated
- `code/src/model_checker/theory_lib/bimodal/examples.py`, `semantic/core.py` -- comments
- `code/tests/packaging/test_generate_then_execute.py`, `code/docs/core/TESTING_GUIDE.md` 9.3 --
  cp1252 harness decode fix (see Plan Deviations)

## Verification

- Bimodal + utils suites: 852 passed. Builder e2e `test_full_pipeline.py`: 3 passed.
- Full suite, first run (before the harness fix): 3416 passed, 5 skipped, 1 failed
  (`test_generate_then_execute_cp1252[bimodal]`, parent-side `UnicodeDecodeError`, see below).
  After the harness fix all four cp1252 packaging legs pass (4 passed); full-suite re-run:
  3417 passed, 5 skipped, 0 failed (526s).
- Live `./dev_cli.py .../bimodal/examples.py | cat -v | grep -c '^['`: 0 (default and `-a`);
  `MD_CM_1` prints the four rows above with joiners at identical columns; `Certificate:` count 0.
- `PYTHONIOENCODING=cp1252` subprocess legs (default and `-a`): no `UnicodeEncodeError`, `=>`
  in place of `⟹`, `…` retained; `PYTHONIOENCODING=ascii`: `...` and `=>`.
- `ruff check` clean on `model.py`, `glyphs.py`, and the packaging test; task-reference grep
  clean over every touched `code/` file; residual `(back)^`/`Certificate:` grep over the bimodal
  README/docs/comments returns only `USER_GUIDE.md`'s structural sentence.

## Plan Deviations

- Phase 9 (added file): `code/tests/packaging/test_generate_then_execute.py` and the matching
  recipe in `code/docs/core/TESTING_GUIDE.md` 9.3. The cp1252 end-to-end leg ran the child with
  `PYTHONIOENCODING=cp1252` but decoded its stdout with `text=True` (UTF-8). `…` is cp1252 byte
  0x85, which is not valid UTF-8, so the harness raised `UnicodeDecodeError` on a correctly
  behaving child. The leg now decodes with `encoding="cp1252"`. This is a harness bug the new
  glyph exposed, not a source change; the plan's decision that `…` must survive cp1252 stands.
- Phase 9: `docs/SETTINGS.md`'s samples are regenerated from a `\Box B ⊨ \Box A` scratch example
  (three lassos, exercising the `reserved, unused` role) rather than the prior two-lasso sample,
  which no example in `examples.py` produces.
