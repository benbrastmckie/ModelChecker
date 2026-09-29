# Implementation Summary: Bimodal Countermodel Presentation

- **Task**: 218 - Refactor bimodal/ theory countermodel presentation
- **Plan**: plans/01_bimodal-countermodel-presentation.md (7 phases, all COMPLETED)
- **Session**: sess_1790641161_19a0a0

## What Changed

`dev_cli.py` output for a bimodal example now reads, per countermodel: a `Search bounds:
back=B, mid=M, fwd=F (N lassos: 1 main + K reserved witnesses)` header in place of `Atomic
States: 0`; a `Certificate:` block with a legend, one aligned row per lasso (`L{i}`, a role
column `main` / `witness for \Box A` / `reserved, unused`, and `(back)^ω | mid | (fwd)^ω` over
atoms with `[ ]` marking the evaluation point and `∅` for empty labels); a `Box guesses:` table
whose `falsified at L{i}, t=±t` witness is read from the certificate itself; `Evaluation point:
L0 at t=-2`; and exactly one `Verification:` line (checkout shortened to 12 hex). Interpreted
sentences read `(True at L0, t=-2)`. A theorem prints the D8 "No certificate found ... not a
validity claim" message once. `-a/--align_vertically` is live for bimodal and switches the
certificate block to a time-aligned table. Iteration diffs print `L0, position -1: + □A` /
`□A: False -> True` in user notation, on the live `iterate: N` path too.

Systemic change (one): `model_checker.output.color.use_colors(output)` (`NO_COLOR` >
`FORCE_COLOR` > `TERM=dumb` > `isatty()`) replaces every `output is sys.__stdout__` /
`sys.stdout` color test in the framework and in the logos/exclusion/imposition/bimodal printers
and the `--maximize` runner output, so pipes and redirected files receive plain text.

## Bug Fixed (F1)

The old `Witness: L{i} at position {p}` line read `WitnessRegistry._witness_lassos`, a reserved
index, not provenance. On `MD_CM_1` it reported `L1 at position None` for `\Box A` while the
only (C3) falsifier was `(L3, t=+2)`. `BimodalStructure.box_witness` now scans
`certificate.lassos` x `_box_window` and returns a pair the (C3) predicate accepts.

## Files

- New: `bimodal/semantic/render.py` (`render`, `build_names`, `print_differences`,
  `signed_time`), `output/color.py`, tests `bimodal/tests/unit/test_render.py`,
  `output/tests/unit/test_color.py`, `builder/tests/unit/test_module_output_capture.py`.
- Modified: `bimodal/semantic/{model,proposition,core}.py`, `bimodal/iterate.py`,
  `bimodal/examples.py`, `utils/glyphs.py` (8 glyph entries), `models/structure.py`,
  `output/__init__.py`, `builder/runner.py`, logos/exclusion/imposition `semantic/model.py`,
  `imposition/iterate.py`, bimodal `README.md`, `docs/{SETTINGS,ITERATE,ARCHITECTURE,
  USER_GUIDE,API_REFERENCE}.md`, `code/docs/core/CODE_STANDARDS.md`, and the bimodal/utils/
  models/output test files named per phase.

## Verification

- Full suite: `3416 passed, 5 skipped` (`pytest code/tests/ code/src/model_checker`).
- Live `dev_cli.py` bimodal run through a pipe: 0 ANSI escapes, 0 dataclass reprs, one
  `Verification:` per countermodel (13/13), one `No certificate found` per theorem (12/12);
  `-a` run: 0 `align_vertically` warnings (was 25), table per countermodel; logos/imposition/
  exclusion pipe runs 0 escapes; `FORCE_COLOR=1` into a pipe colors, `NO_COLOR=1` wins.
- `PYTHONIOENCODING=cp1252` subprocess legs (default, `-a`, iterate, full examples): no
  `UnicodeEncodeError`; every new glyph has a real-encoded-stream test.
- D8/F2 substrings preserved verbatim (pinned by `test_output_gate.py`).

## Plan Deviations

- Phase 1: `render` is not re-exported from `semantic/__init__.py` (that package re-exports
  only the three theory classes); `IMP` reuses the existing `ARROW` glyph; `¬` is a cp1252
  code point, so its `~` fallback is pinned on an `ascii` stream.
- Phase 3 (extended): the eight `output is sys.__stdout__` sites were not the only escape
  sources -- `logos/semantic/model.py::print_model_differences` (`is sys.stdout`),
  `imposition/iterate.py::display_model_differences` (26 unconditional literals),
  `imposition/semantic/model.py::print_model_differences` (42 unconditional `self.COLORS`
  uses), and `builder/runner.py`'s maximize output were gated too.
- Phase 4 (altered): the box-guess table and role column render in the user's notation
  (`\Box A`), since every boxed closure member is a named sentence or derived subsentence; the
  `□` fallback surfaces only in iteration diffs. Multi-atom labels keep braces (`{A,B}`) so the
  slot separator stays unambiguous. `print_all` prints the D8 block on the no-certificate path.
- Phase 6 (extended): on the live `BuildModule` path the runner calls
  `structure.print_model_differences()`, which bimodal did not override -- added
  `BimodalStructure.print_model_differences`, sharing `render.print_differences` with the
  iterator; `iterate_example`'s per-structure wrapper removed.
- Phase 7: `check-task-references.sh` does not accept a `code/` scope; the equivalent grep was
  run over every touched deliverable (zero hits). `USER_GUIDE.md` needed one `^w` -> `^ω` edit.
