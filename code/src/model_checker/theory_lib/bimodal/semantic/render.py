"""User-notation rendering of closure `Formula`s for printed output.

The certificate search runs over `semantic/formula.py`'s six-constructor closure, so every
formula the printer has in hand is an `Imp`/`Bot`/`Box`/`Untl`/`Snce`/`Atom` tree -- the
user's `\\neg`, `\\wedge`, `\\vee`, `\\top`, `\\Diamond`, `\\future`, `\\past` have all been
compiled away by `translate`. Printing the dataclass `repr` of such a tree
(`Imp(left=Imp(left=Atom(base='A', ...` for `A \\vee B`) is unreadable, and the reprs cannot
be changed: `witness_registry.py` builds Z3 variable names from `{formula!r}`.

`render` therefore takes two routes, in order:

1. **Reverse lookup** (`build_names`): every sentence and subsentence the user wrote is in
   `Syntax.all_sentences`, keyed by its infix text, and `translate` maps each one to a closure
   formula. Inverting that map lets the printer show `\\Box (A \\vee B)` for the formula the
   user typed as `\\Box (A \\vee B)`. Two sentences can translate to the same formula (`A \\vee B`
   and `(\\neg A \\rightarrow B)` do); the first seen in `all_sentences` insertion order wins --
   premises before conclusions, outer sentence before its subsentences -- which is deterministic.

2. **Structural fallback**: a formula the user never spelled out (a closure member such as the
   inner `Imp(A, Bot)` of a `\\Diamond A`, or an iteration diff's changed label bit) is printed
   by matching the derived-operator patterns `Formula.lean`'s "Naming Convention" section fixes
   and `translate` produces: `Imp(x, Bot)` is `¬x`, `Imp(Imp(a, Bot), b)` is `(a ∨ b)`,
   `Imp(Imp(a, Imp(b, Bot)), Bot)` is `(a ∧ b)`, `Imp(Bot, Bot)` is `⊤`,
   `Imp(Box(Imp(x, Bot)), Bot)` is `◇x`, `Imp(Untl(⊤, Imp(a, Bot)), Bot)` is `\\Future a` (and
   the `Snce` mirror `\\Past a`), any other `Imp` is `(a → b)`, `Box` is `□`, `Untl`/`Snce` are
   `(g U e)`/`(g S e)`.

Every non-ASCII symbol goes through `utils/glyphs.py`'s `glyph(name, output)`, so a cp1252
pipe gets `~`, `&`, `|`, `->`, `[]`, `<>`, `_|_`, `T` instead of a `UnicodeEncodeError` --
see `code/docs/core/TESTING_GUIDE.md` section 9.
"""

from __future__ import annotations

from typing import Any, Dict, Optional

from model_checker.output.color import use_colors
from model_checker.utils.glyphs import glyph

from .formula import Atom, Bot, Box, Formula, Imp, Snce, Untl, translate

__all__ = ["build_names", "print_differences", "render", "signed_time"]

Names = Dict[Formula, str]


def build_names(syntax: Any) -> Names:
    """`{translate(sentence): sentence.name}` over `syntax.all_sentences`, first-seen wins.

    A sentence `translate` has no rule for (which cannot happen for a type-updated bimodal
    `Syntax`, but is cheap to guard) is skipped rather than aborting the whole map.
    """
    names: Names = {}
    all_sentences = getattr(syntax, "all_sentences", None) or {}
    for sentence in all_sentences.values():
        try:
            formula = translate(sentence)
        except (ValueError, AttributeError):
            continue
        names.setdefault(formula, str(sentence.name))
    return names


def signed_time(t: int) -> str:
    """`-2`, `0`, `+2`: integer positions print with an explicit sign except at the origin,
    so a reader sees at a glance which side of the `mid` segment a position lies on."""
    return f"{t:+d}" if t else "0"


def _is_top(formula: Formula) -> bool:
    return isinstance(formula, Imp) and isinstance(formula.left, Bot) and isinstance(
        formula.right, Bot
    )


def _is_neg(formula: Formula) -> bool:
    return isinstance(formula, Imp) and isinstance(formula.right, Bot)


def render(formula: Formula, output: Any = None, names: Optional[Names] = None) -> str:
    """Render `formula` in the user's own notation where `names` has it, else structurally.

    Args:
        formula: A closure `Formula` (`semantic/formula.py`).
        output: The destination stream (or `None`); only its `.encoding` is consulted, via
            `utils/glyphs.py`, to pick Unicode or ASCII operator symbols.
        names: An optional reverse-`translate` map from `build_names`. Consulted at every
            depth, so a named subformula renders by name inside an unnamed parent.
    """
    names = names or {}

    def go(f: Formula) -> str:
        named = names.get(f)
        if named is not None:
            return named
        if isinstance(f, Atom):
            return f.base if f.fresh_index is None else f"{f.base}#{f.fresh_index}"
        if isinstance(f, Bot):
            return glyph("BOT", output)
        if isinstance(f, Box):
            return f"{glyph('BOX', output)}{go(f.child)}"
        if isinstance(f, Untl):
            return f"({go(f.guard)} U {go(f.event)})"
        if isinstance(f, Snce):
            return f"({go(f.guard)} S {go(f.event)})"
        if isinstance(f, Imp):
            return _render_imp(f, go)
        raise TypeError(f"not a Formula: {f!r}")

    def _render_imp(f: Imp, go) -> str:
        if _is_top(f):
            return glyph("TOP", output)
        left, right = f.left, f.right
        if isinstance(right, Bot):
            # Negation-shaped: pick the derived operator `translate` encoded this way.
            if isinstance(left, Box) and _is_neg(left.child):
                return f"{glyph('LOZENGE', output)}{go(left.child.left)}"
            if isinstance(left, Untl) and _is_top(left.guard) and _is_neg(left.event):
                return f"\\Future {go(left.event.left)}"
            if isinstance(left, Snce) and _is_top(left.guard) and _is_neg(left.event):
                return f"\\Past {go(left.event.left)}"
            if isinstance(left, Imp) and _is_neg(left.right) and not isinstance(left.left, Bot):
                return f"({go(left.left)} {glyph('AND', output)} {go(left.right.left)})"
            return f"{glyph('NEG', output)}{go(left)}"
        if _is_neg(left):
            return f"({go(left.left)} {glyph('OR', output)} {go(right)})"
        return f"({go(left)} {glyph('ARROW', output)} {go(right)})"

    return go(formula)


def print_differences(differences: Dict[str, Any], output: Any, names: Optional[Names] = None) -> None:
    """Print a bimodal `model_differences` dict (`iterate.py`'s `_calculate_differences`
    shape) in the form `docs/ITERATE.md` documents: `L0, position -1: + □A` per changed label
    bit, `□A: False -> True` per changed box guess, `+ L1 added`/`- L1 removed` per lasso
    present on one side only, and `Target Time: 0 -> 1`.

    Shared by `BimodalModelIterator.display_model_differences` and
    `BimodalStructure.print_model_differences` (the method `builder/runner.py` actually calls
    on the live `iterate: N` path), so both print identical text. `+` lines are green and `-`
    lines red only when `use_colors(output)` holds; the sign is always printed, so color never
    carries information alone. Generic keys the shared iterator merges in (`structural_metrics`
    and the like) are ignored here.

    Palette consistency reviewed against `model.py`'s declared constants (`_GREEN` = 32,
    `_RED` = 31, `_RESET` = 0): this module's own green/red/reset literals already match
    those SGR codes exactly, so no change was needed to stay consistent with the wider
    color coverage `print_evaluation`'s block now has.
    """
    if not differences:
        return
    colored = use_colors(output)
    green = "\033[32m" if colored else ""
    red = "\033[31m" if colored else ""
    reset = "\033[0m" if colored else ""

    def show(formula: Formula) -> str:
        return render(formula, output, names)

    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)

    if differences.get("labels"):
        print("Label Changes:", file=output)
        for lasso_index, changes in sorted(differences["labels"].items()):
            if isinstance(changes, dict) and ("added" in changes or "removed" in changes):
                if changes.get("added"):
                    print(f"  {green}+ L{lasso_index} added{reset}", file=output)
                if changes.get("removed"):
                    print(f"  {red}- L{lasso_index} removed{reset}", file=output)
                continue
            for position, change in sorted(changes.items()):
                for formula in sorted(change["added"], key=repr):
                    print(
                        f"  L{lasso_index}, position {position}: {green}+ {show(formula)}{reset}",
                        file=output,
                    )
                for formula in sorted(change["removed"], key=repr):
                    print(
                        f"  L{lasso_index}, position {position}: {red}- {show(formula)}{reset}",
                        file=output,
                    )

    if differences.get("box_guesses"):
        print("\nBox Guess Changes:", file=output)
        for child, change in differences["box_guesses"].items():
            print(f"  {show(Box(child))}: {change['old']} -> {change['new']}", file=output)

    if differences.get("target_time"):
        change = differences["target_time"]
        print(f"\nTarget Time: {change['old']} -> {change['new']}", file=output)
