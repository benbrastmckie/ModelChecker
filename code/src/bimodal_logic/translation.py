"""bimodal_logic.translation - Formula translation utilities.

This module provides utilities for translating between bimodal logic
formula representations: JSON formula dicts -> prefix lists -> infix strings.

Public API:
    json_to_prefix(formula_json): Convert JSON formula dict to prefix list
    temporal_depth(formula_json): Compute temporal nesting depth of a JSON formula
    prefix_to_infix(prefix_list): Convert prefix list to infix string

JSON Formula Schema:
    Primitive tags (6):
        atom: {"tag": "atom", "name": str}
        bot: {"tag": "bot"}
        imp: {"tag": "imp", "left": formula, "right": formula}
        box: {"tag": "box", "child": formula}
        untl: {"tag": "untl", "event": formula, "guard": formula}
        snce: {"tag": "snce", "event": formula, "guard": formula}

    Enriched tags (11):
        neg: {"tag": "neg", "arg": formula}
        top: {"tag": "top"}
        and: {"tag": "and", "left": formula, "right": formula}
        or: {"tag": "or", "left": formula, "right": formula}
        diamond: {"tag": "diamond", "arg": formula}
        next: {"tag": "next", "arg": formula}
        prev: {"tag": "prev", "arg": formula}
        some_future: {"tag": "some_future", "arg": formula}
        some_past: {"tag": "some_past", "arg": formula}
        all_future: {"tag": "all_future", "arg": formula}
        all_past: {"tag": "all_past", "arg": formula}

Prefix List Format:
    atoms: ["p"]
    nullary operators: ["\\bot"], ["\\top"]
    unary operators: ["\\neg", ["p"]]
    binary operators: ["\\wedge", ["p"], ["q"]]
"""

from __future__ import annotations

from typing import Any


##############################################################################
# JSON tag -> operator symbol mapping
##############################################################################

# Primitive tags
_PRIMITIVE_NULLARY = {
    "bot": "\\bot",
}

_PRIMITIVE_UNARY = {
    "box": ("\\Box", "child"),
}

_PRIMITIVE_BINARY = {
    "imp": ("\\rightarrow", "left", "right"),
    "untl": ("\\Until", "event", "guard"),
    "snce": ("\\Since", "event", "guard"),
}

# Enriched tags
_ENRICHED_NULLARY = {
    "top": "\\top",
}

_ENRICHED_UNARY = {
    "neg": ("\\neg", "arg"),
    "diamond": ("\\Diamond", "arg"),
    "next": ("\\next", "arg"),
    "prev": ("\\prev", "arg"),
    "some_future": ("\\future", "arg"),
    "some_past": ("\\past", "arg"),
    "all_future": ("\\Future", "arg"),
    "all_past": ("\\Past", "arg"),
}

_ENRICHED_BINARY = {
    "and": ("\\wedge", "left", "right"),
    "or": ("\\vee", "left", "right"),
}

# Set of all temporal tags (for temporal_depth increment logic)
_TEMPORAL_INCREMENT_TAGS = frozenset({
    "untl", "snce",           # temporal primitives
    "next", "prev",           # defined temporal (next/prev)
    "some_future", "some_past",  # defined temporal (F/P existential)
    "all_future", "all_past",    # defined temporal (G/H universal)
})

# All known tags
_ALL_KNOWN_TAGS = (
    frozenset({"atom"})
    | frozenset(_PRIMITIVE_NULLARY)
    | frozenset(_PRIMITIVE_UNARY)
    | frozenset(_PRIMITIVE_BINARY)
    | frozenset(_ENRICHED_NULLARY)
    | frozenset(_ENRICHED_UNARY)
    | frozenset(_ENRICHED_BINARY)
)


##############################################################################
# json_to_prefix
##############################################################################

def json_to_prefix(formula_json: dict) -> list:
    """Convert a JSON formula dict to a ModelChecker prefix list.

    Supports all 17 JSON tags (6 primitive + 11 enriched).

    Args:
        formula_json: A dict with a "tag" field and tag-specific fields.

    Returns:
        A prefix list in ModelChecker format:
        - atoms: ["p"]
        - nullary: ["\\bot"]
        - unary: ["\\neg", ["p"]]
        - binary: ["\\wedge", ["p"], ["q"]]

    Raises:
        ValueError: If the tag is unknown or required fields are missing.
        KeyError: If required fields are missing from formula_json.
    """
    tag = formula_json["tag"]  # KeyError if missing "tag"

    if tag not in _ALL_KNOWN_TAGS:
        raise ValueError(
            f"unknown JSON formula tag: {tag!r}. "
            f"Expected one of: {sorted(_ALL_KNOWN_TAGS)}"
        )

    # Handle atom specially
    if tag == "atom":
        name = formula_json["name"]  # KeyError if missing
        return [name]

    # Primitive nullary (bot)
    if tag in _PRIMITIVE_NULLARY:
        return [_PRIMITIVE_NULLARY[tag]]

    # Enriched nullary (top)
    if tag in _ENRICHED_NULLARY:
        return [_ENRICHED_NULLARY[tag]]

    # Primitive unary (box)
    if tag in _PRIMITIVE_UNARY:
        op_sym, field = _PRIMITIVE_UNARY[tag]
        child = formula_json[field]  # KeyError if missing
        return [op_sym, json_to_prefix(child)]

    # Enriched unary (neg, diamond, next, prev, some_future, some_past, all_future, all_past)
    if tag in _ENRICHED_UNARY:
        op_sym, field = _ENRICHED_UNARY[tag]
        arg = formula_json[field]  # KeyError if missing
        return [op_sym, json_to_prefix(arg)]

    # Primitive binary (imp, untl, snce)
    if tag in _PRIMITIVE_BINARY:
        op_sym, left_field, right_field = _PRIMITIVE_BINARY[tag]
        left = formula_json[left_field]    # KeyError if missing
        right = formula_json[right_field]  # KeyError if missing
        return [op_sym, json_to_prefix(left), json_to_prefix(right)]

    # Enriched binary (and, or)
    if tag in _ENRICHED_BINARY:
        op_sym, left_field, right_field = _ENRICHED_BINARY[tag]
        left = formula_json[left_field]    # KeyError if missing
        right = formula_json[right_field]  # KeyError if missing
        return [op_sym, json_to_prefix(left), json_to_prefix(right)]

    # Should not reach here given _ALL_KNOWN_TAGS check above
    raise ValueError(f"unhandled tag: {tag!r}")


##############################################################################
# temporal_depth
##############################################################################

def temporal_depth(formula_json: dict) -> int:
    """Compute the temporal nesting depth of a JSON formula.

    Depth rules:
    - Leaf nodes (atom, bot, top): 0
    - Extensional unary (neg): depth(arg)
    - Extensional binary (imp, and, or): max(depth(left), depth(right))
    - Modal (box, diamond): max of children depths (NO increment)
    - Temporal primitive (untl, snce): 1 + max(depth(event), depth(guard))
    - Temporal enriched (next, prev, some_future, some_past, all_future, all_past):
        1 + depth(arg)

    Boundary Claim (BimodalSemantics finite time domain):
        For a formula of temporal depth d evaluated at t=0 with M >= d+2,
        boundary effects cannot create spurious countermodels.

        Formal argument:
        - BimodalSemantics uses open interval (-M, M), giving 2*M-1 integer time
          points: {-(M-1), ..., -1, 0, 1, ..., M-1}.
        - Evaluation is fixed at t=0 (the main_time constraint).
        - The key invariant for a depth-d formula at time t is: M - 1 - t >= d,
          i.e., at least d future time points exist beyond t.
        - At t=0, this becomes M - 1 >= d, equivalently M >= d+1.
        - For STRICT boundary safety (no vacuous truth at any reachable
          sub-evaluation point along a depth-d chain), M >= d+2 is required.
          This ensures the chain t=0 -> t=1 -> ... -> t=d reaches at most t=d
          which satisfies M - 1 - d >= 1 (at least one more time point available).
        - Boundary vacuity only arises at t=M-1 (the last future time point).
          A depth-d formula evaluated from t=0 can reach at most t=d, which is
          strictly less than M-1 when M >= d+2. Therefore t=M-1 is unreachable.
        - The recommended minimum M for genuine (non-vacuous) evaluation:
            M_safe(d) = max(d + 2, 3)
          Values d=0,1 map to M=3 (the minimum non-trivial domain), d=2->4,
          d=3->5, etc.

        Note: Many examples use M < d+2 and still produce correct results because
        boundary vacuity for those specific formulas does not create spurious
        countermodels. The dynamic M adjustment (M = max(depth+2, 3)) belongs in
        OracleProvider (task 103), not in BimodalSemantics constraints.

    Args:
        formula_json: A dict with a "tag" field and tag-specific fields.

    Returns:
        Non-negative integer representing temporal nesting depth.
    """
    tag = formula_json["tag"]

    # Leaf nodes: depth 0
    if tag in ("atom", "bot", "top"):
        return 0

    # Temporal primitives: 1 + max of children
    if tag == "untl":
        event_depth = temporal_depth(formula_json["event"])
        guard_depth = temporal_depth(formula_json["guard"])
        return 1 + max(event_depth, guard_depth)

    if tag == "snce":
        event_depth = temporal_depth(formula_json["event"])
        guard_depth = temporal_depth(formula_json["guard"])
        return 1 + max(event_depth, guard_depth)

    # Temporal enriched unary: 1 + depth(arg)
    if tag in ("next", "prev", "some_future", "some_past", "all_future", "all_past"):
        return 1 + temporal_depth(formula_json["arg"])

    # Modal operators: max of children (NO increment)
    if tag == "box":
        return temporal_depth(formula_json["child"])

    if tag == "diamond":
        return temporal_depth(formula_json["arg"])

    # Extensional unary (neg): depth(arg)
    if tag == "neg":
        return temporal_depth(formula_json["arg"])

    # Extensional binary (imp, and, or): max(depth(left), depth(right))
    if tag == "imp":
        return max(
            temporal_depth(formula_json["left"]),
            temporal_depth(formula_json["right"])
        )

    if tag == "and":
        return max(
            temporal_depth(formula_json["left"]),
            temporal_depth(formula_json["right"])
        )

    if tag == "or":
        return max(
            temporal_depth(formula_json["left"]),
            temporal_depth(formula_json["right"])
        )

    raise ValueError(f"unknown JSON formula tag in temporal_depth: {tag!r}")


##############################################################################
# prefix_to_infix
##############################################################################

def prefix_to_infix(prefix_list: list) -> str:
    """Convert a ModelChecker prefix list to an infix string.

    Produces parenthesized infix strings compatible with the ModelChecker parser.

    Args:
        prefix_list: A prefix list in ModelChecker format:
            - atoms: ["p"]
            - nullary: ["\\bot"]
            - unary: ["\\neg", sublist]
            - binary: ["\\wedge", left_sublist, right_sublist]

    Returns:
        An infix string compatible with the ModelChecker formula parser.

    Examples:
        prefix_to_infix(["p"]) -> "p"
        prefix_to_infix(["\\bot"]) -> "\\bot"
        prefix_to_infix(["\\neg", ["p"]]) -> "\\neg p"
        prefix_to_infix(["\\wedge", ["p"], ["q"]]) -> "(p \\wedge q)"
    """
    if not isinstance(prefix_list, list) or len(prefix_list) == 0:
        raise ValueError(f"prefix_list must be a non-empty list, got: {prefix_list!r}")

    head = prefix_list[0]

    # Atom or nullary operator: single-element list
    if len(prefix_list) == 1:
        return str(head)

    # Unary: [op, arg]
    if len(prefix_list) == 2:
        op_str = str(head)
        arg_str = prefix_to_infix(prefix_list[1])
        return f"{op_str} {arg_str}"

    # Binary: [op, left, right]
    if len(prefix_list) == 3:
        op_str = str(head)
        left_str = prefix_to_infix(prefix_list[1])
        right_str = prefix_to_infix(prefix_list[2])
        return f"({left_str} {op_str} {right_str})"

    raise ValueError(
        f"prefix_list has unexpected arity {len(prefix_list) - 1}: {prefix_list!r}"
    )


##############################################################################
# Private helpers for fold/unfold
##############################################################################

def _make_bot() -> dict:
    """Return a fresh bot node."""
    return {"tag": "bot"}


def _make_top_expanded() -> dict:
    """Return imp(bot, bot), the primitive expansion of top."""
    return {"tag": "imp", "left": _make_bot(), "right": _make_bot()}


def _is_bot(node: dict) -> bool:
    """Return True if node is a bot node."""
    return node.get("tag") == "bot"


def _is_top_pattern(node: dict) -> bool:
    """Return True if node matches the top pattern: imp(bot, bot)."""
    return (
        node.get("tag") == "imp"
        and _is_bot(node.get("left", {}))
        and _is_bot(node.get("right", {}))
    )


def _is_neg_pattern(node: dict) -> bool:
    """Return True if node matches the neg pattern: imp(_, bot)."""
    return node.get("tag") == "imp" and _is_bot(node.get("right", {}))


##############################################################################
# unfold_formula
##############################################################################

def unfold_formula(formula_json: dict) -> dict:
    """Recursively expand all enriched tags to the 6 primitive tags.

    Primitive tags (atom, bot, imp, box, untl, snce) are passed through
    with their children recursively unfolded.  The 11 enriched tags are
    replaced by their primitive-only definitions.

    Unfold mappings:
        neg φ  -> imp(unfold(φ), bot)
        top    -> imp(bot, bot)
        and φ ψ -> imp(imp(unfold(φ), imp(unfold(ψ), bot)), bot)
        or  φ ψ -> imp(imp(unfold(φ), bot), unfold(ψ))
        diamond φ -> imp(box(imp(unfold(φ), bot)), bot)
        next φ -> untl(unfold(φ), bot)
        prev φ -> snce(unfold(φ), bot)
        some_future φ -> untl(unfold(φ), imp(bot, bot))
        some_past   φ -> snce(unfold(φ), imp(bot, bot))
        all_future  φ -> imp(untl(imp(unfold(φ), bot), imp(bot, bot)), bot)
        all_past    φ -> imp(snce(imp(unfold(φ), bot), imp(bot, bot)), bot)

    Args:
        formula_json: A dict with a "tag" field and tag-specific fields.

    Returns:
        A new formula dict using only the 6 primitive tags.

    Raises:
        ValueError: If the tag is unknown.
        KeyError: If required fields are missing from formula_json.
    """
    tag = formula_json["tag"]

    # ---- Primitive tags: recurse into children ----

    if tag == "atom":
        return dict(formula_json)

    if tag == "bot":
        return _make_bot()

    if tag == "imp":
        return {
            "tag": "imp",
            "left": unfold_formula(formula_json["left"]),
            "right": unfold_formula(formula_json["right"]),
        }

    if tag == "box":
        return {
            "tag": "box",
            "child": unfold_formula(formula_json["child"]),
        }

    if tag == "untl":
        return {
            "tag": "untl",
            "event": unfold_formula(formula_json["event"]),
            "guard": unfold_formula(formula_json["guard"]),
        }

    if tag == "snce":
        return {
            "tag": "snce",
            "event": unfold_formula(formula_json["event"]),
            "guard": unfold_formula(formula_json["guard"]),
        }

    # ---- Level 1 enriched tags ----

    if tag == "top":
        # top -> imp(bot, bot)
        return _make_top_expanded()

    if tag == "neg":
        # neg φ -> imp(φ, bot)
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "imp", "left": phi, "right": _make_bot()}

    if tag == "next":
        # next φ -> untl(φ, bot)
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "untl", "event": phi, "guard": _make_bot()}

    if tag == "prev":
        # prev φ -> snce(φ, bot)
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "snce", "event": phi, "guard": _make_bot()}

    # ---- Level 2 enriched tags ----

    if tag == "and":
        # and φ ψ -> imp(imp(φ, imp(ψ, bot)), bot)
        phi = unfold_formula(formula_json["left"])
        psi = unfold_formula(formula_json["right"])
        return {
            "tag": "imp",
            "left": {
                "tag": "imp",
                "left": phi,
                "right": {"tag": "imp", "left": psi, "right": _make_bot()},
            },
            "right": _make_bot(),
        }

    if tag == "or":
        # or φ ψ -> imp(imp(φ, bot), ψ)
        phi = unfold_formula(formula_json["left"])
        psi = unfold_formula(formula_json["right"])
        return {
            "tag": "imp",
            "left": {"tag": "imp", "left": phi, "right": _make_bot()},
            "right": psi,
        }

    if tag == "diamond":
        # diamond φ -> imp(box(imp(φ, bot)), bot)
        phi = unfold_formula(formula_json["arg"])
        return {
            "tag": "imp",
            "left": {
                "tag": "box",
                "child": {"tag": "imp", "left": phi, "right": _make_bot()},
            },
            "right": _make_bot(),
        }

    if tag == "some_future":
        # some_future φ -> untl(φ, imp(bot, bot))
        phi = unfold_formula(formula_json["arg"])
        return {
            "tag": "untl",
            "event": phi,
            "guard": _make_top_expanded(),
        }

    if tag == "some_past":
        # some_past φ -> snce(φ, imp(bot, bot))
        phi = unfold_formula(formula_json["arg"])
        return {
            "tag": "snce",
            "event": phi,
            "guard": _make_top_expanded(),
        }

    # ---- Level 3 enriched tags ----

    if tag == "all_future":
        # all_future φ -> imp(untl(imp(φ, bot), imp(bot, bot)), bot)
        phi = unfold_formula(formula_json["arg"])
        return {
            "tag": "imp",
            "left": {
                "tag": "untl",
                "event": {"tag": "imp", "left": phi, "right": _make_bot()},
                "guard": _make_top_expanded(),
            },
            "right": _make_bot(),
        }

    if tag == "all_past":
        # all_past φ -> imp(snce(imp(φ, bot), imp(bot, bot)), bot)
        phi = unfold_formula(formula_json["arg"])
        return {
            "tag": "imp",
            "left": {
                "tag": "snce",
                "event": {"tag": "imp", "left": phi, "right": _make_bot()},
                "guard": _make_top_expanded(),
            },
            "right": _make_bot(),
        }

    raise ValueError(
        f"unknown JSON formula tag in unfold_formula: {tag!r}. "
        f"Expected one of: {sorted(_ALL_KNOWN_TAGS)}"
    )


##############################################################################
# fold_formula
##############################################################################

def fold_formula(formula_json: dict) -> dict:
    """Greedily fold primitive patterns into enriched tags using outside-in matching.

    Pattern matching is applied outside-in with Level 3 before Level 2 before
    Level 1.  Within the imp(_, bot) family, specificity order prevents
    ambiguity:
        1. all_future: left is untl with top guard and neg-pattern event
        2. all_past:   left is snce with top guard and neg-pattern event
        3. diamond:    left is box with neg-pattern child
        4. and:        left is imp with neg-pattern right child
        5. top:        left is bot AND right is bot (before neg)
        6. neg:        any remaining imp(_, bot)

    Args:
        formula_json: A dict with a "tag" field and tag-specific fields.
            May contain only primitive tags or a mix.

    Returns:
        A new formula dict with enriched tags applied where patterns match.

    Raises:
        KeyError: If required fields are missing from formula_json.
    """
    tag = formula_json["tag"]

    # ---- Level 3 patterns (check before recursing children) ----

    if tag == "imp":
        left = formula_json["left"]
        right = formula_json["right"]

        if _is_bot(right):
            # imp(X, bot): check specificity order

            # 1. all_future: left is untl(neg_event, top_guard)
            if (
                left.get("tag") == "untl"
                and _is_top_pattern(left.get("guard", {}))
                and _is_neg_pattern(left.get("event", {}))
            ):
                # Fold inner event neg-pattern's left as arg
                event_node = left["event"]  # imp(phi, bot)
                phi = fold_formula(event_node["left"])
                return {"tag": "all_future", "arg": phi}

            # 2. all_past: left is snce(neg_event, top_guard)
            if (
                left.get("tag") == "snce"
                and _is_top_pattern(left.get("guard", {}))
                and _is_neg_pattern(left.get("event", {}))
            ):
                event_node = left["event"]  # imp(phi, bot)
                phi = fold_formula(event_node["left"])
                return {"tag": "all_past", "arg": phi}

            # 3. diamond: left is box(neg_pattern_child)
            if (
                left.get("tag") == "box"
                and _is_neg_pattern(left.get("child", {}))
            ):
                child_node = left["child"]  # imp(phi, bot)
                phi = fold_formula(child_node["left"])
                return {"tag": "diamond", "arg": phi}

            # 4. and: left is imp(phi, imp(psi, bot))
            if (
                left.get("tag") == "imp"
                and _is_neg_pattern(left.get("right", {}))
            ):
                phi = fold_formula(left["left"])
                psi = fold_formula(left["right"]["left"])
                return {"tag": "and", "left": phi, "right": psi}

            # 5. top: both sides are bot  (more specific than neg)
            if _is_bot(left):
                return {"tag": "top"}

            # 6. neg: fallback for remaining imp(X, bot)
            folded_left = fold_formula(left)
            return {"tag": "neg", "arg": folded_left}

        # imp(X, Y) where Y is not bot
        # Check or pattern: imp(imp(phi, bot), psi)
        if _is_neg_pattern(left):
            phi = fold_formula(left["left"])
            psi = fold_formula(right)
            return {"tag": "or", "left": phi, "right": psi}

        # Generic imp: recurse into both children
        return {
            "tag": "imp",
            "left": fold_formula(left),
            "right": fold_formula(right),
        }

    if tag == "untl":
        guard = formula_json["guard"]
        event = formula_json["event"]

        # next: guard is bot
        if _is_bot(guard):
            phi = fold_formula(event)
            return {"tag": "next", "arg": phi}

        # some_future: guard is top pattern (imp(bot, bot))
        if _is_top_pattern(guard):
            phi = fold_formula(event)
            return {"tag": "some_future", "arg": phi}

        # Generic untl
        return {
            "tag": "untl",
            "event": fold_formula(event),
            "guard": fold_formula(guard),
        }

    if tag == "snce":
        guard = formula_json["guard"]
        event = formula_json["event"]

        # prev: guard is bot
        if _is_bot(guard):
            phi = fold_formula(event)
            return {"tag": "prev", "arg": phi}

        # some_past: guard is top pattern (imp(bot, bot))
        if _is_top_pattern(guard):
            phi = fold_formula(event)
            return {"tag": "some_past", "arg": phi}

        # Generic snce
        return {
            "tag": "snce",
            "event": fold_formula(event),
            "guard": fold_formula(guard),
        }

    # ---- Passthrough tags: recurse into children ----

    if tag == "atom":
        return dict(formula_json)

    if tag == "bot":
        return _make_bot()

    if tag == "box":
        return {
            "tag": "box",
            "child": fold_formula(formula_json["child"]),
        }

    # ---- Enriched tags that might appear in already-folded or mixed input ----
    # Recurse into their children so they stay consistent

    if tag == "top":
        return {"tag": "top"}

    if tag == "neg":
        return {"tag": "neg", "arg": fold_formula(formula_json["arg"])}

    if tag == "and":
        return {
            "tag": "and",
            "left": fold_formula(formula_json["left"]),
            "right": fold_formula(formula_json["right"]),
        }

    if tag == "or":
        return {
            "tag": "or",
            "left": fold_formula(formula_json["left"]),
            "right": fold_formula(formula_json["right"]),
        }

    if tag == "diamond":
        return {"tag": "diamond", "arg": fold_formula(formula_json["arg"])}

    if tag == "next":
        return {"tag": "next", "arg": fold_formula(formula_json["arg"])}

    if tag == "prev":
        return {"tag": "prev", "arg": fold_formula(formula_json["arg"])}

    if tag == "some_future":
        return {"tag": "some_future", "arg": fold_formula(formula_json["arg"])}

    if tag == "some_past":
        return {"tag": "some_past", "arg": fold_formula(formula_json["arg"])}

    if tag == "all_future":
        return {"tag": "all_future", "arg": fold_formula(formula_json["arg"])}

    if tag == "all_past":
        return {"tag": "all_past", "arg": fold_formula(formula_json["arg"])}

    raise ValueError(
        f"unknown JSON formula tag in fold_formula: {tag!r}. "
        f"Expected one of: {sorted(_ALL_KNOWN_TAGS)}"
    )


##############################################################################
# normalize_formula
##############################################################################

def _fold_at_level(formula_json: dict, max_level: int) -> dict:
    """Fold a formula allowing only enriched operators at or below max_level.

    Level 0: no enriched operators (same as unfold)
    Level 1: neg, top, next, prev
    Level 2: Level 1 + and, or, diamond, some_future, some_past
    Level 3: Level 2 + all_future, all_past (same as full fold)

    Args:
        formula_json: A primitive-only formula dict (output of unfold_formula).
        max_level: Maximum enriched operator level to allow (0-3).

    Returns:
        A formula dict with enriched operators up to max_level applied.
    """
    _LEVEL1 = frozenset({"neg", "top", "next", "prev"})
    _LEVEL2 = frozenset({"and", "or", "diamond", "some_future", "some_past"})
    _LEVEL3 = frozenset({"all_future", "all_past"})

    tag = formula_json["tag"]

    if tag == "imp":
        left = formula_json["left"]
        right = formula_json["right"]

        if _is_bot(right):
            # Check Level 3 patterns
            if max_level >= 3:
                if (
                    left.get("tag") == "untl"
                    and _is_top_pattern(left.get("guard", {}))
                    and _is_neg_pattern(left.get("event", {}))
                ):
                    event_node = left["event"]
                    phi = _fold_at_level(event_node["left"], max_level)
                    return {"tag": "all_future", "arg": phi}

                if (
                    left.get("tag") == "snce"
                    and _is_top_pattern(left.get("guard", {}))
                    and _is_neg_pattern(left.get("event", {}))
                ):
                    event_node = left["event"]
                    phi = _fold_at_level(event_node["left"], max_level)
                    return {"tag": "all_past", "arg": phi}

            # Check Level 2 patterns
            if max_level >= 2:
                if (
                    left.get("tag") == "box"
                    and _is_neg_pattern(left.get("child", {}))
                ):
                    child_node = left["child"]
                    phi = _fold_at_level(child_node["left"], max_level)
                    return {"tag": "diamond", "arg": phi}

                if (
                    left.get("tag") == "imp"
                    and _is_neg_pattern(left.get("right", {}))
                ):
                    phi = _fold_at_level(left["left"], max_level)
                    psi = _fold_at_level(left["right"]["left"], max_level)
                    return {"tag": "and", "left": phi, "right": psi}

            # Check Level 1 patterns
            if max_level >= 1:
                if _is_bot(left):
                    return {"tag": "top"}
                # neg: fallback
                folded_left = _fold_at_level(left, max_level)
                return {"tag": "neg", "arg": folded_left}

            # Level 0: no enriched, recurse into both sides
            return {
                "tag": "imp",
                "left": _fold_at_level(left, max_level),
                "right": _fold_at_level(right, max_level),
            }

        # imp(X, Y) where Y is not bot
        if max_level >= 2 and _is_neg_pattern(left):
            phi = _fold_at_level(left["left"], max_level)
            psi = _fold_at_level(right, max_level)
            return {"tag": "or", "left": phi, "right": psi}

        return {
            "tag": "imp",
            "left": _fold_at_level(left, max_level),
            "right": _fold_at_level(right, max_level),
        }

    if tag == "untl":
        guard = formula_json["guard"]
        event = formula_json["event"]

        if max_level >= 1 and _is_bot(guard):
            phi = _fold_at_level(event, max_level)
            return {"tag": "next", "arg": phi}

        if max_level >= 2 and _is_top_pattern(guard):
            phi = _fold_at_level(event, max_level)
            return {"tag": "some_future", "arg": phi}

        return {
            "tag": "untl",
            "event": _fold_at_level(event, max_level),
            "guard": _fold_at_level(guard, max_level),
        }

    if tag == "snce":
        guard = formula_json["guard"]
        event = formula_json["event"]

        if max_level >= 1 and _is_bot(guard):
            phi = _fold_at_level(event, max_level)
            return {"tag": "prev", "arg": phi}

        if max_level >= 2 and _is_top_pattern(guard):
            phi = _fold_at_level(event, max_level)
            return {"tag": "some_past", "arg": phi}

        return {
            "tag": "snce",
            "event": _fold_at_level(event, max_level),
            "guard": _fold_at_level(guard, max_level),
        }

    if tag == "atom":
        return dict(formula_json)

    if tag == "bot":
        return _make_bot()

    if tag == "box":
        return {"tag": "box", "child": _fold_at_level(formula_json["child"], max_level)}

    raise ValueError(
        f"unexpected tag in _fold_at_level: {tag!r} (input should be primitive-only)"
    )


def normalize_formula(formula_json: dict, level: int) -> dict:
    """Fold/unfold a formula to use enriched operators up to the given level.

    First unfolds all enriched tags to primitives, then folds back allowing
    only operators at or below the specified level.

    Levels:
        0: No enriched operators (equivalent to unfold_formula)
        1: Allow neg, top, next, prev
        2: Allow Level 1 + and, or, diamond, some_future, some_past
        3: Allow all 11 enriched operators (equivalent to fold_formula(unfold_formula(f)))

    Args:
        formula_json: A formula dict with any combination of tags.
        level: Target level (integer 0-3).

    Returns:
        A normalized formula dict using enriched operators up to level.

    Raises:
        ValueError: If level is not in the range [0, 3].
    """
    if not isinstance(level, int) or level < 0 or level > 3:
        raise ValueError(
            f"level must be an integer in [0, 3], got: {level!r}"
        )
    unfolded = unfold_formula(formula_json)
    return _fold_at_level(unfolded, level)
