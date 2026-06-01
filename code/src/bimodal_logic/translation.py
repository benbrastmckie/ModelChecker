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
