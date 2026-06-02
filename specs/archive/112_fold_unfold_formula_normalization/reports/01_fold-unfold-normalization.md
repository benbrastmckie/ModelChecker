# Research Report: Fold/Unfold Formula Normalization Utilities

**Task**: 112 — Fold/unfold formula normalization utilities
**Status**: Researched
**Session**: sess_1748797200_a3b7c9
**Date**: 2026-06-01

---

## 1. Summary of Findings

Task 112 requires adding three functions to `code/src/bimodal_logic/translation.py`:

1. `unfold_formula(formula_json) -> formula_json` — recursively expand all 11 enriched tags to the 6 primitive tags
2. `fold_formula(formula_json) -> formula_json` — greedily replace primitive patterns with enriched tags, from most complex to least
3. `normalize_formula(formula_json, level: int) -> formula_json` — fold/unfold to a specific operator level

Task 102 is fully complete. The existing `translation.py` has solid infrastructure to build on: JSON schema is defined, tag mappings are established, and all 17 tags are understood. The new functions are pure JSON-to-JSON transformations that operate entirely in the formula dict domain, with no need to touch the prefix list or infix string layers.

---

## 2. Current State of translation.py (from Task 102)

### 2.1 File Location and Module

`/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/translation.py`

Public API (from `__init__.py`):
```python
from .translation import json_to_prefix, temporal_depth, prefix_to_infix
```

The module is a complete, well-tested implementation of JSON-to-prefix conversion. All 106 tests pass.

### 2.2 Existing Data Structures

The module defines these tag classification dictionaries:

```python
_PRIMITIVE_NULLARY = {"bot": "\\bot"}
_PRIMITIVE_UNARY   = {"box": ("\\Box", "child")}
_PRIMITIVE_BINARY  = {"imp": ..., "untl": ..., "snce": ...}
_ENRICHED_NULLARY  = {"top": "\\top"}
_ENRICHED_UNARY    = {"neg", "diamond", "next", "prev", "some_future", "some_past", "all_future", "all_past"}
_ENRICHED_BINARY   = {"and", "or"}
```

These classification sets can be reused directly by `unfold_formula` and `fold_formula`.

### 2.3 What Needs to Be Added

The module currently has no `unfold_formula`, `fold_formula`, or `normalize_formula` functions. These three functions are the complete deliverable for task 112.

---

## 3. Operator Hierarchy and Unfold Mappings

### 3.1 The 6 Primitive Tags (Level 0)

These are the irreducible building blocks. `unfold_formula` must reduce everything to these:

| Tag | Fields | Notes |
|-----|--------|-------|
| `atom` | `name` | Propositional variable |
| `bot` | (none) | Falsum / bottom |
| `imp` | `left`, `right` | Material implication |
| `box` | `child` | Modal necessity |
| `untl` | `event`, `guard` | Temporal Until |
| `snce` | `event`, `guard` | Temporal Since |

### 3.2 BimodalLogic Operator Definitions (from Formula.lean)

These are the exact definitions as given in the task specification, expressed as JSON:

**Level 1: neg, top, next, prev** — defined using only primitives

| Enriched Tag | BimodalLogic Definition | JSON Expansion |
|---|---|---|
| `neg φ` | `φ.imp bot` | `{"tag": "imp", "left": φ, "right": {"tag": "bot"}}` |
| `top` | `bot.imp bot` | `{"tag": "imp", "left": {"tag": "bot"}, "right": {"tag": "bot"}}` |
| `next φ` | `untl φ bot` | `{"tag": "untl", "event": φ, "guard": {"tag": "bot"}}` |
| `prev φ` | `snce φ bot` | `{"tag": "snce", "event": φ, "guard": {"tag": "bot"}}` |

**Level 2: and, or, diamond, some_future, some_past** — defined using Level 1 + primitives

| Enriched Tag | BimodalLogic Definition | JSON Expansion |
|---|---|---|
| `and φ ψ` | `(φ.imp ψ.neg).neg` | `imp(imp(φ, imp(ψ, bot)), bot)` |
| `or φ ψ` | `φ.neg.imp ψ` | `imp(imp(φ, bot), ψ)` |
| `diamond φ` | `φ.neg.box.neg` | `imp(box(imp(φ, bot)), bot)` |
| `some_future φ` | `untl φ top` | `untl(φ, imp(bot, bot))` |
| `some_past φ` | `snce φ top` | `snce(φ, imp(bot, bot))` |

**Level 3: all_future, all_past** — defined using Level 2 + Level 1

| Enriched Tag | BimodalLogic Definition | JSON Expansion |
|---|---|---|
| `all_future φ` | `(some_future φ.neg).neg` | `imp(untl(imp(φ, bot), imp(bot, bot)), bot)` |
| `all_past φ` | `(some_past φ.neg).neg` | `imp(snce(imp(φ, bot), imp(bot, bot)), bot)` |

### 3.3 Level Assignments for normalize_formula

```
Level 0: atom, bot, imp, box, untl, snce   (primitives)
Level 1: neg, top, next, prev               (defined using only primitives)
Level 2: and, or, diamond, some_future, some_past  (defined using Level 1)
Level 3: all_future, all_past              (defined using Level 2)
```

The `normalize_formula(formula_json, level)` contract:
- `level=0` → equivalent to `unfold_formula(formula_json)` — primitives only
- `level=1` → allow neg, top, next, prev; fold others back up to Level 1 where possible
- `level=2` → allow all of Level 1 plus and, or, diamond, some_future, some_past
- `level=3` → equivalent to `fold_formula(formula_json)` — maximize enriched usage

---

## 4. Unfold Algorithm

`unfold_formula(formula_json)` is a straightforward recursive descent:

```
unfold(node):
  if node.tag in primitives:
    recurse into all children, return updated node
  elif node.tag == "neg":   return unfold(imp(unfold(φ), bot))
  elif node.tag == "top":   return imp(bot, bot)
  elif node.tag == "next":  return unfold(untl(unfold(φ), bot))
  elif node.tag == "prev":  return unfold(snce(unfold(φ), bot))
  elif node.tag == "and":   return unfold(imp(imp(unfold(φ), imp(unfold(ψ), bot)), bot))
  elif node.tag == "or":    return unfold(imp(imp(unfold(φ), bot), unfold(ψ)))
  elif node.tag == "diamond": return unfold(imp(box(imp(unfold(φ), bot)), bot))
  elif node.tag == "some_future": return unfold(untl(unfold(φ), top_expanded))
  elif node.tag == "some_past":   return unfold(snce(unfold(φ), top_expanded))
  elif node.tag == "all_future":  return unfold(imp(untl(imp(unfold(φ), bot), top_expanded), bot))
  elif node.tag == "all_past":    return unfold(imp(snce(imp(unfold(φ), bot), top_expanded), bot))
```

Where `top_expanded = {"tag": "imp", "left": {"tag": "bot"}, "right": {"tag": "bot"}}`.

The key simplification is that after building the expanded form, we must recurse into it to ensure all children are also fully unfolded. The cleanest implementation recursively unfolds each sub-formula before assembling the expanded node, then the caller does not need to re-recurse.

**Implementation strategy**: unfold each child first, then assemble the primitive representation from the already-unfolded children.

```python
def unfold_formula(formula_json: dict) -> dict:
    tag = formula_json["tag"]
    if tag == "atom":
        return formula_json   # leaf, no change
    if tag == "bot":
        return formula_json   # leaf, no change
    if tag == "imp":
        return {"tag": "imp",
                "left": unfold_formula(formula_json["left"]),
                "right": unfold_formula(formula_json["right"])}
    if tag == "box":
        return {"tag": "box", "child": unfold_formula(formula_json["child"])}
    if tag == "untl":
        return {"tag": "untl",
                "event": unfold_formula(formula_json["event"]),
                "guard": unfold_formula(formula_json["guard"])}
    if tag == "snce":
        return {"tag": "snce",
                "event": unfold_formula(formula_json["event"]),
                "guard": unfold_formula(formula_json["guard"])}
    # Enriched tags: build primitive equivalent, then recurse
    _bot = {"tag": "bot"}
    _top = {"tag": "imp", "left": _bot, "right": _bot}
    if tag == "neg":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "imp", "left": phi, "right": _bot}
    if tag == "top":
        return {"tag": "imp", "left": _bot, "right": _bot}
    if tag == "next":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "untl", "event": phi, "guard": _bot}
    if tag == "prev":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "snce", "event": phi, "guard": _bot}
    if tag == "and":
        phi = unfold_formula(formula_json["left"])
        psi = unfold_formula(formula_json["right"])
        return {"tag": "imp",
                "left": {"tag": "imp", "left": phi, "right": {"tag": "imp", "left": psi, "right": _bot}},
                "right": _bot}
    if tag == "or":
        phi = unfold_formula(formula_json["left"])
        psi = unfold_formula(formula_json["right"])
        return {"tag": "imp",
                "left": {"tag": "imp", "left": phi, "right": _bot},
                "right": psi}
    if tag == "diamond":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "imp",
                "left": {"tag": "box", "child": {"tag": "imp", "left": phi, "right": _bot}},
                "right": _bot}
    if tag == "some_future":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "untl", "event": phi, "guard": _top}
    if tag == "some_past":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "snce", "event": phi, "guard": _top}
    if tag == "all_future":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "imp",
                "left": {"tag": "untl",
                         "event": {"tag": "imp", "left": phi, "right": _bot},
                         "guard": _top},
                "right": _bot}
    if tag == "all_past":
        phi = unfold_formula(formula_json["arg"])
        return {"tag": "imp",
                "left": {"tag": "snce",
                         "event": {"tag": "imp", "left": phi, "right": _bot},
                         "guard": _top},
                "right": _bot}
    raise ValueError(f"unknown tag: {tag!r}")
```

---

## 5. Fold Algorithm and Overlapping Patterns

### 5.1 The Overlapping Pattern Problem

This is the core challenge. Consider:

- `neg φ = imp(φ, bot)` — matches any `imp(_, bot)`
- `and φ ψ = imp(imp(φ, imp(ψ, bot)), bot)` — the outer structure is `imp(_, bot)`, which neg would also match
- `all_future φ = imp(untl(imp(φ, bot), top), bot)` — also `imp(_, bot)` at the outermost level

If we fold `neg` eagerly, we'd fold `all_future φ` into `neg(untl(neg φ, top))` instead of the more compressed `all_future φ`.

**Solution**: Fold from Level 3 down to Level 1. Always attempt to match the most complex (highest-level) pattern before simpler ones. This ensures `all_future` / `all_past` patterns are recognized before `neg` consumes the outer `imp(_, bot)`.

### 5.2 Pattern Matching Rules (Level 3 → 1)

**Level 3 patterns** (check first):
```
all_future φ: imp(untl(imp(φ, bot), imp(bot, bot)), bot)
  Requires: outer imp(_, bot), inner untl(imp(φ, bot), top_pattern)

all_past φ: imp(snce(imp(φ, bot), imp(bot, bot)), bot)
  Requires: outer imp(_, bot), inner snce(imp(φ, bot), top_pattern)
```

**Level 2 patterns** (check second):
```
some_future φ: untl(φ, imp(bot, bot))
  Requires: untl with guard = top_pattern

some_past φ: snce(φ, imp(bot, bot))
  Requires: snce with guard = top_pattern

and φ ψ: imp(imp(φ, imp(ψ, bot)), bot)
  Requires: outer imp(_, bot), inner imp(φ, neg_pattern(ψ))

or φ ψ: imp(imp(φ, bot), ψ)
  Requires: outer imp(_, bot) where left itself is imp(φ, bot) = neg φ

diamond φ: imp(box(imp(φ, bot)), bot)
  Requires: outer imp(_, bot), inner box(imp(φ, bot))
```

**Level 1 patterns** (check last):
```
neg φ: imp(φ, bot)
  Requires: imp with right = bot

top: imp(bot, bot)
  Requires: imp(bot, bot) — both sides are bot

next φ: untl(φ, bot)
  Requires: untl with guard = bot

prev φ: snce(φ, bot)
  Requires: snce with guard = bot
```

### 5.3 Helper: is_top_pattern(node)

The `top` pattern `imp(bot, bot)` appears in several Level 2 and Level 3 patterns as the guard. We need a helper to recognize it:

```python
def _is_top_pattern(node: dict) -> bool:
    """Match the primitive expansion of top: imp(bot, bot)."""
    return (node.get("tag") == "imp" and
            node.get("left", {}).get("tag") == "bot" and
            node.get("right", {}).get("tag") == "bot")
```

### 5.4 Helper: is_neg_pattern(node, inner)

For recognizing `neg φ` = `imp(φ, bot)` where the right child is bot:

```python
def _is_neg_pattern(node: dict) -> tuple[bool, dict | None]:
    """Returns (True, inner_formula) if node matches imp(φ, bot)."""
    if node.get("tag") == "imp" and node.get("right", {}).get("tag") == "bot":
        return True, node["left"]
    return False, None
```

### 5.5 Fold Algorithm (Outside-In)

`fold_formula` must work **outside-in**: match patterns at the root before recursing into children. This is critical because folding from inside-out could reconstruct intermediate forms that don't match higher-level patterns.

```
fold(node):
  # Try patterns from Level 3 down to Level 1 at current root
  if matches all_future:  return {"tag": "all_future", "arg": fold(extracted_φ)}
  if matches all_past:    return {"tag": "all_past",   "arg": fold(extracted_φ)}
  if matches some_future: return {"tag": "some_future","arg": fold(extracted_φ)}
  if matches some_past:   return {"tag": "some_past",  "arg": fold(extracted_φ)}
  if matches and:         return {"tag": "and", "left": fold(φ), "right": fold(ψ)}
  if matches or:          return {"tag": "or",  "left": fold(φ), "right": fold(ψ)}
  if matches diamond:     return {"tag": "diamond", "arg": fold(extracted_φ)}
  if matches top:         return {"tag": "top"}
  if matches neg:         return {"tag": "neg", "arg": fold(extracted_φ)}
  if matches next:        return {"tag": "next", "arg": fold(extracted_φ)}
  if matches prev:        return {"tag": "prev", "arg": fold(extracted_φ)}
  # No enriched pattern matched: recurse into children
  if tag == "imp":  return {"tag": "imp", "left": fold(left), "right": fold(right)}
  if tag == "box":  return {"tag": "box", "child": fold(child)}
  if tag == "untl": return {"tag": "untl", "event": fold(event), "guard": fold(guard)}
  if tag == "snce": return {"tag": "snce", "event": fold(event), "guard": fold(guard)}
  # Atoms and bot: return unchanged
  return node
```

### 5.6 Ordering Within Level 2

Within Level 2, we must check `some_future`/`some_past` before `and`/`or`/`diamond` because:

- `some_future φ = untl(φ, top)` — tag is `untl`, no ambiguity with `and`/`or`/`diamond`
- `some_past φ = snce(φ, top)` — tag is `snce`, no ambiguity
- `and φ ψ = imp(imp(φ, neg(ψ)), bot)` — could be confused with `all_future` / `all_past` if the inner untl is present
- `or φ ψ = imp(neg(φ), ψ)` — the inner `neg(φ)` = `imp(φ, bot)` could confuse `and` matching

Critical ordering within `imp(_, bot)` family (all use outer `imp(X, bot)`):

1. Check `all_future`: left = `untl(imp(φ, bot), top)` — specific enough, check first
2. Check `all_past`: left = `snce(imp(φ, bot), top)` — specific enough
3. Check `diamond`: left = `box(imp(φ, bot))` — box at top of left child
4. Check `and`: left = `imp(φ, imp(ψ, bot))` — left child is imp whose right is neg(ψ)
5. Check `or`: left = `imp(φ, bot)` (= neg φ) — less specific, check after and
6. Check `neg`: left = anything — least specific, check last

The critical ambiguity between `and` and `or` at Level 2 within the `imp(_, bot)` pattern:
- `and φ ψ = imp(imp(φ, neg(ψ)), bot)` — left = `imp(φ, imp(ψ, bot))` — left of left is φ, right of left is `imp(ψ, bot)` (= neg ψ)
- `or φ ψ = imp(neg(φ), ψ)` — left = `imp(φ, bot)` — left of left is φ, right of left is `bot`

These are distinguishable: `and` has `right-of-left = imp(ψ, bot)` (any formula), while `or` matches only when the outer right is NOT bot (i.e., `or` is `imp(neg(φ), ψ)` where ψ is not necessarily bot). The distinction:
- `and` pattern: `imp( imp(φ, imp(ψ, bot)) , bot )` — right of outer imp is bot
- `or` pattern: `imp( imp(φ, bot) , ψ )` — right of outer imp is ψ (anything)

Since `or` subsumes `neg(φ).imp(ψ)` where ψ can be anything, `and` must be checked before `or` to avoid `imp(imp(φ, neg(ψ)), bot)` being misidentified as `or(imp(φ, neg(ψ)), bot)` ... wait, actually `or` has the outer right NOT being bot. And `and` outer right IS bot. So:
- Outer `imp(_, bot)`: could be `neg`, `and`, `all_future`, `all_past`, `diamond`
- Outer `imp(_, non-bot)`: could be `or` (the ψ is the second argument)

This means `and`/`neg`/`all_future`/`all_past`/`diamond` all have outer `right = bot`, while `or` does NOT have outer right = bot (ψ is the second argument to or). They are structurally distinct at the outer level.

### 5.7 Level-Specific Fold (for normalize_formula)

`fold_at_level(node, max_level)` applies only patterns at or below `max_level`:
- `max_level=0`: no folding (return node with children recursively processed at level 0)
- `max_level=1`: fold neg, top, next, prev only
- `max_level=2`: fold all of Level 1 plus and, or, diamond, some_future, some_past
- `max_level=3`: fold all — same as `fold_formula`

---

## 6. Formula JSON Structure — Complete Tag Reference

From the test file `test_json_translation.py` (the authoritative reference):

```
Primitive tags (6):
  atom:  {"tag": "atom", "name": str}           leaf
  bot:   {"tag": "bot"}                          leaf
  imp:   {"tag": "imp",  "left": F, "right": F}  binary
  box:   {"tag": "box",  "child": F}             unary
  untl:  {"tag": "untl", "event": F, "guard": F} binary-temporal
  snce:  {"tag": "snce", "event": F, "guard": F} binary-temporal

Enriched tags (11):
  neg:         {"tag": "neg",         "arg": F}            unary
  top:         {"tag": "top"}                               nullary
  and:         {"tag": "and",         "left": F, "right": F} binary
  or:          {"tag": "or",          "left": F, "right": F} binary
  diamond:     {"tag": "diamond",     "arg": F}            unary
  next:        {"tag": "next",        "arg": F}            unary
  prev:        {"tag": "prev",        "arg": F}            unary
  some_future: {"tag": "some_future", "arg": F}            unary
  some_past:   {"tag": "some_past",   "arg": F}            unary
  all_future:  {"tag": "all_future",  "arg": F}            unary
  all_past:    {"tag": "all_past",    "arg": F}            unary
```

The field naming conventions (`arg` for unary, `left`/`right` for binary, `child` for box, `event`/`guard` for untl/snce) are consistent throughout the codebase.

---

## 7. Overlapping Pattern Analysis (Detailed)

### 7.1 The `imp(_, bot)` Family

All of these have the outer structure `imp(X, bot)`:
- `neg φ = imp(φ, bot)` — X = φ (any)
- `and φ ψ = imp(imp(φ, imp(ψ, bot)), bot)` — X = `imp(φ, imp(ψ, bot))`
- `diamond φ = imp(box(imp(φ, bot)), bot)` — X = `box(imp(φ, bot))`
- `all_future φ = imp(untl(imp(φ, bot), top), bot)` — X = `untl(neg(φ), top)`
- `all_past φ = imp(snce(imp(φ, bot), top), bot)` — X = `snce(neg(φ), top)`

Discriminant for X:
- X.tag == "untl" AND X.guard is_top_pattern AND X.event is_neg_pattern → `all_future`
- X.tag == "snce" AND X.guard is_top_pattern AND X.event is_neg_pattern → `all_past`
- X.tag == "box" AND X.child is_neg_pattern → `diamond`
- X.tag == "imp" AND X.right is_neg_pattern (i.e., X.right.right = bot) → `and` (X = imp(φ, neg(ψ)))
- X.tag == anything_else (or X is neg) → `neg` (fallback)

### 7.2 The `untl(_, bot)` Pattern

- `next φ = untl(φ, bot)` — guard is bot
- `some_future φ = untl(φ, top)` — guard is top_pattern

Discriminant: guard.tag == "bot" → `next`; guard is_top_pattern → `some_future`; otherwise → keep as `untl`.

### 7.3 The `snce(_, bot)` Pattern

- `prev φ = snce(φ, bot)` — guard is bot
- `some_past φ = snce(φ, top)` — guard is top_pattern

Same logic as untl.

### 7.4 The `imp(bot, bot)` Pattern

`top = imp(bot, bot)` — a special case of `imp(_, bot)` where left is also bot. Must be checked BEFORE `neg` since `neg bot = imp(bot, bot) = top`. Both are valid folds; we prefer `top` (higher level).

Wait — `top` is Level 1, same as `neg`. But `top` is semantically more specific (both left and right must be bot). The check order within Level 1: check `top` before `neg` since `top` pattern is a strict subset of `neg bot`.

---

## 8. Testing Strategy

### 8.1 Required Property Tests

The gate requires round-trip property for 100+ randomly generated formulas and correct identification of all 11 enriched patterns.

**Property 1: unfold then fold round-trip**
```python
def test_unfold_fold_roundtrip(formula):
    """unfold(fold(formula)) should be structurally equal to unfold(formula)."""
    # Note: fold(unfold(formula)) == formula is NOT guaranteed because
    # fold maximizes enriched usage — formula may not have been maximally folded.
    # The correct round-trip is:
    assert unfold_formula(fold_formula(unfold_formula(formula))) == unfold_formula(formula)
    # Or equivalently: unfold . fold . unfold = unfold (idempotent after first unfold)
```

**Property 2: fold is idempotent after unfold**
```python
def test_fold_of_unfolded_is_stable(formula):
    """fold(fold(unfold(formula))) == fold(unfold(formula))."""
    unfolded = unfold_formula(formula)
    folded = fold_formula(unfolded)
    assert fold_formula(folded) == folded  # fold is idempotent on folded formulas
```

**Property 3: unfold produces only primitive tags**
```python
def test_unfold_produces_only_primitives(formula):
    result = unfold_formula(formula)
    # all tags in result must be in {"atom", "bot", "imp", "box", "untl", "snce"}
```

**Property 4: normalize(f, 0) == unfold(f)**
```python
def test_normalize_level0_equals_unfold(formula):
    assert normalize_formula(formula, 0) == unfold_formula(formula)
```

**Property 5: fold correctly identifies all 11 enriched patterns**
```python
def test_fold_recognizes_all_enriched_tags():
    # For each enriched tag, construct its primitive expansion and verify fold recovers it
    atoms = {"tag": "atom", "name": "p"}
    atom_q = {"tag": "atom", "name": "q"}
    bot = {"tag": "bot"}
    top = {"tag": "imp", "left": bot, "right": bot}
    
    assert fold_formula({"tag": "imp", "left": atoms, "right": bot})["tag"] == "neg"
    assert fold_formula(top)["tag"] == "top"
    assert fold_formula({"tag": "untl", "event": atoms, "guard": bot})["tag"] == "next"
    assert fold_formula({"tag": "snce", "event": atoms, "guard": bot})["tag"] == "prev"
    # ... and, or, diamond, some_future, some_past, all_future, all_past
```

### 8.2 Random Formula Generator

For property tests, we need a random formula generator:

```python
import random

def random_formula(atoms=["p", "q", "r"], max_depth=4, rng=None):
    """Generate a random formula JSON with mixed enriched and primitive tags."""
    if rng is None:
        rng = random.Random()
    all_tags = ["atom", "bot", "top", "neg", "and", "or", "imp", "box", "diamond",
                "untl", "snce", "next", "prev", "some_future", "some_past", "all_future", "all_past"]
    if max_depth == 0:
        tag = rng.choice(["atom", "bot", "top"])
    else:
        tag = rng.choice(all_tags)
    
    if tag == "atom":
        return {"tag": "atom", "name": rng.choice(atoms)}
    if tag in ("bot", "top"):
        return {"tag": tag}
    if tag in ("neg", "diamond", "next", "prev", "some_future", "some_past", "all_future", "all_past"):
        return {"tag": tag, "arg": random_formula(atoms, max_depth-1, rng)}
    if tag in ("imp", "box"):
        if tag == "box":
            return {"tag": "box", "child": random_formula(atoms, max_depth-1, rng)}
        return {"tag": "imp", "left": random_formula(atoms, max_depth-1, rng),
                "right": random_formula(atoms, max_depth-1, rng)}
    if tag in ("and", "or"):
        return {"tag": tag, "left": random_formula(atoms, max_depth-1, rng),
                "right": random_formula(atoms, max_depth-1, rng)}
    if tag in ("untl", "snce"):
        return {"tag": tag, "event": random_formula(atoms, max_depth-1, rng),
                "guard": random_formula(atoms, max_depth-1, rng)}
```

### 8.3 Test File Location

New tests should go in:
```
code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py
```

Test classes:
1. `TestUnfoldFormula` — unit tests for each of the 11 enriched tags + primitives
2. `TestFoldFormula` — unit tests for each of the 11 enriched pattern recognitions
3. `TestNormalizeFormula` — tests for level 0, 1, 2, 3 behavior
4. `TestRoundTrip` — property-based tests with 100+ random formulas
5. `TestOverlappingPatterns` — explicit tests for `all_future`/`neg` conflict, `top`/`neg bot` conflict, `and`/`or` conflict

---

## 9. Implementation Approach

### 9.1 Where to Add

All three functions go into `code/src/bimodal_logic/translation.py`. They should be added after the existing `prefix_to_infix` function and exported from `__init__.py`.

### 9.2 Helper Functions

Private helper functions to add:
- `_is_bot(node)` — check `node["tag"] == "bot"`
- `_is_top_pattern(node)` — check `imp(bot, bot)`
- `_make_bot()` — return `{"tag": "bot"}`
- `_make_top()` — return `{"tag": "imp", "left": {"tag": "bot"}, "right": {"tag": "bot"}}`

### 9.3 Export Changes

`__init__.py` needs:
```python
from .translation import (
    json_to_prefix, temporal_depth, prefix_to_infix,
    unfold_formula, fold_formula, normalize_formula,
)
```

### 9.4 Edge Cases

1. **atom**: Pass through unchanged in both fold and unfold
2. **bot**: Pass through unchanged
3. **`top` vs `neg bot`**: In fold, check `is_top_pattern(node)` (both left and right are bot) BEFORE checking `is_neg_pattern`
4. **Idempotency**: `unfold(unfold(f)) == unfold(f)` — should hold because unfold produces only primitives, and primitives unfold to themselves
5. **`normalize_formula(f, 3)`**: Should equal `fold_formula(unfold_formula(f))` — full round-trip to maximum compression
6. **`normalize_formula(f, 0)`**: Should equal `unfold_formula(f)` — primitives only

### 9.5 Implementation Order

Following TDD as required by project standards:
1. Write `test_fold_unfold.py` with failing tests first (RED phase)
2. Implement `unfold_formula` — simpler, no pattern matching needed (GREEN)
3. Implement helper predicates `_is_top_pattern`, `_is_neg_pattern` etc.
4. Implement `fold_formula` using the ordered pattern matching (GREEN)
5. Implement `normalize_formula` as composition of fold/unfold (GREEN)
6. Add property-based random round-trip tests (RED → GREEN)

---

## 10. Summary and Recommendations

### Key Findings

1. **Task 102 is fully complete**: The `translation.py` module has a clean, well-structured foundation. All 106 tests pass. The tag classification dictionaries can be reused.

2. **Unfold is straightforward**: Direct recursive dispatch on tags, building primitive nodes bottom-up from already-unfolded children.

3. **Fold requires careful ordering**: The `imp(_, bot)` family has 5 overlapping patterns (neg, and, diamond, all_future, all_past). The discriminant is the structure of the LEFT child of the outer imp. This is unambiguous if checked in order: all_future/all_past (untl/snce guard) > diamond (box) > and (imp with neg-right) > neg (anything).

4. **`top` must precede `neg`**: `imp(bot, bot)` matches both `top` and `neg bot`. Prefer `top` (higher specificity). Since both are Level 1, the check order within Level 1 is: top, neg.

5. **Outside-in fold**: Matching at the root before recursing into children is essential for correctness. Inside-out folding would reconstruct intermediate forms that don't match higher-level patterns.

6. **Round-trip property**: The correct round-trip is `unfold(fold(unfold(f))) == unfold(f)`, not `fold(unfold(f)) == f` (the latter holds only if f was already maximally folded).

### Recommended Implementation

- Add private helpers `_is_top_pattern`, `_make_bot`, `_make_top` to translation.py
- Implement `unfold_formula` as straightforward recursive descent (20-30 lines of dispatch)
- Implement `fold_formula` as outside-in pattern matching with Level 3→1 ordering (40-60 lines)
- Implement `normalize_formula` as `fold_at_level(unfold_formula(f), level)` (5 lines + internal level-aware fold)
- Export all three from `__init__.py`
- Tests in `test_fold_unfold.py` with 100+ random round-trip tests

### Risk Assessment

**Low risk**: The algorithm is deterministic and the patterns are structurally unambiguous given the correct ordering. The main risk is ordering errors in the `imp(_, bot)` family — mitigated by the explicit test for all 11 enriched patterns.

**Medium risk**: The `normalize_formula` level parameter semantics need careful definition. The task says `level=3` should be `G/H` but the dependency analysis shows `all_future`/`all_past` ARE Level 3. The `normalize_formula` contract should be: levels 0-3 correspond to the dependency levels, and `fold_at_level(f, L)` allows operators at levels 0 through L.
