# Defect 2 and Defect 3 Reproduction (Temporary Guard, Reverted)

Reproduction procedure: a temporary `if not hasattr(semantics, 'is_world'): continue` guard was
inserted into `iterate/models.py`'s `build_new_model_structure` world-state loop (the same guard
shape Phase 2 makes permanent), run against a real bimodal `BuildExample`
(`\Future A |- \Box A`, `back=2, mid=1, fwd=2`), then fully reverted (`git diff` on the file is
empty after reversion -- confirmed).

## Defect 2 -- silent exclusion gap

`ConstraintGenerator(example).create_extended_constraints([example.model_structure.z3_model])`
returns `[]` for the bimodal `build_example`: `_create_state_difference_constraints`'s
`hasattr(semantics, 'is_world')` gate short-circuits before generating anything, so the live
loop's difference constraint list is empty -- nothing forces the next solve to differ from the
first model.

## Defect 3 -- empty-graph isomorphism false positive

`example.model_structure.z3_world_states` is `MISSING` entirely (bimodal's `ModelStructure`
subclass never sets it, and `ModelDefaults` never defines a default) -- `graph.py`'s
`ModelGraph._create_graph` reads it via `getattr(model_structure, 'z3_world_states', [])`, so it
silently substitutes `[]` rather than raising. A second, genuinely different model was solved
(`ConstraintGenerator.check_satisfiability` returned `sat` on a fresh solve with the guard active
and Defect 2's empty constraint list, so nothing forced it to differ, but it is a fresh
model-value assignment regardless) and built into `new_structure`, which also has
`z3_world_states` `MISSING` for the same reason. `IsomorphismChecker.check_isomorphism(
new_structure, new_model, [structure1], [example.model_structure.z3_model])` returned `True`
(reported isomorphic) -- both graphs are empty and NetworkX 3.6.1's `nx.is_isomorphic` treats two
empty graphs as isomorphic. This is the false-positive dedup research Finding 7 called
"structurally a no-op": it is not a no-op, it is exactly the mechanism that made every live
bimodal `iterate: N > 1` run report 30/30 isomorphic skips once Defect 1 is patched around (see
`03_baseline-runner-output.txt`'s bimodal-with-guard run, `checked_model_count: 31`,
`isomorphic_model_count: 30`, "Insufficient progress" -- identical shape to the three
`is_world` theories' own baseline, for an unrelated reason: those three keep re-finding
isomorphic *real* graphs; bimodal reports every model isomorphic to the first because both
graphs it ever builds are empty).

Reproduction script: `06_defect2-3-repro.py` (the exact code run; not part of the shipped
codebase).
