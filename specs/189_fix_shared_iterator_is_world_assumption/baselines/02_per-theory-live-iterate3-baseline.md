# Per-Theory Live `iterate: 3` Baseline (Pre-Change)

Recorded via a scratch script driving `<Theory>ModelIterator.iterate_generator()` directly
against a real `BuildExample` (no mocks on the solver/model path), one representative
countermodel example per theory, `iterate: 3` forced via settings, `max_time: 10`.

All three `is_world`-bearing theories hit the same generic termination condition
(`TerminationManager.should_terminate`'s "Insufficient progress" branch:
`checked_model_count > 10 * max_iterations` i.e. `> 30`), because the live loop's difference
constraint (`ConstraintGenerator._create_difference_constraint`, gated on `hasattr(semantics,
'is_world')`) only toggles world-membership per state and is comparatively weak against these
particular formulas, so most re-solves land on graph-isomorphic re-shufflings of the same
underlying model. This is the framework's actual current behavior for these examples, not a
new observation from this task; it is recorded here purely so Phase 6 can diff its own
post-change numbers against it.

## logos (`B, (A -> B) |- A`, N=4)
- models yielded (after first): 0
- total model_structures (incl. first): 1
- checked_model_count: 31
- isomorphic_model_count: 30
- termination: "Insufficient progress - checked too many models with few results"

## imposition (`~A, A diamondright C, A boxright C |- (A & B) boxright C`, N=3)
- models yielded (after first): 0
- total model_structures (incl. first): 1
- checked_model_count: 31
- isomorphic_model_count: 30
- termination: "Insufficient progress - checked too many models with few results"

## exclusion (`(~A v ~B) |- ~(A & B)`, N=3)
- models yielded (after first): 0
- total model_structures (incl. first): 1
- checked_model_count: 31
- isomorphic_model_count: 30
- termination: "Insufficient progress - checked too many models with few results"

Full runner output: `03_baseline-runner-output.txt`.
