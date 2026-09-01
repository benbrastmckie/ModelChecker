"""
Audit baseline script (scratchpad, audit-only, no source tree modifications).

For every example in bimodal/examples.py's unit_tests dict, run the model
checker twice:
  1. baseline  -- unmodified BimodalSemantics.build_frame_constraints
  2. no_abund  -- monkeypatched to drop the abundance constraint
                  (capped_skolem_abundance_constraint /
                  depth_bounded_skolem_abundance_constraint) from the
                  constraint list, everything else unchanged.

Records z3_model_status (True=SAT/model found), timeout, check_result,
solving_time for both runs, and flags whether the verdict flipped.

Monkeypatching happens only in this throwaway script's process -- core.py
on disk is never touched (per the audit's non-goal on semantics changes).
"""
import json
import sys
import time

sys.path.insert(0, "/home/benjamin/Projects/ModelChecker/code/src")

import z3

from model_checker import ModelConstraints, Syntax
from model_checker.utils.testing import run_enhanced_test
from model_checker.utils.context import isolated_z3_context
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.examples import (
    countermodel_examples,
    theorem_examples,
)

ALL_EXAMPLES = {**countermodel_examples, **theorem_examples}

# Save the original method so we can monkeypatch/restore cleanly.
_ORIG_BUILD_FRAME_CONSTRAINTS = BimodalSemantics.build_frame_constraints


def build_frame_constraints_no_abundance(self):
    """Same as build_frame_constraints but with the abundance constraint
    (item 8, capped_skolem_abundance_constraint / depth_bounded variant)
    removed from the returned list. Everything else identical."""
    # Rebuild the list directly using the same code path as the real
    # method, with skolem_abundance forced to [].
    valid_main_world = self.is_world(self.main_world)
    valid_main_time = self.is_valid_time(self.main_time)

    enumerate_world = z3.Int('enumerate_world')
    enumeration_constraint = z3.ForAll(
        [enumerate_world],
        z3.Implies(self.is_world(enumerate_world), enumerate_world >= 0),
    )

    convex_world = z3.Int('convex_world')
    convex_world_ordering = z3.ForAll(
        [convex_world],
        z3.Implies(
            z3.And(self.is_world(convex_world), convex_world > 0),
            self.is_world(convex_world - 1)
        )
    )

    world_interval = self.world_interval_constraint()

    lawful_world = z3.Int('lawful_world_id')
    lawful_time = z3.Int('lawful_time')
    lawful = z3.ForAll(
        [lawful_world, lawful_time],
        z3.Implies(
            z3.And(
                self.is_world(lawful_world),
                self.is_valid_time(lawful_time, -1),
                self.is_valid_time_for_world(lawful_world, lawful_time),
                self.is_valid_time_for_world(lawful_world, lawful_time + 1),
            ),
            self.task_rel(
                z3.Select(self.world_function(lawful_world), lawful_time),
                z3.IntVal(1),
                z3.Select(self.world_function(lawful_world), lawful_time + 1)
            )
        )
    )

    nullity_identity = self.build_nullity_identity_constraint()
    converse = self.build_converse_constraint()
    forward_comp = self.build_forward_comp_constraint()

    world_one = z3.Int('world_one')
    world_two = z3.Int('world_two')
    some_time = z3.Int('some_time')
    world_uniqueness = z3.ForAll(
        [world_one, world_two],
        z3.Implies(
            z3.And(
                self.is_world(world_one),
                self.is_world(world_two),
                world_one != world_two
            ),
            z3.Exists(
                [some_time],
                z3.And(
                    self.is_valid_time(some_time),
                    self.is_valid_time_for_world(world_one, some_time),
                    self.is_valid_time_for_world(world_two, some_time),
                    z3.Select(self.world_function(world_one), some_time) !=
                    z3.Select(self.world_function(world_two), some_time)
                )
            )
        )
    )

    return [
        valid_main_world,
        valid_main_time,
        enumeration_constraint,
        convex_world_ordering,
        world_interval,
        lawful,
        nullity_identity,
        converse,
        forward_comp,
        # skolem_abundance REMOVED here (this is the experiment)
        world_uniqueness,
    ]


def run_one(example_case, patched):
    if patched:
        BimodalSemantics.build_frame_constraints = build_frame_constraints_no_abundance
    else:
        BimodalSemantics.build_frame_constraints = _ORIG_BUILD_FRAME_CONSTRAINTS
    try:
        with isolated_z3_context():
            result = run_enhanced_test(
                example_case,
                BimodalSemantics,
                BimodalProposition,
                bimodal_operators,
                Syntax,
                ModelConstraints,
                BimodalStructure,
                strategy_name="no_abundance" if patched else "baseline",
            )
        return {
            "model_found": result.model_found,
            "timeout": result.timeout,
            "check_result": result.check_result,
            "z3_model_status": result.z3_model_status,
            "solving_time": round(result.solving_time, 2),
            "error": result.error_message,
        }
    finally:
        BimodalSemantics.build_frame_constraints = _ORIG_BUILD_FRAME_CONSTRAINTS


def main():
    names = sorted(ALL_EXAMPLES.keys())
    out = {}
    for i, name in enumerate(names):
        example_case = ALL_EXAMPLES[name]
        settings = example_case[2]
        print(f"[{i+1}/{len(names)}] {name} (expectation={settings.get('expectation')}, "
              f"N={settings.get('N')}, M={settings.get('M')}, max_time={settings.get('max_time')})",
              flush=True)
        t0 = time.time()
        baseline = run_one(example_case, patched=False)
        t1 = time.time()
        no_abund = run_one(example_case, patched=True)
        t2 = time.time()
        flipped = (
            baseline["check_result"] != "inconclusive"
            and no_abund["check_result"] != "inconclusive"
            and baseline["z3_model_status"] != no_abund["z3_model_status"]
        )
        entry = {
            "expectation": settings.get("expectation"),
            "N": settings.get("N"),
            "M": settings.get("M"),
            "max_time": settings.get("max_time"),
            "baseline": baseline,
            "no_abundance": no_abund,
            "verdict_flipped": flipped,
            "baseline_wall_s": round(t1 - t0, 2),
            "no_abundance_wall_s": round(t2 - t1, 2),
        }
        out[name] = entry
        print(f"    baseline: found={baseline['model_found']} check={baseline['check_result']} "
              f"t={baseline['solving_time']}s | no_abundance: found={no_abund['model_found']} "
              f"check={no_abund['check_result']} t={no_abund['solving_time']}s | "
              f"FLIPPED={flipped}", flush=True)
        # Write incrementally so a partial run is still useful if interrupted.
        with open("/tmp/claude-1000/-home-benjamin-Projects-ModelChecker/15065234-5397-4b68-927a-0fb793f145d2/scratchpad/baseline_results.json", "w") as f:
            json.dump(out, f, indent=2)

    print("DONE")


if __name__ == "__main__":
    main()
