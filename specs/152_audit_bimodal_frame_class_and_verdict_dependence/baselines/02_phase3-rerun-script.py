"""
Phase 3 re-run (bimodal frame-class audit): decide BM_TH_1/BM_TH_2's undecided baseline sides at
a raised max_time, and reproduce BM_TH_3/BM_TH_4's clean flips at the same session's host
conditions.

Same monkeypatch methodology as baselines/01_abundance-removal-script.py, unchanged, applied to
exactly the 4 abundance-dependent examples. BM_TH_1/BM_TH_2's max_time is raised from 30s to a
capped 90s (3x) for the baseline (with-abundance) side only; the no_abundance side and BM_TH_3/
BM_TH_4 keep their original settings unchanged. core.py on disk is never touched.
"""
import copy
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
    BM_TH_1_example,
    BM_TH_2_example,
    BM_TH_3_example,
    BM_TH_4_example,
)

_ORIG_BUILD_FRAME_CONSTRAINTS = BimodalSemantics.build_frame_constraints

RAISED_MAX_TIME = 90  # capped escalation: 3x the original 30s ceiling, explicit stop point


def build_frame_constraints_no_abundance(self):
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


EXAMPLES = {
    "BM_TH_1": BM_TH_1_example,
    "BM_TH_2": BM_TH_2_example,
    "BM_TH_3": BM_TH_3_example,
    "BM_TH_4": BM_TH_4_example,
}

RAISED = {"BM_TH_1", "BM_TH_2"}


def main():
    print(f"HOST LOAD AT START: {time.strftime('%Y-%m-%d %H:%M:%S')}", flush=True)
    out = {}
    for name, example_case in EXAMPLES.items():
        case = copy.deepcopy(example_case)
        settings = case[2]
        if name in RAISED:
            settings['max_time'] = RAISED_MAX_TIME
        print(f"[{name}] expectation={settings.get('expectation')} N={settings.get('N')} "
              f"M={settings.get('M')} max_time={settings.get('max_time')}", flush=True)
        t0 = time.time()
        baseline = run_one(case, patched=False)
        t1 = time.time()
        no_abund = run_one(case, patched=True)
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

    print(f"HOST LOAD AT END: {time.strftime('%Y-%m-%d %H:%M:%S')}", flush=True)
    with open("/tmp/claude-1000/-home-benjamin-Projects-ModelChecker/15065234-5397-4b68-927a-0fb793f145d2/scratchpad/phase3_results.json", "w") as f:
        json.dump(out, f, indent=2)
    print("DONE")


if __name__ == "__main__":
    main()
