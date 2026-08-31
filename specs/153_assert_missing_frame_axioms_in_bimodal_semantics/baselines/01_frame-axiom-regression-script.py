"""
Task-153 regression harness (scratchpad-style, process-local, no source tree
modifications by this script itself).

Adapted from specs/152_.../baselines/01_abundance-removal-script.py (task 152's
abundance-removal harness). This script's two arms are:

  1. baseline        -- whatever BimodalSemantics.build_frame_constraints
                         currently is on disk, completely unmodified. Before
                         Phase 4 lands, this is the pre-task-153 method (no
                         Seriality/Interpolation). After Phase 4 lands, this IS
                         the post-change method (Seriality/Interpolation
                         already asserted), since Phase 4 edits core.py
                         directly.
  2. with_new_axioms  -- a script-local, self-contained reconstruction of
                         build_frame_constraints that inlines the Skolemized
                         Seriality and Interpolation constraints from the
                         research report (Section 2.1 / 3.1), independent of
                         whether core.py has been changed yet. This lets the
                         "with new axioms" scenario be measured at any point
                         in the task, and (post-Phase-4) doubles as a
                         cross-check that the inline reconstruction matches
                         the real, committed core.py implementation.

Phase 1 invokes ONLY the baseline arm, against the current (pre-change) tree,
to produce 01_pre-change-verdicts.json -- a same-host "before" reference to
sit alongside task 152's recorded baseline for Phase 7's diff.

Phase 7 invokes the with_new_axioms arm against the post-Phase-4 tree to
produce 03_post-change-verdicts.json.

Monkeypatching happens only in this throwaway script's process --
core.py on disk is never touched by this script.
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


def _build_seriality_constraint_inline(self):
    """Script-local reconstruction of build_seriality_constraint (report Section 2.1).

    Skolemized: one top-level ForAll([w, x]), two Skolem functions
    (serial_succ, serial_pred), no nested Exists.
    """
    serial_succ = z3.Function(
        'serial_succ_inline', self.WorldStateSort, self.TimeSort, self.WorldStateSort
    )
    serial_pred = z3.Function(
        'serial_pred_inline', self.WorldStateSort, self.TimeSort, self.WorldStateSort
    )
    w = z3.BitVec('serial_w_inline', self.N)
    x = z3.Int('serial_x_inline')
    guard = z3.And(x >= 0, self.is_valid_duration(x))
    return z3.ForAll(
        [w, x],
        z3.Implies(
            guard,
            z3.And(
                self.task_rel(w, x, serial_succ(w, x)),
                self.task_rel(serial_pred(w, x), x, w),
            )
        )
    )


def _build_interpolation_constraint_inline(self):
    """Script-local reconstruction of build_interpolation_constraint (report Section 3.1).

    Skolemized: one top-level ForAll([w, v, d1, d2]), one Skolem function
    (interp_witness), no nested Exists. This is the MANDATED encoding -- the
    nested ForAll/Exists reading is a measured BM_TH_3/BM_TH_4 regression at
    M=2 and is never used here.
    """
    interp_witness = z3.Function(
        'interp_witness_inline', self.WorldStateSort, z3.IntSort(),
        z3.IntSort(), self.WorldStateSort, self.WorldStateSort
    )
    w = z3.BitVec('interpS_w_inline', self.N)
    v = z3.BitVec('interpS_v_inline', self.N)
    d1 = z3.Int('interpS_d1_inline')
    d2 = z3.Int('interpS_d2_inline')
    u = interp_witness(w, d1, d2, v)
    return z3.ForAll(
        [w, v, d1, d2],
        z3.Implies(
            z3.And(self.is_valid_duration(d1), self.is_valid_duration(d2),
                   self.is_valid_duration(d1 + d2), self.task_rel(w, d1 + d2, v)),
            z3.And(self.task_rel(w, d1, u), self.task_rel(u, d2, v))
        )
    )


def build_frame_constraints_with_new_axioms(self):
    """Same overall structure as the real build_frame_constraints, but with
    Seriality and Interpolation inserted (inline, script-local Skolemized
    builders above) after forward_comp and before skolem_abundance --
    mirroring the real insertion point Phase 4 uses in core.py."""
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

    # --- Task 153: the two new axioms, inline Skolemized reconstructions ---
    seriality = _build_seriality_constraint_inline(self)
    interpolation = _build_interpolation_constraint_inline(self)
    # -------------------------------------------------------------------

    temporal_depth = getattr(self, 'temporal_depth', None)
    if temporal_depth is None:
        skolem_abundance = [self.capped_skolem_abundance_constraint()]
    elif temporal_depth == 0:
        skolem_abundance = []
    elif self.M <= 2:
        skolem_abundance = [self.capped_skolem_abundance_constraint()]
    else:
        skolem_abundance = self.depth_bounded_skolem_abundance_constraint(
            max_shift=temporal_depth
        )

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
        seriality,
        interpolation,
        *skolem_abundance,
        world_uniqueness,
    ]


def run_one(example_case, arm):
    if arm == "with_new_axioms":
        BimodalSemantics.build_frame_constraints = build_frame_constraints_with_new_axioms
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
                strategy_name=arm,
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


def main(arm, out_path):
    assert arm in ("baseline", "with_new_axioms"), arm
    names = sorted(ALL_EXAMPLES.keys())
    out = {}
    for i, name in enumerate(names):
        example_case = ALL_EXAMPLES[name]
        settings = example_case[2]
        print(f"[{i+1}/{len(names)}] {name} (expectation={settings.get('expectation')}, "
              f"N={settings.get('N')}, M={settings.get('M')}, max_time={settings.get('max_time')})",
              flush=True)
        t0 = time.time()
        result = run_one(example_case, arm)
        t1 = time.time()
        entry = {
            "expectation": settings.get("expectation"),
            "N": settings.get("N"),
            "M": settings.get("M"),
            "max_time": settings.get("max_time"),
            "arm": arm,
            "result": result,
            "wall_s": round(t1 - t0, 2),
        }
        out[name] = entry
        print(f"    {arm}: found={result['model_found']} check={result['check_result']} "
              f"status={result['z3_model_status']} t={result['solving_time']}s", flush=True)
        # Write incrementally so a partial run is still useful if interrupted.
        with open(out_path, "w") as f:
            json.dump(out, f, indent=2)

    print("DONE")


if __name__ == "__main__":
    arm = sys.argv[1] if len(sys.argv) > 1 else "baseline"
    out_path = sys.argv[2] if len(sys.argv) > 2 else (
        "/home/benjamin/Projects/ModelChecker/specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_pre-change-verdicts.json"
        if arm == "baseline" else
        "/home/benjamin/Projects/ModelChecker/specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/03_post-change-verdicts.json"
    )
    main(arm, out_path)
