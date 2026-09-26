"""
Task-188 regression/sweep harness (scratchpad-style, process-local; no
source-tree modification by this script itself).

Adapted from
specs/archive/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_frame-axiom-regression-script.py
(task 153's frame-axiom harness). This script's three arms are:

  1. baseline        -- whatever BimodalSemantics.build_seriality_constraint /
                         build_interpolation_constraint currently are on disk,
                         completely unmodified. Before Phase 3 lands, this is
                         the pre-rename (committed) tree; after Phase 3 lands,
                         this IS the post-rename tree, since Phase 3 edits
                         core.py directly. Used for the "before"/"after"
                         full-example-set snapshots (Phase 1, Phase 4).

  2. renamed          -- both build_seriality_constraint and
                         build_interpolation_constraint monkeypatched, in
                         this process only, to script-local reconstructions
                         whose Z3 symbol identifiers are alpha-renamed
                         (same sorts, same arities, same ForAll/Implies/And
                         structure, same guard -- no logical content
                         changed). Used for the >= 20-seed sweep (Phase 2)
                         BEFORE any source edit is made.

  3. renamed_single    -- only one of the two axioms renamed, selectable via
                         --axiom {seriality,interpolation}, preserving the
                         research report's SS5 single-axiom finding as a
                         rerunnable check. Not used by the Phase 2 gate
                         itself (which uses `renamed`, both axioms), but kept
                         available for spot re-verification.

Seed pinning: --seed N calls z3.set_param('smt.random_seed', N) and
z3.set_param('sat.random_seed', N) before each run, matching the convention
BM_CM_1_settings and BM_CM_4_settings already cite ("pinned smt/sat.random_seed").

Counter poisoning: --poison-counter K sets
model_checker.theory_lib.bimodal.operators._bound_var_counter to
itertools.count(K) immediately before constructing BimodalSemantics, exactly
reproducing test_bound_var_counter_isolation.py's parametrize states
[0, 17, 30]. BimodalSemantics.__init__ -> _reset_global_state() resets this
counter to 0 regardless (core.py:118-122), so poisoning only has an
observable effect if that reset is bypassed; this option exists to let the
harness reproduce the isolation test's exact construction-time state for
verification, not to defeat the reset.

Probe budget override: --probe-budget SECONDS overrides every selected
example's max_time for that run only (the on-disk settings dict is not
mutated; the override is applied to a shallow copy passed into run_enhanced_test).

Monkeypatching happens only in this process -- core.py on disk is untouched
by this script itself.
"""
import argparse
import itertools
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
from model_checker.theory_lib.bimodal import operators as bimodal_operators_module
from model_checker.theory_lib.bimodal.examples import (
    countermodel_examples,
    theorem_examples,
)

ALL_EXAMPLES = {**countermodel_examples, **theorem_examples}

_ORIG_SERIALITY = BimodalSemantics.build_seriality_constraint
_ORIG_INTERPOLATION = BimodalSemantics.build_interpolation_constraint


def _build_seriality_constraint_renamed(self):
    """Alpha-renamed reconstruction of build_seriality_constraint. Same
    sorts, arities, ForAll/Implies/And structure, and guard as the
    committed method -- only the Z3 symbol identifiers differ
    (serial_succ -> serial_succ_r2, etc.), to isolate whether solve cost is
    sensitive to incidental symbol identity rather than logical content."""
    serial_succ = z3.Function(
        'serial_succ_r2', self.WorldStateSort, self.TimeSort, self.WorldStateSort
    )
    serial_pred = z3.Function(
        'serial_pred_r2', self.WorldStateSort, self.TimeSort, self.WorldStateSort
    )
    w = z3.BitVec('serial_w_r2', self.N)
    x = z3.Int('serial_x_r2')
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


def _build_interpolation_constraint_renamed(self):
    """Alpha-renamed reconstruction of build_interpolation_constraint. Same
    sorts, arities, ForAll/Implies/And structure, and guards as the
    committed method -- only the Z3 symbol identifiers differ
    (interp_witness -> interp_witness_r2, etc.)."""
    interp_witness = z3.Function(
        'interp_witness_r2', self.WorldStateSort, z3.IntSort(),
        z3.IntSort(), self.WorldStateSort, self.WorldStateSort
    )
    w = z3.BitVec('interp_w_r2', self.N)
    v = z3.BitVec('interp_v_r2', self.N)
    d1 = z3.Int('interp_d1_r2')
    d2 = z3.Int('interp_d2_r2')
    u = interp_witness(w, d1, d2, v)
    return z3.ForAll(
        [w, v, d1, d2],
        z3.Implies(
            z3.And(
                self.is_valid_duration(d1),
                self.is_valid_duration(d2),
                self.is_valid_duration(d1 + d2),
                self.task_rel(w, d1 + d2, v)
            ),
            z3.And(
                self.task_rel(w, d1, u),
                self.task_rel(u, d2, v)
            )
        )
    )


def _apply_arm(arm, axiom):
    if arm == "baseline":
        BimodalSemantics.build_seriality_constraint = _ORIG_SERIALITY
        BimodalSemantics.build_interpolation_constraint = _ORIG_INTERPOLATION
    elif arm == "renamed":
        BimodalSemantics.build_seriality_constraint = _build_seriality_constraint_renamed
        BimodalSemantics.build_interpolation_constraint = _build_interpolation_constraint_renamed
    elif arm == "renamed_single":
        assert axiom in ("seriality", "interpolation"), axiom
        if axiom == "seriality":
            BimodalSemantics.build_seriality_constraint = _build_seriality_constraint_renamed
            BimodalSemantics.build_interpolation_constraint = _ORIG_INTERPOLATION
        else:
            BimodalSemantics.build_seriality_constraint = _ORIG_SERIALITY
            BimodalSemantics.build_interpolation_constraint = _build_interpolation_constraint_renamed
    else:
        raise ValueError(f"unknown arm: {arm}")


def _restore():
    BimodalSemantics.build_seriality_constraint = _ORIG_SERIALITY
    BimodalSemantics.build_interpolation_constraint = _ORIG_INTERPOLATION


def run_one(example_case, arm, axiom=None, seed=None, poison_counter=None, probe_budget=None):
    _apply_arm(arm, axiom)
    try:
        if seed is not None:
            z3.set_param('smt.random_seed', seed)
            z3.set_param('sat.random_seed', seed)
        if poison_counter is not None:
            bimodal_operators_module._bound_var_counter = itertools.count(poison_counter)

        premises, conclusions, settings = example_case
        run_settings = dict(settings)
        if probe_budget is not None:
            run_settings['max_time'] = probe_budget
        run_case = [premises, conclusions, run_settings]

        with isolated_z3_context():
            result = run_enhanced_test(
                run_case,
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
        _restore()


def cmd_sweep(args):
    """Run one named example across many seeds, for a single arm."""
    case = ALL_EXAMPLES[args.example]
    settings = case[2]
    seeds = list(range(args.seed_start, args.seed_start + args.num_seeds))
    out = {
        "example": args.example,
        "arm": args.arm,
        "axiom": args.axiom,
        "probe_budget": args.probe_budget,
        "expectation": settings.get("expectation"),
        "N": settings.get("N"),
        "M": settings.get("M"),
        "results": {},
    }
    for i, seed in enumerate(seeds):
        t0 = time.time()
        result = run_one(
            case, args.arm, axiom=args.axiom, seed=seed,
            probe_budget=args.probe_budget,
        )
        t1 = time.time()
        out["results"][str(seed)] = {**result, "wall_s": round(t1 - t0, 2)}
        print(
            f"[{i+1}/{len(seeds)}] seed={seed} check={result['check_result']} "
            f"found={result['model_found']} timeout={result['timeout']} "
            f"t={result['solving_time']}s",
            flush=True,
        )
        with open(args.out, "w") as f:
            json.dump(out, f, indent=2)
    print("DONE")


def cmd_counter_states(args):
    """Run one named example across the isolation test's poisoned-counter states."""
    case = ALL_EXAMPLES[args.example]
    settings = case[2]
    states = [0, 17, 30]
    out = {
        "example": args.example,
        "arm": args.arm,
        "probe_budget": args.probe_budget,
        "expectation": settings.get("expectation"),
        "results": {},
    }
    for state in states:
        t0 = time.time()
        result = run_one(
            case, args.arm, poison_counter=state, probe_budget=args.probe_budget,
        )
        t1 = time.time()
        out["results"][str(state)] = {**result, "wall_s": round(t1 - t0, 2)}
        print(
            f"poisoned_start={state} check={result['check_result']} "
            f"found={result['model_found']} t={result['solving_time']}s",
            flush=True,
        )
    with open(args.out, "w") as f:
        json.dump(out, f, indent=2)
    print("DONE")


def cmd_full(args):
    """Run the full example set for one arm, writing an incremental JSON snapshot."""
    names = sorted(ALL_EXAMPLES.keys())
    out = {}
    for i, name in enumerate(names):
        example_case = ALL_EXAMPLES[name]
        settings = example_case[2]
        print(
            f"[{i+1}/{len(names)}] {name} (expectation={settings.get('expectation')}, "
            f"N={settings.get('N')}, M={settings.get('M')}, max_time={settings.get('max_time')})",
            flush=True,
        )
        t0 = time.time()
        result = run_one(example_case, args.arm, axiom=args.axiom, seed=args.seed)
        t1 = time.time()
        entry = {
            "expectation": settings.get("expectation"),
            "N": settings.get("N"),
            "M": settings.get("M"),
            "max_time": settings.get("max_time"),
            "arm": args.arm,
            "result": result,
            "wall_s": round(t1 - t0, 2),
        }
        out[name] = entry
        print(
            f"    {args.arm}: found={result['model_found']} check={result['check_result']} "
            f"status={result['z3_model_status']} t={result['solving_time']}s",
            flush=True,
        )
        with open(args.out, "w") as f:
            json.dump(out, f, indent=2)
    print(f"DONE (n={len(names)})")


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="mode", required=True)

    p_full = sub.add_parser("full", help="run the full example set for one arm")
    p_full.add_argument("--arm", required=True, choices=["baseline", "renamed", "renamed_single"])
    p_full.add_argument("--axiom", choices=["seriality", "interpolation"], default=None)
    p_full.add_argument("--seed", type=int, default=None)
    p_full.add_argument("--out", required=True)
    p_full.set_defaults(func=cmd_full)

    p_sweep = sub.add_parser("sweep", help="run one example across many seeds")
    p_sweep.add_argument("--example", required=True)
    p_sweep.add_argument("--arm", required=True, choices=["baseline", "renamed", "renamed_single"])
    p_sweep.add_argument("--axiom", choices=["seriality", "interpolation"], default=None)
    p_sweep.add_argument("--seed-start", type=int, default=1000)
    p_sweep.add_argument("--num-seeds", type=int, default=20)
    p_sweep.add_argument("--probe-budget", type=float, default=40)
    p_sweep.add_argument("--out", required=True)
    p_sweep.set_defaults(func=cmd_sweep)

    p_counter = sub.add_parser("counter-states", help="run one example across [0, 17, 30]")
    p_counter.add_argument("--example", required=True)
    p_counter.add_argument("--arm", required=True, choices=["baseline", "renamed", "renamed_single"])
    p_counter.add_argument("--probe-budget", type=float, default=40)
    p_counter.add_argument("--out", required=True)
    p_counter.set_defaults(func=cmd_counter_states)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
