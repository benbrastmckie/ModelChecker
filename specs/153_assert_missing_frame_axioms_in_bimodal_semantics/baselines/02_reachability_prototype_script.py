"""
Task 153 Phase 2: time-boxed measurement of the definitional-reachability
alternative for task_rel (scratchpad-style, process-local; core.py never
edited on disk by this script).

Redefines task_rel(w, d, v) as the reachability, in exactly `d` steps, of a
single free binary relation R : WorldStateSort x WorldStateSort -> Bool,
via a Python-level macro expanding to a finite disjunction over unrolled
d-length compositions of R for each concrete d in the bounded window
(-(M-1), M-1) -- 2M-1 cases per the plan's Phase 2 task description.
z3.TransitiveClosure is NOT used (no in-tree precedent; wrong shape for a
duration-indexed relation; Z3-specific against z3_shim.py's cvc5 migration).

Mechanism: BimodalSemantics.task_rel is only ever called as
self.task_rel(w, d, v) throughout the codebase (verified: no bare
FuncDeclRef reference elsewhere), so a ReachabilitySemantics subclass can
transparently monkeypatch self.task_rel to a plain Python closure returning
the macro-expanded Z3 formula, right after define_primitives() runs and
before build_frame_constraints() (and the rest of the pipeline) consumes it.

This measures whether the macro-expanded definition performs acceptably; it
does NOT attempt to re-derive nullity_identity/converse/forward_comp as
theorems of the new definition (that is a separate, larger design question
noted in the report Section 3.4 and explicitly out of scope for this task
even on a "go" result) -- the existing frame-axiom assertions are kept
as-is, now stated over the macro-expanded task_rel.
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

SUBSET = ["BM_TH_1", "BM_TH_2", "BM_TH_3", "BM_TH_4", "EX_CM_1", "EX_TH_1"]


class ReachabilitySemantics(BimodalSemantics):
    """BimodalSemantics with task_rel redefined as bounded R-reachability."""

    def define_primitives(self):
        super().define_primitives()
        R = z3.Function('unit_task_R', self.WorldStateSort, self.WorldStateSort, z3.BoolSort())
        self._reach_R = R
        self._chain_fn_cache = {}
        M = self.M

        def _chain(w, k, v):
            if k == 0:
                return w == v
            if k > 0:
                if k == 1:
                    return R(w, v)
                fns = self._chain_fn_cache.get(k)
                if fns is None:
                    fns = [
                        z3.Function(f'chain_{k}_{i}', self.WorldStateSort,
                                    self.WorldStateSort, self.WorldStateSort)
                        for i in range(1, k)
                    ]
                    self._chain_fn_cache[k] = fns
                nodes = [w] + [f(w, v) for f in fns] + [v]
                return z3.And(*[R(nodes[i], nodes[i + 1]) for i in range(len(nodes) - 1)])
            return _chain(v, -k, w)

        def task_rel_defined(w, d, v):
            branches = [z3.And(d == k, _chain(w, k, v)) for k in range(-(M - 1), M)]
            return z3.Or(*branches)

        # Monkeypatch: every call site does self.task_rel(w, d, v).
        self.task_rel = task_rel_defined

    def build_forward_comp_constraint(self):
        """Override: the parent's explicit z3.MultiPattern hint names
        self.task_rel(w, d1, v) etc. as trigger terms. Under the
        reachability redefinition those calls expand to Or/And compound
        formulas, which Z3 rejects as patterns ("'and'/'or' cannot be used
        in patterns" -> "invalid pattern"). Dropping the explicit pattern
        (falling back to Z3's automatic pattern selection) is the minimal
        change needed to even run this prototype; this is itself a data
        point: the reachability redefinition is incompatible with the
        existing hand-tuned multi-pattern without further rework."""
        w = z3.BitVec('comp_w', self.N)
        v = z3.BitVec('comp_v', self.N)
        u = z3.BitVec('comp_u', self.N)
        d1 = z3.Int('comp_d1')
        d2 = z3.Int('comp_d2')

        body = z3.Implies(
            z3.And(
                self.task_rel(w, d1, v),
                self.task_rel(v, d2, u),
                self.is_valid_duration(d1),
                self.is_valid_duration(d2),
                self.is_valid_duration(d1 + d2)
            ),
            self.task_rel(w, d1 + d2, u)
        )
        return z3.ForAll([w, v, u, d1, d2], body)


def run_one(example_case, semantics_class, arm_name):
    with isolated_z3_context():
        result = run_enhanced_test(
            example_case,
            semantics_class,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
            strategy_name=arm_name,
        )
    return {
        "model_found": result.model_found,
        "timeout": result.timeout,
        "check_result": result.check_result,
        "z3_model_status": result.z3_model_status,
        "solving_time": round(result.solving_time, 2),
        "error": result.error_message,
    }


def main():
    out = {}
    t_start = time.time()
    for name in SUBSET:
        example_case = ALL_EXAMPLES[name]
        settings = example_case[2]
        print(f"=== {name} (N={settings.get('N')}, M={settings.get('M')}, "
              f"max_time={settings.get('max_time')}) ===", flush=True)

        t0 = time.time()
        baseline = run_one(example_case, BimodalSemantics, "baseline")
        t1 = time.time()
        print(f"  baseline: check={baseline['check_result']} status={baseline['z3_model_status']} "
              f"t={baseline['solving_time']}s", flush=True)

        t2 = time.time()
        try:
            reach = run_one(example_case, ReachabilitySemantics, "reachability")
        except Exception as e:
            reach = {"error": f"EXCEPTION: {type(e).__name__}: {e}"}
        t3 = time.time()
        print(f"  reachability: {reach}", flush=True)

        out[name] = {
            "N": settings.get("N"), "M": settings.get("M"),
            "baseline": baseline, "reachability": reach,
            "baseline_wall_s": round(t1 - t0, 2),
            "reachability_wall_s": round(t3 - t2, 2),
            "elapsed_since_start_s": round(t3 - t_start, 2),
        }
        with open("/home/benjamin/Projects/ModelChecker/specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/02_reachability-prototype-raw.json", "w") as f:
            json.dump(out, f, indent=2)

        if time.time() - t_start > 5400:  # 1.5h hard time-box
            print("TIME-BOX EXPIRED", flush=True)
            break

    print("DONE", flush=True)


if __name__ == "__main__":
    main()
