"""Profile different abundance constraint strategies on BM_TH_1.

This script compares:
  A) Original: +/-1 Skolem abundance (skolem_abundance_constraint)
  B) Full existential: full_abundance_constraint (nested ForAll/Exists with variable shift)
  C) Full Skolem: skolem_full_abundance_constraint (shift_of Skolem function)
  D) Capped Skolem: capped_skolem_abundance_constraint (boundary-checked shift_of)

Run from the project root with:
  python -m code.src.model_checker.theory_lib.bimodal.profile_abundance
OR
  cd code/src && python -m model_checker.theory_lib.bimodal.profile_abundance
"""
import time
import sys
import os

# Allow running from project root
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))

from model_checker import z3_shim as z3
from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.examples import (
    BM_TH_1_example,
    BM_TH_2_example,
)


def run_with_strategy(strategy_name, abundance_method_name, max_time=30):
    """Run BM_TH_1 with a particular abundance strategy and time it."""
    import importlib
    import model_checker.theory_lib.bimodal.semantic as sem_module

    # Monkey-patch the build_frame_constraints to use the chosen method
    original_build_frame = BimodalSemantics.build_frame_constraints

    def patched_build_frame(self):
        constraints = original_build_frame(self)
        return constraints

    # Patch the skolem_abundance_constraint call in build_frame_constraints
    # by replacing the method reference
    original_method = getattr(BimodalSemantics, 'skolem_abundance_constraint')
    replacement = getattr(BimodalSemantics, abundance_method_name)

    # Temporarily replace the method
    BimodalSemantics.skolem_abundance_constraint = replacement

    settings = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': max_time,
        'expectation': False,  # We now expect NO countermodel (valid theorem)
    }
    example = [
        ['\\Box A'],
        ['\\Future A'],
        settings,
    ]

    start = time.time()
    try:
        result = run_test(
            example,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )
        elapsed = time.time() - start
        status = "PASS (no countermodel, theorem valid)" if result else "FAIL (countermodel found)"
    except Exception as e:
        elapsed = time.time() - start
        status = f"ERROR: {e}"
        result = False

    # Restore original method
    BimodalSemantics.skolem_abundance_constraint = original_method

    return {
        'strategy': strategy_name,
        'method': abundance_method_name,
        'result': result,
        'status': status,
        'elapsed': elapsed,
    }


def main():
    print("=" * 70)
    print("Profiling abundance strategies on BM_TH_1 (Box A -> Future A)")
    print("N=2, M=2, max_time=30s per strategy")
    print("Expected: no countermodel (theorem should be valid)")
    print("=" * 70)

    strategies = [
        ("A: Original +/-1 Skolem", "skolem_abundance_constraint"),
        ("B: Full Existential", "full_abundance_constraint"),
        ("C: Full Skolem (shift_of)", "skolem_full_abundance_constraint"),
        ("D: Capped Skolem", "capped_skolem_abundance_constraint"),
    ]

    results = []
    for name, method in strategies:
        print(f"\nRunning strategy {name}...")
        r = run_with_strategy(name, method, max_time=30)
        results.append(r)
        print(f"  Status:  {r['status']}")
        print(f"  Elapsed: {r['elapsed']:.2f}s")

    print("\n" + "=" * 70)
    print("Summary:")
    print("-" * 70)
    for r in results:
        print(f"  {r['strategy']:40s} | {r['elapsed']:6.2f}s | {r['status'][:30]}")
    print("=" * 70)

    # Recommend best strategy
    valid_strategies = [r for r in results if r['result']]
    if valid_strategies:
        best = min(valid_strategies, key=lambda r: r['elapsed'])
        print(f"\nBest performing valid strategy: {best['strategy']} ({best['elapsed']:.2f}s)")
        print(f"Recommended method: {best['method']}")
    else:
        print("\nNo strategy produced the expected result within the time limit.")
        print("Consider increasing max_time or adjusting N/M parameters.")


if __name__ == '__main__':
    main()
