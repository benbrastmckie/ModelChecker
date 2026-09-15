from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure
def S(N=3, expectation=True, max_time=60):
    return {'N': N, 'contingent': True, 'non_null': True, 'non_empty': True, 'disjoint': False,
            'max_time': max_time, 'iterate': 1, 'expectation': expectation, 'solver': 'z3'}
X = "(A \\boxrightILMC B)"
ex = {}
# Weakened transitivity, atomic antecedent, base and ILMC clauses
ex["T1_WT_ATOMIC_SQ"]   = [["(A \\boxright C)", "((A \\wedge C) \\boxright D)"], ["(A \\boxright D)"], S(3, False)]
ex["T2_WT_ATOMIC_ILMC"] = [["(A \\boxrightILMC C)", "((A \\wedge C) \\boxrightILMC D)"], ["(A \\boxrightILMC D)"], S(3, False)]
# Weakened transitivity at a nested counterfactual antecedent X = A []-> B
ex["T3_WT_NESTED_ILMC"] = [[f"({X} \\boxrightILMC C)", f"(({X} \\wedge C) \\boxrightILMC D)"], [f"({X} \\boxrightILMC D)"], S(3, False)]
ex["T4_WT_NESTED_ILMC_N4"] = [[f"({X} \\boxrightILMC C)", f"(({X} \\wedge C) \\boxrightILMC D)"], [f"({X} \\boxrightILMC D)"], S(4, False, 120)]
# Settled core is independent of which necessary antecedent supplies the null verifier
ex["T5_CORE_INDEPENDENT"] = [["(A \\leq B)", "(D \\sqsubseteq E)"], ["(((A \\leq B) \\boxrightILMC C) \\equiv ((D \\sqsubseteq E) \\boxrightILMC C))"], S(3, False)]
ex["T6_CORE_VIA_TOP_TOP"] = [["(A \\leq B)"], ["(((A \\leq B) \\boxrightILMC C) \\equiv ((\\top \\boxrightILMC \\top) \\boxrightILMC C))"], S(3, False)]
general_settings = {"print_constraints": False, "print_impossible": True, "print_z3": False, "save_output": False, "maximize": False}
reg = LogosOperatorRegistry(); reg.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual'])
semantic_theories = {"Brast-McKie": {"semantics": LogosSemantics, "proposition": LogosProposition, "model": LogosModelStructure, "operators": reg.get_operators()}}
example_range = ex
