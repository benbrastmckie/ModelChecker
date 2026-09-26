"""Experiments on uniformity between the null-state clauses and ILMC."""
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure

def S(N=3, expectation=True, max_time=30):
    return {'N': N, 'contingent': True, 'non_null': True, 'non_empty': True,
            'disjoint': False, 'max_time': max_time, 'iterate': 1,
            'expectation': expectation, 'solver': 'z3'}

ex = {}
# 1. Is Box A the same proposition as (top boxrightILMC A)?  expect: theorem (no countermodel)
ex["U1_BOX_EQ_TOP_ILMC"] = [[], ["(\\Box A \\equiv (\\top \\boxrightILMC A))"], S(3, False)]
# 2. Same with the status-quo counterfactual.  expect: countermodel ({w} vs {null})
ex["U2_BOX_EQ_TOP_SQ"] = [[], ["(\\Box A \\equiv (\\top \\boxright A))"], S(3, True)]
# 3. All true necessities are one proposition.  expect: theorem
ex["U3_BOX_COLLAPSE"] = [["\\Box A", "\\Box B"], ["(\\Box A \\equiv \\Box B)"], S(3, False)]
# 4. All true constitutive claims are one proposition.  expect: theorem
ex["U4_CONST_COLLAPSE"] = [["(A \\leq B)", "(C \\sqsubseteq D)"], ["((A \\leq B) \\equiv (C \\sqsubseteq D))"], S(3, False)]
# 5. A true constitutive antecedent is centered under ILMC.  expect: theorem
ex["U5_CONST_ANTE_CENTERED"] = [["(A \\leq B)"], ["\\Box (((A \\leq B) \\boxrightILMC C) \\leftrightarrow C)"], S(3, False)]
# 6. ...but the proposition is the settler core of C, not C itself.  expect: countermodel
ex["U6_CONST_ANTE_NOT_C"] = [["(A \\leq B)"], ["(((A \\leq B) \\boxrightILMC C) \\equiv C)"], S(3, True)]
# 7. Same under the status quo.  expect: countermodel
ex["U7_CONST_ANTE_NOT_C_SQ"] = [["(A \\leq B)"], ["(((A \\leq B) \\boxright C) \\equiv C)"], S(3, True)]
# 8. Counterpossibles are one proposition under ILMC.  expect: theorem
ex["U8_BOT_ANTE_COLLAPSE"] = [[], ["((\\bot \\boxrightILMC A) \\equiv (\\bot \\boxrightILMC B))"], S(3, False)]
# 9. Two true necessities via ILMC are one proposition.  expect: theorem
ex["U9_TOP_ILMC_COLLAPSE"] = [["\\Box A", "\\Box B"], ["((\\top \\boxrightILMC A) \\equiv (\\top \\boxrightILMC B))"], S(3, False)]
# 10. Box via ILMC and via the modal clause agree in truth (sanity).  expect: theorem
ex["U10_BOX_TRUTH_AGREE"] = [[], ["\\Box (\\Box A \\leftrightarrow (\\top \\boxrightILMC A))"], S(3, False)]

general_settings = {"print_constraints": False, "print_impossible": True,
                    "print_z3": False, "save_output": False, "maximize": False}
reg = LogosOperatorRegistry()
reg.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual'])
semantic_theories = {"Brast-McKie": {"semantics": LogosSemantics, "proposition": LogosProposition,
                                     "model": LogosModelStructure, "operators": reg.get_operators()}}
example_range = ex
# 11/12. Is the settled core of C ground- or essence-related to C?  expect: countermodels
ex["U11_CORE_GROUNDS_C"] = [["(A \\leq B)"], ["(((A \\leq B) \\boxrightILMC C) \\leq C)"], S(3, True)]
ex["U12_C_GROUNDS_CORE"] = [["(A \\leq B)"], ["(C \\leq ((A \\leq B) \\boxrightILMC C))"], S(3, True)]
ex["U13_CORE_ESSENCE_C"] = [["(A \\leq B)"], ["(((A \\leq B) \\boxrightILMC C) \\sqsubseteq C)"], S(3, True)]
