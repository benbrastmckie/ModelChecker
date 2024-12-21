"""run 'pytest' from the '.../Code/src/new_checker/' directory"""
import pytest
from .utils import (
    check_model_status,
    default_max_time,
)

from new_checker.syntactic import (
    OperatorCollection,
)

from new_checker.semantic import (
    Proposition,
    Semantics,
)

from new_checker.defined import (
    NegationOperator,
    AndOperator,
    OrOperator,
    CounterfactualOperator,
    PossibilityOperator,
    NecessityOperator,
    MightCounterfactualOperator,
)

semantics = Semantics
proposition = Proposition
operators = OperatorCollection(
    NegationOperator,
    AndOperator,
    OrOperator,
    CounterfactualOperator,
    MightCounterfactualOperator,
    NecessityOperator,
    PossibilityOperator,
)

max_time = default_max_time

########################################
##### COUNTERFACTUAL COUNTERMODELS #####
########################################

@pytest.mark.timeout(max_time)
def test_CF_CM1():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM2():
# MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    premises = ['(A \\circleright C)']
    conclusions = ['((A \\wedge B) \\circleright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM3():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    premises = ['(A \\boxright C)', '\\Diamond (A \\wedge B)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM4():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    premises = ['\\neg A', '(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM5():
# COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    premises = ['(A \\boxright C)','(B \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM6():
# WEAKENED MONOTONICITY
    premises = ['(A \\boxright B)','(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )


@pytest.mark.timeout(max_time)
def test_CF_CM7():
# COUNTERFACTUAL CONTRAPOSITION
    premises = ['(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM8():
# COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    premises = ['\\neg B','(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM9():
# COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM10():
# TRANSITIVITY
    premises = ['(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM11():
# COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM12():
# COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM13():
# SOBEL SEQUENCE (N = 3)
    premises = [
        '(A \\boxright X)',
        '\\neg ((A \\wedge B) \\boxright X)',
        '(((A \\wedge B) \\wedge C) \\boxright X)',
    ]
    conclusions = []
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM14():
# SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
    premises = [
        '\\Diamond A',
        '(A \\boxright X)',
        '\\Diamond (A \\wedge B)',
        '\\neg ((A \\wedge B) \\boxright X)',
        '\\Diamond ((A \\wedge B) \\wedge C)',
        '(((A \\wedge B) \\wedge C) \\boxright X)',
        '\\Diamond (((A \\wedge B) \\wedge C) \\wedge D)',
    ]
    conclusions = []
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM15():
# COUNTERFACTUAL EXCLUDED MIDDLE
    premises = ['\\neg A']
    conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM16():
# SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    premises = ['\\neg A','(A \\boxright (B \\vee C))']
    conclusions = ['(A \\boxright B)','(A \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM17():
# INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    premises = ['(A \\boxright C)','(B \\boxright C)']
    conclusions = ['((A \\vee B) \\boxright C)']
    settings = {
        'N' : 4,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM18():
# MUST FACTIVITY
    premises = ['A', 'B']
    conclusions = ['(A \\boxright B)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM19():
# COUNTERFACTUAL EXPORTATION
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM20():
# COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    premises = ['((A \\wedge B) \\boxright C)','\\Diamond (A \\wedge B)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM21():
# COUNTERFACTUAL EXCLUDED MIDDLE VARIANT
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : True,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

# # NOTE: DOES NOT FIND COUNTERMODEL
# @pytest.mark.timeout(max_time)
# def test_CF_CM22():
#     premises = ['(A \\boxright (B \\boxright C))']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     N = 4
#     contingent = True
#     non_null = True
#     non_null = True
#     disjoint = False
#     desired_status = True
#     check_model_status(
#         premises,
#         conclusions,
#         semantics,
#         proposition,
#         N,
#         contingent,
#         non_null,
#         disjoint,
#         max_time,
#         desired_status,
#     )





################################
##### COUNTERFACTUAL LOGIC #####
################################

@pytest.mark.timeout(max_time)
def test_CF_T1():
    """COUNTERFACTUAL IDENTITY"""
    premises = []
    conclusions = ['(A \\boxright A)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T2():
    """COUNTERFACTUAL MODUS PONENS"""
    premises = ['A','(A \\boxright B)']
    conclusions = ['B']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T3():
    """WEAKENED TRANSITIVITY"""
    premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T4():
    """ANTECEDENT DISJUNCTION TO CONJUNCTION"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T5():
    """SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T6():
    """DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T7():
    premises = ['(A \\boxright C)', '(B \\boxright C)', '((A \\wedge B) \\boxright C)']
    conclusions = ['((A \\vee B) \\boxright C)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T8():
    premises = ['(A \\boxright (B \\wedge C))']
    conclusions = ['(A \\boxright B)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T9():
    premises = ['(A \\boxright B)','(A \\boxright C)']
    conclusions = ['(A \\boxright (B \\wedge C))']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )

@pytest.mark.timeout(max_time)
def test_CF_T10():
    """MIGHT FACTIVITY"""
    premises = ['A','B']
    conclusions = ['(A \\circleright B)']
    settings = {
        'N' : 3,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'desired_status' : False,
        'print_impossible' : True,
        'max_time' : max_time,
    }
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        operators,
        settings,
    )
