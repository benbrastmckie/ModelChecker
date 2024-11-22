"""run 'pytest' from the '.../new_checker' directory"""
import pytest
from .utils import (
    check_model_status,
    default_max_time,
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
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM2():
# MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    premises = ['(A \\circleright C)']
    conclusions = ['((A \\wedge B) \\circleright C)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM3():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    premises = ['(A \\boxright C)', '\\possible (A \\wedge B)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM4():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    premises = ['\\neg A', '(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM5():
# COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    premises = ['(A \\boxright C)','(B \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )


@pytest.mark.timeout(max_time)
def test_CF_CM6():
# COUNTERFACTUAL CONTRAPOSITION
    premises = ['(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM7():
# COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    premises = ['\\neg B','(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM8():
# COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM9():
# TRANSITIVITY
    premises = ['(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM10():
# COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    premises = ['\\neg A','(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM11():
# COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM12():
# SOBEL SEQUENCE (N = 3)
    premises = [
        '(A \\boxright X)',
        '\\neg ((A \\wedge B) \\boxright X)',
        '(((A \\wedge B) \\wedge C) \\boxright X)',
    ]
    conclusions = []
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(3)
def test_CF_CM13():
# SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
    premises = [
        '\\possible A',
        '(A \\boxright X)',
        '\\possible (A \\wedge B)',
        '\\neg ((A \\wedge B) \\boxright X)',
        '\\possible ((A \\wedge B) \\wedge C)',
        '(((A \\wedge B) \\wedge C) \\boxright X)',
        '\\possible (((A \\wedge B) \\wedge C) \\wedge D)',
    ]
    conclusions = []
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM14():
# COUNTERFACTUAL EXCLUDED MIDDLE
    premises = ['\\neg A']
    conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM15():
# SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    premises = ['\\neg A','(A \\boxright (B \\vee C))']
    conclusions = ['(A \\boxright B)','(A \\boxright C)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM16():
# INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    premises = ['(A \\boxright C)','(B \\boxright C)']
    conclusions = ['((A \\vee B) \\boxright C)']
    N = 4
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM17():
# MUST FACTIVITY
    premises = ['A', 'B']
    conclusions = ['(A \\boxright B)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM18():
# COUNTERFACTUAL EXPORTATION
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM19():
# COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    premises = ['((A \\wedge B) \\boxright C)','\\possible2 (A \\wedge B)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF_CM20():
# COUNTERFACTUAL EXCLUDED MIDDLE VARIANT
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

# # NOTE: DOES NOT FIND COUNTERMODEL
# @pytest.mark.timeout(max_time)
# def test_CL_8():
#     premises = ['(A \\boxright (B \\boxright C))']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     N = 4
#     contingent = True
#     non_null = True
#     disjoint = False
#     desired_status = True
#     check_model_status(
#         premises,
#         conclusions,
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
def test_CF1():
    """COUNTERFACTUAL IDENTITY"""
    premises = []
    conclusions = ['(A \\boxright A)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF2():
    """COUNTERFACTUAL MODUS PONENS"""
    premises = ['A','(A \\boxright B)']
    conclusions = ['B']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF3():
    """WEAKENED TRANSITIVITY"""
    premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF4():
    """ANTECEDENT DISJUNCTION TO CONJUNCTION"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF5():
    """SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF6():
    """DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\boxright C) \\wedge (B \\boxright C))']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF7():
    premises = ['(A \\boxright C)', '(B \\boxright C)', '((A \\wedge B) \\boxright C)']
    conclusions = ['((A \\vee B) \\boxright C)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF8():
    premises = ['(A \\boxright (B \\wedge C))']
    conclusions = ['(A \\boxright B)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_CF9():
    premises = ['(A \\boxright B)','(A \\boxright C)']
    conclusions = ['(A \\boxright (B \\wedge C))']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

# @pytest.mark.timeout(max_time)
# def test_CF10():
#     """FACTIVITY MIGHT"""
#     premises = ['A','B']
#     conclusions = ['(A \\circleright B)']
#     N = 3
#     contingent = False
#     non_null = True
#     disjoint = False
#     desired_status = False
#     check_model_status(
#         premises,
#         conclusions,
#         N,
#         contingent,
#         non_null,
#         disjoint,
#         max_time,
#         desired_status,
#     )
