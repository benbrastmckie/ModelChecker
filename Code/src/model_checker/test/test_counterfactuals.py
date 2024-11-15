"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)


########################################
##### COUNTERFACTUAL COUNTERMODELS #####
########################################

@pytest.mark.timeout(max_time)
def test_CF_CM1():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING
    N = 3
    premises = ['(A boxright C)']
    conclusions = ['((A wedge B) boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM2():
# MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    N = 3
    premises = ['(A circleright C)']
    conclusions = ['((A wedge B) circleright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM3():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    N = 3
    premises = ['(A boxright C)', 'Diamond (A wedge B)']
    conclusions = ['((A wedge B) boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM4():
# COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    N = 4
    premises = ['neg A', '(A boxright C)']
    conclusions = ['((A wedge B) boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM5():
# COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    N = 4
    premises = ['(A boxright C)','(B boxright C)']
    conclusions = ['((A wedge B) boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )


@pytest.mark.timeout(max_time)
def test_CF_CM6():
# COUNTERFACTUAL CONTRAPOSITION
    N = 3
    premises = ['(A boxright B)']
    conclusions = ['(neg B boxright neg A)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM7():
# COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    N = 4
    premises = ['neg B','(A boxright B)']
    conclusions = ['(neg B boxright neg A)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM8():
# COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    N = 4
    premises = ['neg A','neg B','(A boxright B)']
    conclusions = ['(neg B boxright neg A)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM9():
# TRANSITIVITY
    N = 3
    premises = ['(A boxright B)','(B boxright C)']
    conclusions = ['(A boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM10():
# COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    N = 4
    premises = ['neg A','(A boxright B)','(B boxright C)']
    conclusions = ['(A boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM11():
# COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    N = 4
    premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
    conclusions = ['(A boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM12():
# SOBEL SEQUENCE (N = 3)
    N = 3
    premises = [
        '(A boxright X)',
        'neg ((A wedge B) boxright X)',
        '(((A wedge B) wedge C) boxright X)',
    ]
    conclusions = []
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM13():
# SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
    N = 4
    premises = [
        'Diamond A',
        '(A boxright X)',
        'Diamond (A wedge B)',
        'neg ((A wedge B) boxright X)',
        'Diamond ((A wedge B) wedge C)',
        '(((A wedge B) wedge C) boxright X)',
        'Diamond (((A wedge B) wedge C) wedge D)',
    ]
    conclusions = []
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM14():
# COUNTERFACTUAL EXCLUDED MIDDLE
    N = 3
    premises = ['neg A']
    conclusions = ['(A boxright B)','(A boxright neg B)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM15():
# SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    N = 3
    premises = ['neg A','(A boxright (B vee C))']
    conclusions = ['(A boxright B)','(A boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM16():
# INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    N = 4
    premises = ['(A boxright C)','(B boxright C)']
    conclusions = ['((A vee B) boxright C)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM17():
# MUST FACTIVITY
    N = 3
    premises = ['A', 'B']
    conclusions = ['(A boxright B)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM18():
# COUNTERFACTUAL EXPORTATION
    N = 3
    premises = ['((A wedge B) boxright C)']
    conclusions = ['(A boxright (B boxright C))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM19():
# COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    N = 3
    premises = ['((A wedge B) boxright C)','Diamond (A wedge B)']
    conclusions = ['(A boxright (B boxright C))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF_CM20():
# COUNTERFACTUAL EXCLUDED MIDDLE VARIANT
    N = 3
    premises = ['neg A','neg (A boxright B)']
    conclusions = ['(A boxright neg B)']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

# # NOTE: DOES NOT FIND COUNTERMODEL
# @pytest.mark.timeout(0)
# def test_CL_8():
#     N = 4
#     premises = ['(A \\boxright (B \\boxright C))']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     desired_model_status = True
#     contingent_bool = True
#     disjoint_bool = False
#     check_model_status(
#         N,
#         premises,
#         conclusions,
#         desired_model_status,
#         contingent_bool,
#         disjoint_bool
#     )





################################
##### COUNTERFACTUAL LOGIC #####
################################

@pytest.mark.timeout(max_time)
def test_CF1():
    """COUNTERFACTUAL IDENTITY"""
    N = 3
    premises = []
    conclusions = ['(A boxright A)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF2():
    """COUNTERFACTUAL MODUS PONENS"""
    N = 3
    premises = ['A','(A boxright B)']
    conclusions = ['B']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF3():
    """WEAKENED TRANSITIVITY"""
    N = 3
    premises = ['(A boxright B)','((A wedge B) boxright C)']
    conclusions = ['(A boxright C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF4():
    """ANTECEDENT DISJUNCTION TO CONJUNCTION"""
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF5():
    """SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    N = 3
    premises = ['((A vee B) boxright C)']
    conclusions = ['(A boxright C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF6():
    """DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    N = 3
    premises = ['((A vee B) boxright C)']
    conclusions = ['((A boxright C) wedge (B boxright C))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF7():
    N = 3
    premises = ['(A boxright C)', '(B boxright C)', '((A wedge B) boxright C)']
    conclusions = ['((A vee B) boxright C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF8():
    N = 3
    premises = ['(A boxright (B wedge C))']
    conclusions = ['(A boxright B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF9():
    N = 3
    premises = ['(A boxright B)','(A boxright C)']
    conclusions = ['(A boxright (B wedge C))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CF10():
    """FACTIVITY MIGHT"""
    N = 3
    premises = ['A','B']
    conclusions = ['(A circleright B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )
