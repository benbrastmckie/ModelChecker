"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)


########################################
##### IMPOSITION COUNTERMODELS #####
########################################

@pytest.mark.timeout(max_time)
def test_IMP_CM1():
# IMPOSITION ANTECEDENT STRENGTHENING
    N = 3
    premises = ['(A imposition C)']
    conclusions = ['((A wedge B) imposition C)']
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
def test_IMP_CM2():
# IMPOSITION ANTECEDENT STRENGTHENING WITH POSSIBILITY
    N = 3
    premises = ['(A imposition C)', 'Diamond (A wedge B)']
    conclusions = ['((A wedge B) imposition C)']
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
def test_IMP_CM3():
# IMPOSITION ANTECEDENT STRENGTHENING WITH NEGATION
    N = 4
    premises = ['neg A', '(A imposition C)']
    conclusions = ['((A wedge B) imposition C)']
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
def test_IMP_CM4():
# IMPOSITION DOUBLE ANTECEDENT STRENGTHENING
    N = 4
    premises = ['(A imposition C)','(B imposition C)']
    conclusions = ['((A wedge B) imposition C)']
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
def test_IMP_CM5():
# IMPOSITION CONTRAPOSITION
    N = 3
    premises = ['(A imposition B)']
    conclusions = ['(neg B imposition neg A)']
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
def test_IMP_CM6():
# IMPOSITION CONTRAPOSITION WITH NEGATION
    N = 4
    premises = ['neg B','(A imposition B)']
    conclusions = ['(neg B imposition neg A)']
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
def test_IMP_CM7():
# IMPOSITION CONTRAPOSITION WITH TWO NEGATIONS
    N = 4
    premises = ['neg A','neg B','(A imposition B)']
    conclusions = ['(neg B imposition neg A)']
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
def test_IMP_CM8():
# TRANSITIVITY
    N = 3
    premises = ['(A imposition B)','(B imposition C)']
    conclusions = ['(A imposition C)']
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
def test_IMP_CM9():
# IMPOSITION TRANSITIVITY WITH NEGATION
    N = 4
    premises = ['neg A','(A imposition B)','(B imposition C)']
    conclusions = ['(A imposition C)']
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
def test_IMP_CM10():
# IMPOSITION TRANSITIVITY WITH TWO NEGATIONS
    N = 4
    premises = ['neg A','neg B','(A imposition B)','(B imposition C)']
    conclusions = ['(A imposition C)']
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
def test_IMP_CM11():
# SOBEL SEQUENCE (N = 3)
    N = 3
    premises = [
        '(A imposition X)',
        'neg ((A wedge B) imposition X)',
        '(((A wedge B) wedge C) imposition X)',
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
def test_IMP_CM12():
# SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
    N = 4
    premises = [
        'Diamond A',
        '(A imposition X)',
        'Diamond (A wedge B)',
        'neg ((A wedge B) imposition X)',
        'Diamond ((A wedge B) wedge C)',
        '(((A wedge B) wedge C) imposition X)',
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
def test_IMP_CM13():
# IMPOSITION EXCLUDED MIDDLE
    N = 3
    premises = ['neg A']
    conclusions = ['(A imposition B)','(A imposition neg B)']
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
def test_IMP_CM14():
# SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    N = 3
    premises = ['neg A','(A imposition (B vee C))']
    conclusions = ['(A imposition B)','(A imposition C)']
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
def test_IMP_CM15():
# INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    N = 4
    premises = ['(A imposition C)','(B imposition C)']
    conclusions = ['((A vee B) imposition C)']
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
def test_IMP_CM16():
# MUST FACTIVITY
    N = 3
    premises = ['A', 'B']
    conclusions = ['(A imposition B)']
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
def test_IMP_CM17():
# IMPOSITION EXPORTATION
    N = 3
    premises = ['((A wedge B) imposition C)']
    conclusions = ['(A imposition (B imposition C))']
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
def test_IMP_CM18():
# IMPOSITION EXPORTATION WITH POSSIBILITY
    N = 3
    premises = ['((A wedge B) imposition C)','Diamond (A wedge B)']
    conclusions = ['(A imposition (B imposition C))']
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
def test_IMP_CM19():
# IMPOSITION EXCLUDED MIDDLE VARIANT
    N = 3
    premises = ['neg A','neg (A imposition B)']
    conclusions = ['(A imposition neg B)']
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
#     premises = ['(A \\imposition (B \\imposition C))']
#     conclusions = ['((A \\wedge B) \\imposition C)']
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
##### IMPOSITION LOGIC #####
################################

@pytest.mark.timeout(max_time)
def test_IMP1():
    """IMPOSITION IDENTITY"""
    N = 3
    premises = []
    conclusions = ['(A imposition A)']
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
def test_IMP2():
    """IMPOSITION MODUS PONENS"""
    N = 3
    premises = ['A','(A imposition B)']
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
def test_IMP3():
    """WEAKENED TRANSITIVITY"""
    N = 3
    premises = ['(A imposition B)','((A wedge B) imposition C)']
    conclusions = ['(A imposition C)']
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
def test_IMP4():
    """ANTECEDENT DISJUNCTION TO CONJUNCTION"""
    N = 3
    premises = ['((A \\vee B) \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP5():
    """SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    N = 3
    premises = ['((A vee B) imposition C)']
    conclusions = ['(A imposition C)']
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
def test_IMP6():
    """DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    N = 3
    premises = ['((A vee B) imposition C)']
    conclusions = ['((A imposition C) wedge (B imposition C))']
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
def test_IMP7():
    N = 3
    premises = ['(A imposition C)', '(B imposition C)', '((A wedge B) imposition C)']
    conclusions = ['((A vee B) imposition C)']
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
def test_IMP8():
    N = 3
    premises = ['(A imposition (B wedge C))']
    conclusions = ['(A imposition B)']
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
def test_IMP9():
    N = 3
    premises = ['(A imposition B)','(A imposition C)']
    conclusions = ['(A imposition (B wedge C))']
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
