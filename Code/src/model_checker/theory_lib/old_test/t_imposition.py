"""run 'pytest' from the '.../Code/src/model_checker/' directory"""
import pytest

from test.utils import (
    check_model_status,
    default_max_time,
)

from src.model_checker.syntactic import (
    OperatorCollection,
)

from src.model_checker.semantic import (
    Proposition,
    ImpositionSemantics,
)

from src.model_checker.defined import (
    NegationOperator,
    AndOperator,
    OrOperator,
    ImpositionOperator,
    PossibilityOperator,
    NecessityOperator,
    MightImpositionOperator,
)

semantics = ImpositionSemantics
proposition = Proposition
operators = OperatorCollection(
    NegationOperator,
    AndOperator,
    OrOperator,
    ImpositionOperator,
    MightImpositionOperator,
    NecessityOperator,
    PossibilityOperator,
)

max_time = default_max_time

########################################
##### IMPOSITION COUNTERMODELS #####
########################################

@pytest.mark.timeout(max_time)
def test_IMP_CM1():
# IMPOSITION ANTECEDENT STRENGTHENING
    premises = ['(A \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_CM2():
# MIGHT IMPOSITION ANTECEDENT STRENGTHENING
    premises = ['(A \\could C)']
    conclusions = ['((A \\wedge B) \\could C)']
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
def test_IMP_CM3():
# IMPOSITION ANTECEDENT STRENGTHENING WITH POSSIBILITY
    premises = ['(A \\imposition C)', '\\Diamond (A \\wedge B)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_CM4():
# IMPOSITION ANTECEDENT STRENGTHENING WITH NEGATION
    premises = ['\\neg A', '(A \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_CM5():
# IMPOSITION DOUBLE ANTECEDENT STRENGTHENING
    premises = ['(A \\imposition C)','(B \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_CM6():
# WEAKENED MONOTONICITY
    premises = ['(A \\imposition B)','(A \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_CM7():
# IMPOSITION CONTRAPOSITION
    premises = ['(A \\imposition B)']
    conclusions = ['(\\neg B \\imposition \\neg A)']
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
def test_IMP_CM8():
# IMPOSITION CONTRAPOSITION WITH NEGATION
    premises = ['\\neg B','(A \\imposition B)']
    conclusions = ['(\\neg B \\imposition \\neg A)']
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
def test_IMP_CM9():
# IMPOSITION CONTRAPOSITION WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\imposition B)']
    conclusions = ['(\\neg B \\imposition \\neg A)']
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
def test_IMP_CM10():
# TRANSITIVITY
    premises = ['(A \\imposition B)','(B \\imposition C)']
    conclusions = ['(A \\imposition C)']
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
def test_IMP_CM11():
# IMPOSITION TRANSITIVITY WITH NEGATION
    premises = ['\\neg A','(A \\imposition B)','(B \\imposition C)']
    conclusions = ['(A \\imposition C)']
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
def test_IMP_CM12():
# IMPOSITION TRANSITIVITY WITH TWO NEGATIONS
    premises = ['\\neg A','\\neg B','(A \\imposition B)','(B \\imposition C)']
    conclusions = ['(A \\imposition C)']
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
def test_IMP_CM13():
# SOBEL SEQUENCE (N = 3)
    premises = [
        '(A \\imposition X)',
        '\\neg ((A \\wedge B) \\imposition X)',
        '(((A \\wedge B) \\wedge C) \\imposition X)',
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
def test_IMP_CM14():
# SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
    premises = [
        '\\Diamond A',
        '(A \\imposition X)',
        '\\Diamond (A \\wedge B)',
        '\\neg ((A \\wedge B) \\imposition X)',
        '\\Diamond ((A \\wedge B) \\wedge C)',
        '(((A \\wedge B) \\wedge C) \\imposition X)',
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
def test_IMP_CM15():
# IMPOSITION EXCLUDED MIDDLE
    premises = ['\\neg A']
    conclusions = ['(A \\imposition B)','(A \\imposition \\neg B)']
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
def test_IMP_CM16():
# SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    premises = ['\\neg A','(A \\imposition (B \\vee C))']
    conclusions = ['(A \\imposition B)','(A \\imposition C)']
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
def test_IMP_CM17():
# INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    premises = ['(A \\imposition C)','(B \\imposition C)']
    conclusions = ['((A \\vee B) \\imposition C)']
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
def test_IMP_CM18():
# MUST FACTIVITY
    premises = ['A', 'B']
    conclusions = ['(A \\imposition B)']
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
def test_IMP_CM19():
# IMPOSITION EXPORTATION
    premises = ['((A \\wedge B) \\imposition C)']
    conclusions = ['(A \\imposition (B \\imposition C))']
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
def test_IMP_CM20():
# IMPOSITION EXPORTATION WITH POSSIBILITY
    premises = ['((A \\wedge B) \\imposition C)','\\Diamond (A \\wedge B)']
    conclusions = ['(A \\imposition (B \\imposition C))']
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
def test_IMP_CM21():
# IMPOSITION EXCLUDED MIDDLE VARIANT
    premises = ['\\neg A','\\neg (A \\imposition B)']
    conclusions = ['(A \\imposition \\neg B)']
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
# def test_CL_8():
#     premises = ['(A \\imposition (B \\imposition C))']
#     conclusions = ['((A \\wedge B) \\imposition C)']
#     settings = {
#         'N' : 4,
#         'contingent' : True,
#         'non_null' : True,
#         'non_empty' : True,
#         'disjoint' : False,
#         'desired_status' : True,
#         'print_impossible' : True,
#         'max_time' : max_time,
#     }
#     check_model_status(
#         premises,
#         conclusions,
#         semantics,
#         proposition,
#         operators,
#         settings,
#     )





################################
##### IMPOSITION LOGIC #####
################################

@pytest.mark.timeout(max_time)
def test_IMP_T1():
    """IMPOSITION IDENTITY"""
    premises = []
    conclusions = ['(A \\imposition A)']
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
def test_IMP_T2():
    """IMPOSITION MODUS PONENS"""
    premises = ['A','(A \\imposition B)']
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
def test_IMP_T3():
    """WEAKENED TRANSITIVITY"""
    premises = ['(A \\imposition B)','((A \\wedge B) \\imposition C)']
    conclusions = ['(A \\imposition C)']
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
def test_IMP_T4():
    """ANTECEDENT DISJUNCTION TO CONJUNCTION"""
    premises = ['((A \\vee B) \\imposition C)']
    conclusions = ['((A \\wedge B) \\imposition C)']
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
def test_IMP_T5():
    """SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\imposition C)']
    conclusions = ['(A \\imposition C)']
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
def test_IMP_T6():
    """DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT"""
    premises = ['((A \\vee B) \\imposition C)']
    conclusions = ['((A \\imposition C) \\wedge (B \\imposition C))']
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
def test_IMP_T7():
    premises = ['(A \\imposition C)', '(B \\imposition C)', '((A \\wedge B) \\imposition C)']
    conclusions = ['((A \\vee B) \\imposition C)']
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
def test_IMP_T8():
    premises = ['(A \\imposition (B \\wedge C))']
    conclusions = ['(A \\imposition B)']
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
def test_IMP_T9():
    premises = ['(A \\imposition B)','(A \\imposition C)']
    conclusions = ['(A \\imposition (B \\wedge C))']
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
def test_IMP_T10():
    """FACTIVITY MIGHT"""
    premises = ['A','B']
    conclusions = ['(A \\could B)']
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
