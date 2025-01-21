"""run 'pytest' from the '.../Code' directory"""
import pytest
from test.utils import (
    check_model_status,
    default_max_time,
)

from src.model_checker.syntactic import (
    OperatorCollection,
)

from src.model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionOperator,
    UniAndOperator,
    UniOrOperator,
)

semantics = ExclusionSemantics
proposition = UnilateralProposition
operators = OperatorCollection(
    ExclusionOperator,
    UniAndOperator,
    UniOrOperator,
)


max_time = default_max_time

###################################
##### EXCLUSION COUNTERMODELS #####
###################################

@pytest.mark.timeout(max_time)
def test_CMP_CM1():
    """DISTRIBUTION AND/OR"""
    premises = ['((A \\univee B) \\uniwedge (A \\univee B))']
    conclusions = ['(A \\uniwedge (B \\univee C))']
    settings = {
        'N' : 3,
        'contingent' : True,
        'possible' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'fusion_closure' : False,
        'print_impossible' : True,
        'desired_status' : True,
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



###########################
##### EXCLUSION LOGIC #####
###########################

@pytest.mark.timeout(max_time)
def test_CMP_T1():
    """DE MORGAN NOT/OR"""
    premises = ['\\exclude (A \\univee B)']
    conclusions = ['(\\exclude A \\uniwedge \\exclude B)']
    settings = {
        'N' : 3,
        'contingent' : True,
        'possible' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'fusion_closure' : False,
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

# @pytest.mark.timeout(max_time)
def test_IMP_T2():
    """DE MORGAN NOT/AND"""
    premises = ['(A \\uniwedge (B \\univee C))']
    conclusions = ['((A \\univee B) \\uniwedge (A \\univee B))']
    settings = {
        'N' : 3,
        'contingent' : True,
        'possible' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
        'fusion_closure' : False,
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

