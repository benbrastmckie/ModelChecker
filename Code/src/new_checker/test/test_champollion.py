"""run 'pytest' from the '.../Code/src/new_checker/' directory"""
import pytest

from .utils import (
    check_model_status,
    default_max_time,
)

from new_checker.champollion import (
    ChampollionSemantics,
    ChampollionProposition,
)

semantics = ChampollionSemantics
proposition = ChampollionProposition
max_time = default_max_time

########################################
##### IMPOSITION COUNTERMODELS #####
########################################

@pytest.mark.timeout(max_time)
def test_CMP_CM1():
    """DISTRIBUTION AND/OR"""
    premises = ['((A \\univee B) \\uniwedge (A \\univee B))']
    conclusions = ['(A \\uniwedge (B \\univee C))']
    N = 3
    contingent = True
    non_null = True
    disjoint = False
    desired_status = True
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )



###########################
##### EXCLUSION LOGIC #####
###########################

@pytest.mark.timeout(max_time)
def test_CMP_T1():
    """DE MORGAN NOT/OR"""
    premises = ['\\exclude (A \\univee B)']
    conclusions = ['(\\exclude A \\uniwedge \\exclude B)']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

@pytest.mark.timeout(max_time)
def test_IMP_T2():
    """DE MORGAN NOT/AND"""
    premises = ['(A \\uniwedge (B \\univee C))']
    conclusions = ['((A \\univee B) \\uniwedge (A \\univee B))']
    N = 3
    contingent = False
    non_null = True
    disjoint = False
    desired_status = False
    check_model_status(
        premises,
        conclusions,
        semantics,
        proposition,
        N,
        contingent,
        non_null,
        disjoint,
        max_time,
        desired_status,
    )

