"""run 'pytest' from the '.../Code/src/new_checker/' directory"""
import pytest
from .utils import (
    check_model_status,
    default_max_time,
)

from new_checker.semantic import Proposition, Semantics

semantics = Semantics
proposition = Proposition
max_time = default_max_time

#####################################
##### EXTENSIONAL COUNTERMODELS #####
#####################################

@pytest.mark.timeout(max_time)
def test_EXT_CM1():
    N = 3
    premises = ['A']
    conclusions = ['\\neg A']
    desired_status = True
    contingent = True
    non_null = True
    disjoint = False
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






#############################
##### EXTENSIONAL LOGIC #####
#############################

@pytest.mark.timeout(max_time)
def test_EXT1():
    N = 3
    premises = ['A','(A \\rightarrow B)']
    conclusions = ['B']
    desired_status = False
    contingent = False
    non_null = True
    disjoint = False
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
def test_EXT2():
    N = 3
    premises = []
    conclusions = ['(A \\rightarrow (B \\rightarrow A))']
    desired_status = False
    contingent = False
    non_null = True
    disjoint = False
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
def test_EXT3():
    N = 3
    premises = []
    conclusions = ['((A \\rightarrow (B \\rightarrow C)) \\rightarrow ((A \\rightarrow B) \\rightarrow (A \\rightarrow C)))']
    desired_status = False
    contingent = False
    non_null = True
    disjoint = False
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
def test_EXT4():
    N = 3
    premises = []
    conclusions = ['((\\neg A \\rightarrow \\neg B) \\rightarrow (B \\rightarrow A))']
    desired_status = False
    contingent = False
    non_null = True
    disjoint = False
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
