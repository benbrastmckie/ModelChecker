"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)

#####################################
##### EXTENSIONAL COUNTERMODELS #####
#####################################

@pytest.mark.timeout(max_time)
def test_EXT_CM1():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool)






#############################
##### EXTENSIONAL LOGIC #####
#############################

@pytest.mark.timeout(max_time)
def test_EXT1():
    N = 3
    premises = ['A','(A rightarrow B)']
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
        disjoint_bool)

@pytest.mark.timeout(max_time)
def test_EXT2():
    N = 3
    premises = []
    conclusions = ['(A rightarrow (B rightarrow A))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool)

@pytest.mark.timeout(max_time)
def test_EXT3():
    N = 3
    premises = []
    conclusions = ['((A rightarrow (B rightarrow C)) rightarrow ((A rightarrow B) rightarrow (A rightarrow C)))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool)

@pytest.mark.timeout(max_time)
def test_EXT4():
    N = 3
    premises = []
    conclusions = ['((neg A rightarrow neg B) rightarrow (B rightarrow A))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool)
