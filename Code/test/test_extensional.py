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
    contingent = True
    check_model_status(premises, conclusions, desired_model_status, contingent, N)






#############################
##### EXTENSIONAL LOGIC #####
#############################

@pytest.mark.timeout(max_time)
def test_EXT1():
    N = 3
    premises = ['A','(A rightarrow B)']
    conclusions = ['B']
    desired_model_status = False
    contingent = False
    check_model_status(premises, conclusions, desired_model_status, contingent, N)

@pytest.mark.timeout(max_time)
def test_EXT2():
    N = 3
    premises = []
    conclusions = ['(A rightarrow (B rightarrow A))']
    desired_model_status = False
    contingent = False
    check_model_status(premises, conclusions, desired_model_status, contingent, N)

@pytest.mark.timeout(max_time)
def test_EXT3():
    N = 3
    premises = []
    conclusions = ['((A rightarrow (B rightarrow C)) rightarrow ((A rightarrow B) rightarrow (A rightarrow C)))']
    desired_model_status = False
    contingent = False
    check_model_status(premises, conclusions, desired_model_status, contingent, N)

@pytest.mark.timeout(max_time)
def test_EXT4():
    N = 3
    premises = []
    conclusions = ['((neg A rightarrow neg B) rightarrow (B rightarrow A))']
    desired_model_status = False
    contingent = False
    check_model_status(premises, conclusions, desired_model_status, contingent, N)
