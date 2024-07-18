"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)




### INVALID ###

@pytest.mark.timeout(max_time)
def test_ML_CM1():
    """ NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS """
    N = 3
    premises = ['Box A','(A rightarrow B)']
    conclusions = ['Box B']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML_CM2():
    """ COUNTERFACTUAL IMPLIES STRICT CONDITIONAL """
    N = 3
    premises = ['(A boxright B)']
    conclusions = ['Box (A rightarrow B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)






### VALID ###

@pytest.mark.timeout(max_time)
def test_ML1():
    N = 3
    premises = ['Box (A rightarrow B)']
    conclusions = ['(A boxright B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML2():
    # K AXIOM (BOX)
    N = 3
    premises = ['Box (A rightarrow B)']
    conclusions = ['(Box A rightarrow Box B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML3():
    # K AXIOM (TOP)
    N = 3
    premises = ['(top boxright (A rightarrow B))']
    conclusions = ['((top boxright A) rightarrow (top boxright B))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML4():
    # T AXIOM (TOP)
    N = 3
    premises = ['(top boxright A)']
    conclusions = ['A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML5():
    # T AXIOM (BOX)
    N = 3
    premises = ['Box A']
    conclusions = ['A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML6():
    # T AXIOM (BOX)
    N = 3
    premises = ['Box A']
    conclusions = ['A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML7():
    # 4 AXIOM (TOP)
    N = 3
    premises = ['(top boxright A)']
    conclusions = ['(top boxright (top boxright A))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML8():
    # 4 AXIOM (BOX)
    N = 3
    premises = ['Box A']
    conclusions = ['Box Box A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML9():
    # B AXIOM (TOP)
    # NOTE: with Z3 quantifiers MIT ran for 1600 seconds; now .0328 seconds locally
    N = 3
    premises = ['A']
    conclusions = ['(top boxright neg (top boxright neg A))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML10():
    # B AXIOM (BOX)
    N = 3
    premises = ['A']
    conclusions = ['Box Diamond A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML11():
    # 5 AXIOM (TOP)
    # SLOW: 12.9 seconds locally
    N = 3
    premises = ['(top boxright A)']
    conclusions = ['(top boxright neg (top boxright neg A))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML12():
    # 5 AXIOM (BOX)
    N = 3
    premises = ['Box A']
    conclusions = ['Box Diamond A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML13():
    # BOX-TO-TOP EQUIVALENCE
    N = 3
    premises = ['Box A']
    conclusions = ['(top boxright A)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML14():
    # # TOP-TO-BOX EQUIVALENCE
    N = 3
    premises = ['(top boxright A)']
    conclusions = ['Box A']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(max_time)
def test_ML15():
    # NECESSARY EQUIVALENCE
    N = 3
    premises = []
    conclusions = ['Box ((A vee neg A) leftrightarrow (B vee neg B))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)
