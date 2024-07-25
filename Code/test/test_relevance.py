"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)

###################################
##### RELEVANCE COUNTERMODELS #####
###################################

@pytest.mark.timeout(max_time)
def test_RL_CM1():
    """ANTECEDENT STRENGTHENING"""
    N = 3
    premises = []
    conclusions = ['((A wedge B) preceq A)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM2():
    """ANTECEDENT WEAKENING"""
    N = 3
    premises = []
    conclusions = ['((A vee B) preceq A)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM3():
    """RELEVANCE TRANSITIVITY"""
    N = 3
    premises = ['(A preceq B)', '(B preceq C)']
    conclusions = ['(A preceq C)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM4():
    """RELEVANT IMPLICATION: GROUND"""
    N = 3
    premises = ['Box (A rightarrow B)','(A preceq B)']
    conclusions = ['(A leq B)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM5():
    """RELEVANT IMPLICATION: ESSENCE"""
    N = 3
    premises = ['Box (B rightarrow A)','(A preceq B)']
    conclusions = ['(A sqsubseteq B)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM6():
    """RELEVANT IMPLICATION: IDENTITY"""
    N = 3
    premises = ['Box (A leftrightarrow B)','(A preceq B)','(B preceq A)']
    conclusions = ['(A equiv B)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM7():
    """STRICT IMPLICATION"""
    N = 3
    premises = ['Box (A rightarrow B)']
    conclusions = ['(A preceq B)']
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

@pytest.mark.timeout(max_time)
def test_RL_CM8():
    """REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(((A vee B) wedge (A vee C)) preceq (A vee (B wedge C)))']
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

@pytest.mark.timeout(max_time)
def test_RL_CM9():
    """REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(((A wedge B) vee (A wedge C)) preceq (A wedge (B vee C)))']
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

@pytest.mark.timeout(max_time)
def test_RL_CM10():
    """CONJUNCTION INTRODUCTION"""
    N = 3
    premises = ['(A preceq B)']
    conclusions = ['(A preceq (B wedge C))']
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

@pytest.mark.timeout(max_time)
def test_RL_CM11():
    """DISJUNCTION INTRODUCTION"""
    N = 3
    premises = ['(A preceq B)']
    conclusions = ['(A preceq (B vee C))']
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






###########################
##### RELEVANCE LOGIC #####
###########################

### DEFINITIONAL EQUIVALENTS

@pytest.mark.timeout(max_time)
def test_RL1():
    """RELEVANCE TO CONJUNCTION"""
    N = 3
    premises = ['(A preceq B)']
    conclusions = ['((A wedge B) leq B)']
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
def test_RL2():
    """RELEVANCE TO DISJUNCTION"""
    N = 3
    premises = ['(A preceq B)']
    conclusions = ['((A vee B) sqsubseteq B)']
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
def test_RL3():
    """CONJUNCTION TO RELEVANCE"""
    N = 3
    premises = ['((A wedge B) leq B)']
    conclusions = ['(A preceq B)']
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
def test_RL4():
    """DISJUNCTION TO RELEVANCE"""
    N = 3
    premises = ['((A vee B) sqsubseteq B)']
    conclusions = ['(A preceq B)']
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



### AXIOMS

@pytest.mark.timeout(max_time)
def test_RL5():
    """CONJUNCTION INTRODUCTION"""
    N = 3
    premises = []
    conclusions = ['(A preceq (A wedge B))']
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
def test_RL6():
    """DISJUNCTION INTRODUCTION"""
    N = 3
    premises = []
    conclusions = ['(A preceq (A vee B))']
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




### CONSTITUTIVE INTERACTION

@pytest.mark.timeout(max_time)
def test_RL7():
    """GROUNDING RELEVANCE"""
    N = 3
    premises = ['(A leq B)']
    conclusions = ['(A preceq B)']
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
def test_RL8():
    """ESSENCE RELEVANCE"""
    N = 3
    premises = ['(A sqsubseteq B)']
    conclusions = ['(A preceq B)']
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
def test_RL9():
    """IDENTITY RELEVANCE"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['(A preceq B)']
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
