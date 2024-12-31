"""run 'pytest' from the '.../Code/' directory"""
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
    Semantics,
)

from src.model_checker.defined import (
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
    NecessityOperator,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
)

semantics = Semantics
proposition = Proposition
operators = OperatorCollection(
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
    NecessityOperator,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
)

max_time = default_max_time

###################################
##### RELEVANCE COUNTERMODELS #####
###################################

@pytest.mark.timeout(max_time)
def test_RL_CM1():
    """ANTECEDENT STRENGTHENING"""
    premises = []
    conclusions = ['((A \\wedge B) \\preceq A)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM2():
    """ANTECEDENT WEAKENING"""
    premises = []
    conclusions = ['((A \\vee B) \\preceq A)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM3():
    """RELEVANCE TRANSITIVITY"""
    premises = ['(A \\preceq B)', '(B \\preceq C)']
    conclusions = ['(A \\preceq C)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM4():
    """RELEVANT IMPLICATION: GROUND"""
    premises = ['\\Box (A \\rightarrow B)','(A \\preceq B)']
    conclusions = ['(A \\leq B)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM5():
    """RELEVANT IMPLICATION: ESSENCE"""
    premises = ['\\Box (B \\rightarrow A)','(A \\preceq B)']
    conclusions = ['(A \\sqsubseteq B)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM6():
    """RELEVANT IMPLICATION: IDENTITY"""
    premises = ['\\Box (A \\leftrightarrow B)','(A \\preceq B)','(B \\preceq A)']
    conclusions = ['(A \\equiv B)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM7():
    """STRICT IMPLICATION"""
    premises = ['\\Box (A \\rightarrow B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM8():
    """REVERSE DISTRIBUTION: DISJUNCTION OVER CONJUNCTION"""
    premises = []
    conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\preceq (A \\vee (B \\wedge C)))']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM9():
    """REVERSE DISTRIBUTION: CONJUNCTION OVER DISJUNCTION"""
    premises = []
    conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\preceq (A \\wedge (B \\vee C)))']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM10():
    """CONJUNCTION INTRODUCTION"""
    premises = ['(A \\preceq B)']
    conclusions = ['(A \\preceq (B \\wedge C))']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL_CM11():
    """DISJUNCTION INTRODUCTION"""
    premises = ['(A \\preceq B)']
    conclusions = ['(A \\preceq (B \\vee C))']
    settings = {
        'N' : 3,
        'desired_status' : True,
        'contingent' : True,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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






###########################
##### RELEVANCE LOGIC #####
###########################

### DEFINITIONAL EQUIVALENTS

@pytest.mark.timeout(max_time)
def test_RL1():
    """RELEVANCE TO CONJUNCTION"""
    premises = ['(A \\preceq B)']
    conclusions = ['((A \\wedge B) \\leq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL2():
    """RELEVANCE TO DISJUNCTION"""
    premises = ['(A \\preceq B)']
    conclusions = ['((A \\vee B) \\sqsubseteq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL3():
    """CONJUNCTION TO RELEVANCE"""
    premises = ['((A \\wedge B) \\leq B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL4():
    """DISJUNCTION TO RELEVANCE"""
    premises = ['((A \\vee B) \\sqsubseteq B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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



### AXIOMS

@pytest.mark.timeout(max_time)
def test_RL5():
    """CONJUNCTION INTRODUCTION"""
    premises = []
    conclusions = ['(A \\preceq (A \\wedge B))']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL6():
    """DISJUNCTION INTRODUCTION"""
    premises = []
    conclusions = ['(A \\preceq (A \\vee B))']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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




### CONSTITUTIVE INTERACTION

@pytest.mark.timeout(max_time)
def test_RL7():
    """GROUNDING RELEVANCE"""
    premises = ['(A \\leq B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL8():
    """ESSENCE RELEVANCE"""
    premises = ['(A \\sqsubseteq B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
def test_RL9():
    """IDENTITY RELEVANCE"""
    premises = ['(A \\equiv B)']
    conclusions = ['(A \\preceq B)']
    settings = {
        'N' : 3,
        'desired_status' : False,
        'contingent' : False,
        'non_null' : True,
        'non_empty' : True,
        'disjoint' : False,
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
