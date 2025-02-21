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
    NegationOperator, # extensional
    AndOperator,
    OrOperator,
    ConditionalOperator, # extensional defined 
    BiconditionalOperator,
    TopOperator, # extremal
    BotOperator,
    CounterfactualOperator, # counterfactual
    NecessityOperator, # modal
    PossibilityOperator,
    DefNecessityOperator,
    DefPossibilityOperator,  # modal defined
)

semantics = Semantics
proposition = Proposition
operators = OperatorCollection(
    NegationOperator, # extensional
    AndOperator,
    OrOperator,
    ConditionalOperator, # extensional defined 
    BiconditionalOperator,
    TopOperator, # extremal
    BotOperator,
    CounterfactualOperator, # counterfactual
    NecessityOperator, # modal
    PossibilityOperator,
    DefNecessityOperator,
    DefPossibilityOperator,  # modal defined
)

max_time = default_max_time

###############################
##### MODAL COUNTERMODELS #####
###############################

@pytest.mark.timeout(max_time)
def test_ML_CM1():
    """ NECESSITATED ARGUMENTS COUNTERFACTUAL MODUS PONENS """
    premises = ['\\Box A','(A \\rightarrow B)']
    conclusions = ['\\Box B']
    settings = {
        'N' : 3,
        'desired_status' : True,
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
def test_ML_CM2():
    """ COUNTERFACTUAL IMPLIES STRICT CONDITIONAL """
    premises = ['(A \\boxright B)']
    conclusions = ['\\Box (A \\rightarrow B)']
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






################################
######### MODAL LOGIC ##########
################################

@pytest.mark.timeout(max_time)
def test_ML1():
    premises = ['\\Box (A \\rightarrow B)']
    conclusions = ['(A \\boxright B)']
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
def test_ML2():
    # K AXIOM (BOX)
    premises = ['\\Box (A \\rightarrow B)']
    conclusions = ['(\\Box A \\rightarrow \\Box B)']
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
def test_ML3():
    # K AXIOM (TOP)
    premises = ['(\\top \\boxright (A \\rightarrow B))']
    conclusions = ['((\\top \\boxright A) \\rightarrow (\\top \\boxright B))']
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
def test_ML4():
    # T AXIOM (TOP)
    premises = ['(\\top \\boxright A)']
    conclusions = ['A']
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
def test_ML5():
    # T AXIOM (BOX)
    premises = ['\\Box A']
    conclusions = ['A']
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
def test_ML6():
    # 4 AXIOM (TOP)
    premises = ['(\\top \\boxright A)']
    conclusions = ['(\\top \\boxright (\\top \\boxright A))']
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
def test_ML7():
    # 4 AXIOM (BOX)
    premises = ['\\Box A']
    conclusions = ['\\Box \\Box A']
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
def test_ML8():
    # B AXIOM (TOP)
    # NOTE: with Z3 quantifiers MIT ran for 1600 seconds; now .0328 seconds locally
    premises = ['A']
    conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']
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
def test_ML9():
    # B AXIOM (BOX)
    premises = ['A']
    conclusions = ['\\Box \\Diamond A']
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
def test_ML10():
    # 5 AXIOM (TOP)
    # SLOW: 12.9 seconds locally
    premises = ['(\\top \\boxright A)']
    conclusions = ['(\\top \\boxright \\neg (\\top \\boxright \\neg A))']
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
def test_ML11():
    # 5 AXIOM (BOX)
    premises = ['\\Box A']
    conclusions = ['\\Box \\Diamond A']
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
def test_ML12():
    # BOX-TO-\\top EQUIVALENCE
    premises = ['\\Box A']
    conclusions = ['(\\top \\boxright A)']
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
def test_ML13():
    # # TOP-TO-BOX EQUIVALENCE
    premises = ['(\\top \\boxright A)']
    conclusions = ['\\Box A']
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
def test_ML14():
    # NECESSARY EQUIVALENCE
    premises = []
    conclusions = ['\\Box ((A \\vee \\neg A) \\leftrightarrow (B \\vee \\neg B))']
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
