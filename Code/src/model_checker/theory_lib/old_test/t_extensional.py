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
    TopOperator,
    BotOperator,
)

semantics = Semantics
proposition = Proposition
operators = OperatorCollection(
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
    TopOperator,
    BotOperator,
)

max_time = default_max_time

#####################################
##### EXTENSIONAL COUNTERMODELS #####
#####################################

@pytest.mark.timeout(max_time)
def test_EXT_CM1():
    premises = ['A']
    conclusions = ['\\neg A']
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






#############################
##### EXTENSIONAL LOGIC #####
#############################

@pytest.mark.timeout(max_time)
def test_EXT1():
    premises = ['A','(A \\rightarrow B)']
    conclusions = ['B']
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
def test_EXT2():
    premises = []
    conclusions = ['(A \\rightarrow (B \\rightarrow A))']
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
def test_EXT3():
    premises = []
    conclusions = ['((A \\rightarrow (B \\rightarrow C)) \\rightarrow ((A \\rightarrow B) \\rightarrow (A \\rightarrow C)))']
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
def test_EXT4():
    premises = []
    conclusions = ['((\\neg A \\rightarrow \\neg B) \\rightarrow (B \\rightarrow A))']
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
