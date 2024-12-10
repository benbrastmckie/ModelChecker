"""run 'pytest' from the '.../Code/src/new_checker/' directory"""
import pytest
from .utils import (
    check_model_status,
    default_max_time,
)

from new_checker.syntactic import (
    OperatorCollection,
)

from new_checker.semantic import (
    Proposition,
    Semantics,
)

from new_checker.defined_operators import (
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
