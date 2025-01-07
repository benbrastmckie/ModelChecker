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
    PossibilityOperator,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
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
    PossibilityOperator,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
)

max_time = default_max_time

######################################
##### CONSTITUTIVE COUNTERMODELS #####
######################################

@pytest.mark.timeout(max_time)
def test_CL_CM1():
    """STRICT IMPLICATION TO GROUND"""
    premises = ['\\Box (A \\rightarrow B)']
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
def test_CL_CM2():
    """STRICT IMPLICATION TO ESSENCE"""
    premises = ['\\Box (B \\rightarrow A)']
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
def test_CL_CM3():
    """GROUND CONJUNCTION SUPPLEMENTATION"""
    premises = ['(A \\leq B)','(C \\leq D)']
    conclusions = ['((A \\wedge C) \\leq (B \\wedge D))']
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
def test_CL_CM4():
    """ESSENCE DISJUNCTION SUPPLEMENTATION"""
    premises = ['(A \\sqsubseteq B)','(C \\sqsubseteq D)']
    conclusions = ['((A \\vee C) \\sqsubseteq (B \\vee D))']
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
def test_CL_CM5():
    """IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION"""
    premises = []
    conclusions = ['(A \\equiv (A \\vee (A \\wedge B)))']
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
def test_CL_CM6():
    """IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION"""
    premises = []
    conclusions = ['(A \\equiv (A \\wedge (A \\vee B)))']
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
def test_CL_CM7():
    """NECESSARY EQUIVALENTS"""
    premises = []
    conclusions = ['((A \\vee \\neg A) \\equiv (B \\vee \\neg B))']
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
def test_CL_CM8():
    """ESSENCE DISTRIBUTION"""
    premises = []
    conclusions = ['(((A \\vee B) \\wedge (A \\vee C)) \\sqsubseteq (A \\vee (B \\wedge C)))']
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
def test_CL_CM9():
    """GROUND DISTRIBUTION"""
    premises = []
    conclusions = ['(((A \\wedge B) \\vee (A \\wedge C)) \\leq (A \\wedge (B \\vee C)))']
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
def test_CL_CM10():
    """IDENTITY DISTRIBUTION"""
    premises = []
    conclusions = ['((A \\vee (B \\wedge C)) \\equiv ((A \\vee B) \\wedge (A \\vee C)))']
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
###### CONSTITUTIVE LOGIC ######
################################

### DEFINITIONAL EQUIVALENTS ###

@pytest.mark.timeout(max_time)
def test_CL1():
    """GROUND TO ESSENCE"""
    premises = ['(A \\leq B)']
    conclusions = ['(\\neg A \\sqsubseteq \\neg B)']
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
def test_CL2():
    """ESSENCE TO GROUND"""
    premises = ['(A \\sqsubseteq B)']
    conclusions = ['(\\neg A \\leq \\neg B)']
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
def test_CL3():
    """ESSENCE TO IDENTITY"""
    premises = ['(A \\sqsubseteq B)']
    conclusions = ['((A \\wedge B) \\equiv B)']
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
def test_CL4():
    """IDENTITY TO ESSENCE"""
    premises = ['((A \\wedge B) \\equiv B)']
    conclusions = ['(A \\sqsubseteq B)']
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
def test_CL5():
    """GROUND TO IDENTITY"""
    premises = ['(A \\leq B)']
    conclusions = ['((A \\vee B) \\equiv B)']
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
def test_CL6():
    """IDENTITY TO GROUND"""
    premises = ['((A \\vee B) \\equiv B)']
    conclusions = ['(A \\leq B)']
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
def test_CL7():
    """NEGATION TRANSPARENCY"""
    premises = ['(A \\equiv B)']
    conclusions = ['(\\neg A \\equiv \\neg B)']
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
def test_CL8():
    """REVERSE NEGATION TRANSPARENCY"""
    premises = ['(\\neg A \\equiv \\neg B)']
    conclusions = ['(A \\equiv B)']
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



### AXIOMS AND RULES: GROUND ###

@pytest.mark.timeout(max_time)
def test_CL9():
    """DISJUNCTS GROUND DISJUNCTIONS"""
    premises = []
    conclusions = ['(A \\leq (A \\vee B))']
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
def test_CL10():
    """CONJUNCTIONS GROUND DISJUNCTIONS"""
    premises = []
    conclusions = ['((A \\wedge B) \\leq (A \\vee B))']
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
def test_CL11():
    """GROUNDING NEGATED CONJUNCTION"""
    premises = []
    conclusions = ['(\\neg A \\leq \\neg (A \\wedge B))']
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
def test_CL12():
    """GROUNDING TRANSITIVITY"""
    premises = ['(A \\leq B)','(B \\leq C)']
    conclusions = ['(A \\leq C)']
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
def test_CL13():
    """DISJUNCTION INTRODUCTION GROUNDING ANTECEDENT"""
    premises = ['(A \\leq C)','(B \\leq C)']
    conclusions = ['((A \\vee B) \\leq C)']
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
def test_CL14():
    """GROUNDING ANTISYMMETRY"""
    premises = ['(A \\leq B)','(B \\leq A)']
    conclusions = ['(A \\equiv B)']
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
def test_CL15():
    """GROUNDING MODUS PONENS"""
    premises = ['A','(A \\leq B)']
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
def test_CL16():
    """GROUNDING MODUS TOLLENS"""
    premises = ['\\neg B','(A \\leq B)']
    conclusions = ['\\neg A']
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
def test_CL17():
    """GROUND DISJUNCTION SUPPLEMENTATION"""
    premises = ['(A \\leq B)','(C \\leq D)']
    conclusions = ['((A \\vee C) \\leq (B \\vee D))']
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





### AXIOMS AND RULES: ESSENCE ###

@pytest.mark.timeout(max_time)
def test_CL18():
    """CONJUNCTS ESSENTIAL TO CONJUNCTION"""
    premises = []
    conclusions = ['(A \\sqsubseteq (A \\wedge B))']
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
def test_CL19():
    """DISJUNCTIONS ESSENTIAL TO CONJUNCTIONS"""
    premises = []
    conclusions = ['((A \\vee B) \\sqsubseteq (A \\wedge B))']
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
def test_CL20():
    """ESSENCE NEGATED DISJUNCTION"""
    premises = []
    conclusions = ['(\\neg A \\sqsubseteq \\neg (A \\vee B))']
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
def test_CL21():
    """ESSENCE TRANSITIVITY"""
    premises = ['(A \\sqsubseteq B)','(B \\sqsubseteq C)']
    conclusions = ['(A \\sqsubseteq C)']
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
def test_CL22():
    """CONJUNCTION INTRODUCTION ESSENCE ANTECEDENT"""
    premises = ['(A \\sqsubseteq C)','(B \\sqsubseteq C)']
    conclusions = ['((A \\wedge B) \\sqsubseteq C)']
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
def test_CL23():
    """ESSENCE ANTISYMMETRY"""
    premises = ['(A \\sqsubseteq B)','(B \\sqsubseteq A)']
    conclusions = ['(A \\equiv B)']
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
def test_CL24():
    """ESSENCE MODUS PONENS"""
    premises = ['B','(A \\sqsubseteq B)']
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
def test_CL25():
    """ESSENCE MODUS TOLLENS"""
    premises = ['\\neg A','(A \\sqsubseteq B)']
    conclusions = ['\\neg B']
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
def test_CL26():
    """ESSENCE CONJUNCTION SUPPLEMENTATION"""
    premises = ['(A \\sqsubseteq B)','(C \\sqsubseteq D)']
    conclusions = ['((A \\wedge C) \\sqsubseteq (B \\wedge D))']
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





### AXIOMS AND RULES: IDENTITY ###

@pytest.mark.timeout(max_time)
def test_CL27():
    """CONJUNCTION IDEMPOTENCE"""
    premises = []
    conclusions = ['(A \\equiv (A \\wedge A))']
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
def test_CL28():
    """DISJUNCTION IDEMPOTENCE"""
    premises = []
    conclusions = ['(A \\equiv (A \\vee A))']
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
def test_CL29():
    """COMMUTATIVITY"""
    premises = ['(A \\equiv B)']
    conclusions = ['(B \\equiv A)']
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
def test_CL30():
    """NEGATION TRANSPARENCY"""
    premises = ['(A \\equiv B)']
    conclusions = ['(\\neg B \\equiv \\neg A)']
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
def test_CL31():
    """TRANSITIVITY"""
    premises = ['(A \\equiv B)', '(B \\equiv C)']
    conclusions = ['(A \\equiv C)']
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
def test_CL32():
    """CONJUNCTION MONOTONICITY"""
    premises = ['(A \\equiv B)']
    conclusions = ['((A \\wedge C) \\equiv (B \\wedge C))']
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
def test_CL33():
    """DISJUNCTION MONOTONICITY"""
    premises = ['(A \\equiv B)']
    conclusions = ['((A \\vee C) \\equiv (B \\vee C))']
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





### MODAL INTERACTION ###

@pytest.mark.timeout(max_time)
def test_CL34():
    """GROUND TO STRICT IMPLICATION"""
    premises = ['(A \\leq B)']
    conclusions = ['\\Box (A \\rightarrow B)']
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
def test_CL35():
    """ESSENCE TO STRICT IMPLICATION"""
    premises = ['(A \\sqsubseteq B)']
    conclusions = ['\\Box (B \\rightarrow A)']
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
def test_CL36():
    """IDENTITY TO NECESSARY EQUIVALENCE"""
    premises = ['(A \\equiv B)']
    conclusions = ['\\Box (B \\leftrightarrow A)']
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
def test_CL37():
    """NECESSITY OF GROUND"""
    premises = ['(A \\leq B)']
    conclusions = ['\\Box (A \\leq B)']
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
def test_CL38():
    """NECESSITY OF ESSENCE"""
    premises = ['(A \\sqsubseteq B)']
    conclusions = ['\\Box (A \\sqsubseteq B)']
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
def test_CL39():
    """NECESSITY OF IDENTITY"""
    premises = ['(A \\equiv B)']
    conclusions = ['\\Box (A \\equiv B)']
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
