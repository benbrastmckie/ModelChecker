"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)

######################################
##### CONSTITUTIVE COUNTERMODELS #####
######################################

@pytest.mark.timeout(max_time)
def test_CL_CM1():
    """STRICT IMPLICATION TO GROUND"""
    N = 3
    premises = ['Box (A rightarrow B)']
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
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM2():
    """STRICT IMPLICATION TO ESSENCE"""
    N = 3
    premises = ['Box (B rightarrow A)']
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
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM3():
    """GROUND CONJUNCTION SUPPLEMENTATION WITH POSSIBILITY"""
    N = 3
    premises = ['(A leq B)','(C leq D)']
    conclusions = ['((A wedge C) leq (B wedge D))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM4():
    """ESSENCE CONJUNCTION SUPPLEMENTATION"""
    N = 3
    premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
    conclusions = ['((A vee C) sqsubseteq (B vee D))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM5():
    """IDENTITY ABSORPTION: DISJUNCTION OVER CONJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(A equiv (A vee (A wedge B)))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM6():
    """IDENTITY ABSORPTION: CONJUNCTION OVER DISJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(A equiv (A wedge (A vee B)))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM7():
    """NECESSARY EQUIVALENTS"""
    N = 3
    premises = []
    conclusions = ['((A vee neg A) equiv (B vee neg B))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM8():
    """ESSENCE DISTRIBUTION"""
    N = 3
    premises = []
    conclusions = ['(((A vee B) wedge (A vee C)) sqsubseteq (A vee (B wedge C)))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM9():
    """GROUND DISTRIBUTION"""
    N = 3
    premises = []
    conclusions = ['(((A wedge B) vee (A wedge C)) leq (A wedge (B vee C)))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL_CM10():
    """IDENTITY DISTRIBUTION"""
    N = 3
    premises = []
    conclusions = ['((A vee (B wedge C)) equiv ((A vee B) wedge (A vee C)))']
    desired_model_status = True
    contingent_bool = True
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )





################################
###### CONSTITUTIVE LOGIC ######
################################

### DEFINITIONAL EQUIVALENTS ###

@pytest.mark.timeout(max_time)
def test_CL1():
    """GROUND TO ESSENCE"""
    N = 3
    premises = ['(A leq B)']
    conclusions = ['(neg A sqsubseteq neg B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL2():
    """ESSENCE TO GROUND"""
    N = 3
    premises = ['(A sqsubseteq B)']
    conclusions = ['(neg A leq neg B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL3():
    """ESSENCE TO IDENTITY"""
    N = 3
    premises = ['(A sqsubseteq B)']
    conclusions = ['((A wedge B) equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL4():
    """IDENTITY TO ESSENCE: NOTE: with Z3 quantifiers 17.2 seconds locally; now .0103 seconds locally"""
    N = 3
    premises = ['((A wedge B) equiv B)']
    conclusions = ['(A sqsubseteq B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL5():
    """GROUND TO IDENTITY"""
    N = 3
    premises = ['(A leq B)']
    conclusions = ['((A vee B) equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL6():
    """IDENTITY TO GROUND"""
    N = 3
    premises = ['((A vee B) equiv B)']
    conclusions = ['(A leq B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL7():
    """NEGATION TRANSPARENCY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['(neg A equiv neg B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL8():
    """REVERSE NEGATION TRANSPARENCY"""
    N = 3
    premises = ['(neg A equiv neg B)']
    conclusions = ['(A equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )



### AXIOMS AND RULES: GROUND ###

@pytest.mark.timeout(max_time)
def test_CL9():
    """DISJUNCTS GROUND DISJUNCTIONS"""
    N = 3
    premises = []
    conclusions = ['(A leq (A vee B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL10():
    """CONJUNCTIONS GROUND DISJUNCTIONS"""
    N = 3
    premises = []
    conclusions = ['((A wedge B) leq (A vee B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL11():
    """GROUNDING NEGATED CONJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(neg A leq neg (A wedge B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL12():
    """GROUNDING TRANSITIVITY"""
    N = 3
    premises = ['(A leq B)','(B leq C)']
    conclusions = ['(A leq C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL13():
    """DISJUNCTION INTRODUCTION GROUNDING ANTECEDENT"""
    N = 3
    premises = ['(A leq C)','(B leq C)']
    conclusions = ['((A vee B) leq C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL14():
    """GROUNDING ANTISYMMETRY"""
    N = 3
    premises = ['(A leq B)','(B leq A)']
    conclusions = ['(A equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL15():
    """GROUNDING MODUS PONENS"""
    N = 3
    premises = ['A','(A leq B)']
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
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL16():
    """GROUNDING MODUS TOLLENS"""
    N = 3
    premises = ['neg B','(A leq B)']
    conclusions = ['neg A']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL17():
    """GROUND DISJUNCTION SUPPLEMENTATION"""
    N = 3
    premises = ['(A leq B)','(C leq D)']
    conclusions = ['((A vee C) leq (B vee D))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )





### AXIOMS AND RULES: ESSENCE ###

@pytest.mark.timeout(max_time)
def test_CL18():
    """CONJUNCTS ESSENTIAL TO CONJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(A sqsubseteq (A wedge B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL19():
    """DISJUNCTIONS ESSENTIAL TO CONJUNCTIONS"""
    N = 3
    premises = []
    conclusions = ['((A vee B) sqsubseteq (A wedge B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL20():
    """ESSENCE NEGATED DISJUNCTION"""
    N = 3
    premises = []
    conclusions = ['(neg A sqsubseteq neg (A vee B))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL21():
    """ESSENCE TRANSITIVITY"""
    N = 3
    premises = ['(A sqsubseteq B)','(B sqsubseteq C)']
    conclusions = ['(A sqsubseteq C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL22():
    """CONJUNCTION INTRODUCTION ESSENCE ANTECEDENT"""
    N = 3
    premises = ['(A sqsubseteq C)','(B sqsubseteq C)']
    conclusions = ['((A wedge B) sqsubseteq C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL23():
    """ESSENCE ANTISYMMETRY"""
    N = 3
    premises = ['(A sqsubseteq B)','(B sqsubseteq A)']
    conclusions = ['(A equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL24():
    """ESSENCE MODUS PONENS"""
    N = 3
    premises = ['B','(A sqsubseteq B)']
    conclusions = ['A']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL25():
    """ESSENCE MODUS TOLLENS"""
    N = 3
    premises = ['neg A','(A sqsubseteq B)']
    conclusions = ['neg B']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL26():
    """ESSENCE CONJUNCTION SUPPLEMENTATION"""
    N = 3
    premises = ['(A sqsubseteq B)','(C sqsubseteq D)']
    conclusions = ['((A wedge C) sqsubseteq (B wedge D))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )





### AXIOMS AND RULES: IDENTITY ###

@pytest.mark.timeout(max_time)
def test_CL27():
    """CONJUNCTION IDEMPOTENCE"""
    N = 3
    premises = []
    conclusions = ['(A equiv (A wedge A))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL28():
    """DISJUNCTION IDEMPOTENCE"""
    N = 3
    premises = []
    conclusions = ['(A equiv (A vee A))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL29():
    """COMMUTATIVITY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['(B equiv A)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL30():
    """NEGATION TRANSPARENCY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['(neg B equiv neg A)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL31():
    """TRANSITIVITY"""
    N = 3
    premises = ['(A equiv B)', '(B equiv C)']
    conclusions = ['(A equiv C)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL32():
    """CONJUNCTION MONOTONICITY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['((A wedge C) equiv (B wedge C))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL33():
    """DISJUNCTION MONOTONICITY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['((A vee C) equiv (B vee C))']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )





### MODAL INTERACTION ###

@pytest.mark.timeout(max_time)
def test_CL34():
    """GROUND TO STRICT IMPLICATION"""
    N = 3
    premises = ['(A leq B)']
    conclusions = ['Box (A rightarrow B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL35():
    """ESSENCE TO STRICT IMPLICATION"""
    N = 3
    premises = ['(A sqsubseteq B)']
    conclusions = ['Box (B rightarrow A)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL36():
    """IDENTITY TO NECESSARY EQUIVALENCE"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['Box (B leftrightarrow A)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL37():
    """NECESSITY OF GROUND"""
    N = 3
    premises = ['(A leq B)']
    conclusions = ['Box (A leq B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL38():
    """NECESSITY OF ESSENCE"""
    N = 3
    premises = ['(A sqsubseteq B)']
    conclusions = ['Box (A sqsubseteq B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )

@pytest.mark.timeout(max_time)
def test_CL39():
    """NECESSITY OF IDENTITY"""
    N = 3
    premises = ['(A equiv B)']
    conclusions = ['Box (A equiv B)']
    desired_model_status = False
    contingent_bool = False
    disjoint_bool = False
    check_model_status(
        N,
        premises,
        conclusions,
        desired_model_status,
        contingent_bool,
        disjoint_bool
    )
