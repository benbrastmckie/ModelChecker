# from semantics import ForAll
from model_structure import make_model_for, StateSpace
import pytest


# NOTE: crashes locally
# @pytest.mark.timeout(500)
# def test_CL_5():
#     """SLOW: requires N = 4 and 347 seconds on the MIT server"""
N = 4
premises = ['(A \\boxright C)', '(B \\boxright C)']
conclusions = ['((A \\wedge B) \\boxright C)']
desired_model_status = True
mod_setup = make_model_for(N, premises, conclusions)
mod_status, model, runtime = mod_setup.solve(mod_setup.constraints)
if mod_status:
    ss = StateSpace(mod_setup)
    ss.print_all()
    print(runtime)
else:
    mod_setup.no_model_print(True)

def failure_string(desired, premises, conclusions, time):
    if desired is False:
        return f'Erroneously found a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n'
    return f'ERROneously did not find a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n'

def check_model_status(premises, conclusions, desired, N):
    mod_setup = make_model_for(N, premises, conclusions)
    mod_status = mod_setup.model_status
    mod_time = mod_setup.model_runtime
    assert (mod_status == desired), failure_string(desired, premises, conclusions, mod_time)
    try: 
        StateSpace(mod_setup).print_all()
    except:
        print(f'no model correctly found for:\n{premises}\n{conclusions}')
    print(f'solved in {mod_time} seconds\n\n')

def find_model_status(premises, conclusions, desired, N):
    mod_setup = make_model_for(N, premises, conclusions)
    mod_status = mod_setup.model_status
    mod_time = mod_setup.model_runtime
    if mod_status != desired and N < 10:
        N += 1
        find_model_status(premises, conclusions, desired, N)
    print(f"Found model in {mod_time} for N = {N}.")



### INVALID ###

@pytest.mark.timeout(5)
def test_bot():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_CL_1():
    N = 3
    premises = ['A', 'B']
    conclusions = ['(A boxright B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(10)
def test_transitivity(): # aka CL_2
    N = 3
    premises = ['(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_CL_3():
    N = 3
    premises = ['\\neg A']
    conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(10)
def test_CL_4():
    N = 3
    premises = ['(A \\boxright (B \\vee C))']
    conclusions = ['((A \\boxright B) \\vee (A \\boxright C))']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# NOTE: crashes locally
@pytest.mark.timeout(500)
def test_CL_5():
    """SLOW: requires N = 4 and 347 seconds on the MIT server"""
    N = 4
    premises = ['(A \\boxright C)', '(B \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# NOTE: didn't work on the MIT server
@pytest.mark.timeout(300)
def test_CL_6():
    """SLOW: requires N = 4 and 125 seconds on the MIT server"""
    N = 4
    premises = ['(A \\boxright B)', '\\neg B']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_CL_6_no_neg():
    N = 3
    premises = ['(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(10)
def test_CL_7():
    N = 3
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# NOTE: failed on the MIT server
@pytest.mark.timeout(0)
def test_CL_8():
    """SLOW: MIT servers found a model in 467 seconds"""
    N = 3
    premises = ['(A \\boxright (B \\boxright C))']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_CL_9():
    N = 3
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_STA(): # aka CL_9
    N = 3
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# NOTE: failed on the MIT server
@pytest.mark.timeout(500)
def test_STA_w_negation():
    """SLOW: requires N = 4 and 242 seconds on the MIT server"""
    N = 4
    premises = ['\\neg A', '(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_other_1():
    N = 3
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)


### VALID ###

@pytest.mark.timeout(30)
def test_R1():
    N = 3
    premises = ['(A \\rightarrow B)','A']
    conclusions = ['B']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R2():
    N = 3
    premises = ['(A \\boxright B)']
    conclusions = ['(A \\rightarrow B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R3():
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R4():
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['(B \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R5():
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R6():
    N = 3
    premises = ['(A \\boxright C)', '(B \\boxright C)', '((A \\wedge B) \\boxright C)']
    conclusions = ['((A \\vee B) \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(40)
def test_R7_R8():
    N = 3
    premises = ['(A \\boxright (B \\wedge C))']
    conclusions = ['(A \\boxright B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_R9():
    N = 3
    premises = ['(A \\boxright B)','(A \\boxright C)']
    conclusions = ['(A \\boxright (B \\wedge C))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(100)
def test_R10():
    N = 3
    premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)


test_bot()
test_CL_1()
test_transitivity()
test_CL_3()
test_CL_4()
test_CL_5()
test_CL_6()
test_CL_6_no_neg()
test_CL_7()
test_CL_8()
test_CL_9()
test_STA()
test_STA_w_negation()
test_other_1()

# test_R2() # erroneously finds model
test_R3()
test_R4()
test_R5()
test_R6()
test_R7_R8()
test_R9()
# test_R10() # erroneously finds model
