import pytest
from src.model_checker.model_structure import make_model_for

# NOTE: this does not seem necessary after all; tests are running
# import sys
# import os
# # Get the directory path of the current file
# current_dir = os.path.dirname(__file__)
# # Construct the full path to the src directory
# src_dir = os.path.abspath(os.path.join(current_dir, "../src"))
# # Add the src directory to the Python path
# sys.path.append(src_dir)

def failure_string(desired, premises, conclusions, time):
    if desired is False:
        return f'Erroneously found a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n'
    return f'ERROneously did not find a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n'

def check_model_status(premises, conclusions, desired, N):
    mod_structure = make_model_for(N, premises, conclusions)[1]
    mod_status = mod_structure.model_status
    mod_time = mod_structure.model_runtime
    assert (mod_status == desired), failure_string(desired, premises, conclusions, mod_time)

def find_model_status(premises, conclusions, desired, N):
    mod_structure = make_model_for(N, premises, conclusions)[1]
    mod_status = mod_structure.model_status
    mod_time = mod_structure.model_runtime
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

@pytest.mark.timeout(5)
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

# # @pytest.mark.timeout(0)
# def test_CL_5():
#     """SLOW: requires N = 4 and 347 seconds on the MIT server"""
#     N = 4
#     premises = ['(A \\boxright C)', '(B \\boxright C)']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)

# # @pytest.mark.timeout(0)
# def test_CL_6():
#     """SLOW: requires N = 4 and 125 seconds on the MIT server"""
#     N = 4
#     premises = ['(A \\boxright B)', '\\neg B']
#     conclusions = ['(\\neg B \\boxright \\neg A)']
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)

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

# # @pytest.mark.timeout(0)
# def test_CL_8():
#     """SLOW: MIT servers found a model in 467 seconds"""
#     N = 3
#     premises = ['(A \\boxright (B \\boxright C))']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_CL_9():
    N = 3
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(10)
def test_STA(): # aka CL_9
    N = 3
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # @pytest.mark.timeout(0)
# def test_STA_w_negation():
#     """SLOW: MIT servers found a model in 242 seconds"""
#     N = 4
#     premises = ['\\neg A', '(A \\boxright C)']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)

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

# @pytest.mark.timeout(30)
# def test_R9():
#     """SLOW: runs in 8.4 seconds locally but pytest crashes locally"""
#     N = 3
#     premises = ['(A \\boxright B)','(A \\boxright C)']
#     conclusions = ['(A \\boxright (B \\wedge C))']
#     desired_model_status = False
#     check_model_status(premises, conclusions, desired_model_status, N)

# @pytest.mark.timeout(80)
# def test_R10():
#     """SLOW: runs in 39 seconds locally but pytest crashes locally"""
#     N = 3
#     premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
#     conclusions = ['(A \\boxright C)']
#     desired_model_status = False
#     check_model_status(premises, conclusions, desired_model_status, N)
