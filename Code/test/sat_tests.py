import pytest
import sys
import os

# Get the directory path of the current file
current_dir = os.path.dirname(__file__)
# Construct the full path to your project root
project_root = os.path.abspath(os.path.join(current_dir, ".."))
# Add the project root to the Python path
sys.path.append(project_root)
from src.model_checker.model_structure import make_model_for

def failure_string(desired, premises, conclusions):
    if desired is False:
        return f'Erroneously found a model for premises {premises} and conclusions {conclusions}'
    return f'Erroneously did NOT find a model for premises {premises} and conclusions {conclusions}'

def check_model_status(premises, conclusions, desired, N):
    mod_setup, mod_structure = make_model_for(N, premises, conclusions)
    assert (mod_structure.model_status == desired), failure_string(desired, premises, conclusions)


### INVALID ###

@pytest.mark.timeout(5)
def test_bot():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_2():
    N = 3
    premises = ['A', 'B']
    conclusions = ['(A boxright B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_3():
    N = 3
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_4():
    N = 3
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_transitivity():
    N = 3
    premises = ['(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_6():
    N = 3
    premises = ['\\neg A']
    conclusions = ['(A \\boxright B)','(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(10)
def test_7():
    N = 3
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)


### VALID ###

@pytest.mark.timeout(30)
def test_8():
    N = 3
    premises = ['A','(A \\rightarrow B)']
    conclusions = ['B']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_9():
    N = 3
    premises = ['(A \\boxright B)']
    conclusions = ['(A \\rightarrow B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_10():
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_11():
    N = 3
    premises = ['((A \\vee B) \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_12():
    N = 3
    premises = ['(A \\boxright (B \\wedge C))']
    conclusions = ['(A \\boxright B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_13():
    N = 3
    premises = ['(A \\boxright B)','(A \\boxright C)']
    conclusions = ['(A \\boxright (B \\wedge C))']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(30)
def test_14():
    N = 3
    premises = ['(A \\boxright B)','((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)


# haven't set these up yet
################################
######### NOT WORKING ##########
################################

# M: for the not working ones, can you put what the current output is (not
# making or making a model), and what the desired output is?
# B: are you able to run the file? I will add output to issues in github

### HIGH PRIORITY ###

# # NOTE: doesn't work b/c should countermodel
# # recursive printing would be helpful.
# premises = ['(A \\boxright C)','(B \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

# # NOTE: should find a model. works without `\\neg A`.
# premises = ['\\neg A','(A \\boxright C)']
# conclusions = ['((A \\wedge B) \\boxright C)']

### MEDIUM PRIORITY ###

# NOTE: this isn't finding models still
premises = ['(A \\boxright B)','\\neg B']
# NOTE: this seems to work now but the print statement is hard to read
# premises = ['(A \\boxright B)']
conclusions = ['(\\neg B \\boxright \\neg A)']


# # NOTE: this seems to work now but the print statement is hard to read
# premises = ['((A \\wedge B) \\boxright C)']
# conclusions = ['(A \\boxright (B \\boxright C))']

# # NOTE: this is slow for N = 5 and does not find models for N = 3
# premises = ['(A \\boxright (B \\boxright C))']
# conclusions = ['((A \\wedge B) \\boxright C)']
