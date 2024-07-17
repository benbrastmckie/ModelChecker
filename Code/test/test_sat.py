"""run 'pytest' from the '.../Code' directory"""
import pytest
from src.model_checker.model_structure import make_model_for

print(f"\nPytest location: {pytest}")

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
    mod_setup = make_model_for(N, premises, conclusions)
    mod_status = mod_setup.model_status
    mod_time = mod_setup.model_runtime
    assert (mod_status == desired), failure_string(desired, premises, conclusions, mod_time)

def find_model_status(premises, conclusions, desired, N):
    mod_setup = make_model_for(N, premises, conclusions)
    mod_status = mod_setup.model_status
    mod_time = mod_setup.model_runtime
    if mod_status != desired and N < 10:
        N += 1
        find_model_status(premises, conclusions, desired, N)
    print(f"Found model in {mod_time} for N = {N}.")



### INVALID ###

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING
@pytest.mark.timeout(5)
def test_CFCM1():
    N = 3
    premises = ['(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
# premises = ['(A circleright C)']
# conclusions = ['((A wedge B) circleright C)']

# # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
# premises = ['(A boxright C)', 'Diamond (A wedge B)']
# conclusions = ['((A wedge B) boxright C)']

@pytest.mark.timeout(500)
def test_STA_w_negation():
    N = 4
    premises = ['\\neg A', '(A \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
# # NOTE: with Z3 quantifiers ran for 347 seconds on the MIT server; now .1949 seconds locally
# N = 4
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A wedge B) boxright C)']

@pytest.mark.timeout(30)
def test_CL_6_no_neg():
    N = 3
    premises = ['(A \\boxright B)']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(300)
def test_CL_6():
    """SLOW: requires N = 4 and 125 seconds on the MIT server"""
    N = 4
    premises = ['(A \\boxright B)', '\\neg B']
    conclusions = ['(\\neg B \\boxright \\neg A)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A boxright B)']
# conclusions = ['(neg B boxright neg A)']

@pytest.mark.timeout(10)
def test_transitivity(): # aka CL_2
    N = 3
    premises = ['(A \\boxright B)','(B \\boxright C)']
    conclusions = ['(A \\boxright C)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
# # NOTE: with Z3 quantifiers 78 seconds on the MIT server; now .1311 seconds locally
# N = 4
# premises = ['neg A','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
# N = 4
# premises = ['neg A','neg B','(A boxright B)','(B boxright C)']
# conclusions = ['(A boxright C)']

# # SOBEL SEQUENCE (N = 3)
# N = 3
# premises = [
#     '(A boxright X)', # 0.03 seconds locally
#     'neg ((A wedge B) boxright X)', # 1.4 seconds locally
#     '(((A wedge B) wedge C) boxright X)', # 4.9 seconds locally
# ]
# conclusions = []

# # SOBEL SEQUENCE WITH POSSIBILITY (N = 4)
# N = 4
# premises = [
#     'Diamond A',
#     '(A boxright X)',
#     'Diamond (A wedge B)',
#     'neg ((A wedge B) boxright X)', # N = 4: 155.4 seconds on the MIT servers; now .1587 seconds
#     'Diamond ((A wedge B) wedge C)',
#     '(((A wedge B) wedge C) boxright X)',
#     'Diamond (((A wedge B) wedge C) wedge D)', # requires N > 3 to avoid FALSE PREMISE
# ]
# conclusions = []

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

# # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
# premises = ['neg A','(A boxright (B vee C))']
# conclusions = ['(A boxright B)','(A boxright C)']

# # # DISJUNCTIVE ANTECEDENT
# N = 4 # NOTE: with Z3 quantifiers for 40 seconds locally; now .2785 seconds locally
# premises = ['(A boxright C)','(B boxright C)']
# conclusions = ['((A vee B) boxright C)']

@pytest.mark.timeout(500)
def test_CL_5():
    N = 4
    premises = ['(A \\boxright C)', '(B \\boxright C)']
    conclusions = ['((A \\wedge B) \\boxright C)']
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
def test_CL_7():
    N = 3
    premises = ['((A \\wedge B) \\boxright C)']
    conclusions = ['(A \\boxright (B \\boxright C))']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
# premises = ['((A wedge B) boxright C)','Diamond (A wedge B)']
# conclusions = ['(A boxright (B boxright C))']

@pytest.mark.timeout(5)
def test_other_1():
    N = 3
    premises = ['\\neg A','\\neg (A \\boxright B)']
    conclusions = ['(A \\boxright \\neg B)']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

@pytest.mark.timeout(5)
def test_bot():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)

# # NOTE: failed on the MIT server
# @pytest.mark.timeout(0)
# def test_CL_8():
#     """NOTE: DOES NOT FIND COUNTERMODEL"""
#     N = 4
#     premises = ['(A \\boxright (B \\boxright C))']
#     conclusions = ['((A \\wedge B) \\boxright C)']
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)






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
