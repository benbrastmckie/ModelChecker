"""run 'pytest' from the '.../Code' directory"""
import pytest
from src.model_checker.model_structure import make_model_for

print(f"\nPytest location: {pytest}")

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

@pytest.mark.timeout(5)
def test_EXT_CM1():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)





### VALID ###

@pytest.mark.timeout(5)
def test_EXT1():
    N = 3
    premises = ['A','(A rightarrow B)']
    conclusions = ['B']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)
