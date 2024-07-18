"""run 'pytest' from the '.../Code' directory"""
from src.model_checker.model_structure import make_model_for

max_time = 2
contingent = True

def failure_string(desired, premises, conclusions, time):
    if desired is False:
        return f'Erroneously found a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n\nMax time: {max_time}'
    return f'Erroneously did not find a model:\n\nPremises:\n{premises}\n\nConclusions:\n{conclusions}\n\nRun time: {time} seconds\n\nMax time: {max_time}'

def check_model_status(premises, conclusions, desired, N):
    mod_setup = make_model_for(N, premises, conclusions, max_time, contingent)
    mod_status = mod_setup.model_status
    mod_time = mod_setup.model_runtime
    mod_timeout = mod_setup.timeout
    assert (mod_timeout is False), f'Model timed out. Consider increasing max_time to be > {max_time}.'
    assert (mod_status == desired), failure_string(desired, premises, conclusions, mod_time)

# def find_model_status(premises, conclusions, desired, N):
#     mod_setup = make_model_for(N, premises, conclusions, max_time, contingent)
#     mod_status = mod_setup.model_status
#     mod_time = mod_setup.model_runtime
#     if mod_status != desired and N < 10:
#         N += 1
#         find_model_status(premises, conclusions, desired, N)
#     print(f"Found model in {mod_time} for N = {N}.")
