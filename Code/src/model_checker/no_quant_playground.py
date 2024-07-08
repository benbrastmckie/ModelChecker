# from semantics import ForAll
from model_structure import make_model_for, StateSpace


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
else:
    mod_setup.no_model_print(True)