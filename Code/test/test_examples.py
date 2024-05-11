from model_checker.model_structure import make_model_for

N = 3
premises = ['(A boxright B)']
conclusions = ['(A boxright (A vee B)']

def test_models(prems, cons, length):
    """test if models are found for the examples"""
    mod = make_model_for(length)(prems, cons)
    assert mod.model_status is True

test_models(premises,conclusions,N)
