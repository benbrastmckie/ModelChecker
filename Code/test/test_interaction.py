"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)


### INVALID ###

# @pytest.mark.timeout(max_time)
# def test_INT_CM1():
#     N = 3
#     premises = []
#     conclusions = []
#     desired_model_status = True
#     check_model_status(premises, conclusions, desired_model_status, N)





### VALID ###

@pytest.mark.timeout(max_time)
def test_INT1():
    N = 3
    premises = ['Box (A rightarrow B)']
    conclusions = ['(A boxright B)']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)
