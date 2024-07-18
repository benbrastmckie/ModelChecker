"""run 'pytest' from the '.../Code' directory"""
import pytest
from .utils import (
    check_model_status,
    max_time,
)



### INVALID ###

@pytest.mark.timeout(max_time)
def test_EXT_CM1():
    N = 3
    premises = ['A']
    conclusions = ['neg A']
    desired_model_status = True
    check_model_status(premises, conclusions, desired_model_status, N)





### VALID ###

@pytest.mark.timeout(max_time)
def test_EXT1():
    N = 3
    premises = ['A','(A rightarrow B)']
    conclusions = ['B']
    desired_model_status = False
    check_model_status(premises, conclusions, desired_model_status, N)
