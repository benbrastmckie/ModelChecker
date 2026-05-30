~/P/L/ModelChecker ❯❯❯ ./code/run_tests.py                        ✘ 1 master ⬆ ✱
Available theories: bimodal, logos
Available components: builder, iterate, jupyter, models, output, output.notebook
, settings, solver, syntactic, theory_lib, utils
Available subtheories (logos): constitutive, counterfactual, extensional, first_
order, modal, relevance

Running all tests...
================================================================================
ModelChecker Unified Test Runner
================================================================================
Test types: examples, unit, package
Theories: bimodal, logos
Components: builder, iterate, jupyter, models, output, output.notebook, settings
, solver, syntactic, theory_lib, utils

Running example tests for theories: bimodal, logos
  Running example tests for bimodal
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 91 items / 75 deselected / 16 selected                               

src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution.py::test_cli_e
xecution_of_examples PASSED [  6%]
src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py::test_ite
rate_example_function PASSED [ 12%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[EX_CM_1-example_case0] PASSED [ 18%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_1-example_case1] PASSED [ 25%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_2-example_case2] PASSED [ 31%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_3-example_case3] PASSED [ 37%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_4-example_case4] PASSED [ 43%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_5-example_case5] PASSED [ 50%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_CM_6-example_case6] PASSED [ 56%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[EX_TH_1-example_case7] PASSED [ 62%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[MD_TH_1-example_case8] PASSED [ 68%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[TN_TH_2-example_case9] PASSED [ 75%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[BM_TH_1-example_case10] PASSED [ 81%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[BM_TH_2-example_case11] PASSED [ 87%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[BM_TH_3-example_case12] PASSED [ 93%]
src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::test_example_ca
ses[BM_TH_4-example_case13] PASSED [100%]

============================== slowest durations ===============================
0.24s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_1-example_case1]
0.21s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_3-example_case3]
0.21s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[EX_CM_1-example_case0]
0.21s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_TH_1-example_case8]
0.20s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_6-example_case6]
0.20s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[BM_TH_4-example_case13]
0.19s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[BM_TH_3-example_case12]
0.19s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[BM_TH_1-example_case10]
0.19s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_5-example_case5]
0.18s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_2-example_case2]
0.18s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[TN_TH_2-example_case9]
0.18s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[BM_TH_2-example_case11]
0.17s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[MD_CM_4-example_case4]
0.16s call     src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py::
test_example_cases[EX_TH_1-example_case7]
0.13s call     src/model_checker/theory_lib/bimodal/tests/e2e/test_cli_execution
.py::test_cli_execution_of_examples
0.01s call     src/model_checker/theory_lib/bimodal/tests/integration/test_itera
te.py::test_iterate_example_function

(32 durations < 0.005s hidden.  Use -vv to show these durations.)
====================== 16 passed, 75 deselected in 4.60s =======================
  Running example tests for logos
      Testing modal subtheory examples
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 21 items                                                             

src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_CM_1-example_case0] PASSED [  4%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_CM_2-example_case1] PASSED [  9%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_CM_3-example_case2] PASSED [ 14%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_CM_4-example_case3] PASSED [ 19%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_1-example_case4] PASSED [ 23%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_2-example_case5] PASSED [ 28%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_3-example_case6] PASSED [ 33%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_4-example_case7] PASSED [ 38%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_5-example_case8] PASSED [ 42%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_6-example_case9] PASSED [ 47%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_7-example_case10] PASSED [ 52%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_8-example_case11] PASSED [ 57%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_9-example_case12] PASSED [ 61%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_10-example_case13] PASSED [ 66%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_11-example_case14] PASSED [ 71%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_12-example_case15] PASSED [ 76%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_13-example_case16] PASSED [ 80%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_TH_14-example_case17] PASSED [ 85%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_COMP_1-example_case18] PASSED [ 90%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_COMP_2-example_case19] PASSED [ 95%]
src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.p
y::test_modal_examples[MOD_COMP_3-example_case20] PASSED [100%]

============================== slowest durations ===============================
0.13s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_9-example_case12]
0.09s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_2-example_case5]
0.09s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_CM_1-example_case0]
0.08s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_1-example_case4]
0.08s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_8-example_case11]
0.08s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_5-example_case8]
0.08s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_7-example_case10]
0.06s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_CM_2-example_case1]
0.05s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_10-example_case13]
0.05s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_CM_3-example_case2]
0.04s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_4-example_case7]
0.04s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_CM_4-example_case3]
0.04s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_3-example_case6]
0.04s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_6-example_case9]
0.04s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_14-example_case17]
0.03s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_13-example_case16]
0.03s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_12-example_case15]
0.03s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_TH_11-example_case14]
0.02s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_COMP_1-example_case18]
0.02s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_COMP_3-example_case20]
0.01s call     src/model_checker/theory_lib/logos/subtheories/modal/tests/test_m
odal_examples.py::test_modal_examples[MOD_COMP_2-example_case19]

(42 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 21 passed in 2.77s ==============================
      Testing counterfactual subtheory examples
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 37 items                                                             

src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_1-example_case0] PASSED 
[  2%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_2-example_case1] PASSED 
[  5%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_3-example_case2] PASSED 
[  8%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_4-example_case3] PASSED 
[ 10%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_5-example_case4] PASSED 
[ 13%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_6-example_case5] PASSED 
[ 16%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_7-example_case6] PASSED 
[ 18%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_8-example_case7] PASSED 
[ 21%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_9-example_case8] PASSED 
[ 24%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_10-example_case9] PASSED
 [ 27%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_11-example_case10] PASSE
D [ 29%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_12-example_case11] PASSE
D [ 32%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_13-example_case12] PASSE
D [ 35%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_14-example_case13] PASSE
D [ 37%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_15-example_case14] PASSE
D [ 40%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_16-example_case15] PASSE
D [ 43%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_17-example_case16] PASSE
D [ 45%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_18-example_case17] PASSE
D [ 48%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_19-example_case18] PASSE
D [ 51%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_20-example_case19] PASSE
D [ 54%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_21-example_case20] PASSE
D [ 56%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_24-example_case21] PASSE
D [ 59%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_CM_25-example_case22] PASSE
D [ 62%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_1-example_case23] PASSED
 [ 64%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_2-example_case24] PASSED
 [ 67%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_3-example_case25] PASSED
 [ 70%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_4-example_case26] PASSED
 [ 72%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_5-example_case27] PASSED
 [ 75%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_6-example_case28] PASSED
 [ 78%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_7-example_case29] PASSED
 [ 81%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_8-example_case30] PASSED
 [ 83%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_9-example_case31] PASSED
 [ 86%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_10-example_case32] PASSE
D [ 89%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_11-example_case33] PASSE
D [ 91%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_12-example_case34] PASSE
D [ 94%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_13-example_case35] PASSE
D [ 97%]
src/model_checker/theory_lib/logos/subtheories/counterfactual/tests/test_counter
factual_examples.py::test_counterfactual_examples[CF_TH_14-example_case36] PASSE
D [100%]

============================== slowest durations ===============================
1.39s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_20-exampl
e_case19]
1.35s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_19-exampl
e_case18]
0.70s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_14-exampl
e_case13]
0.62s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_13-exampl
e_case12]
0.36s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_9-example
_case31]
0.28s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_24-exampl
e_case21]
0.27s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_3-example
_case25]
0.23s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_7-example
_case29]
0.23s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_6-example
_case28]
0.21s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_12-exampl
e_case11]
0.20s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_11-exampl
e_case10]
0.20s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_17-exampl
e_case16]
0.20s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_6-example
_case5]
0.19s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_1-example
_case0]
0.19s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_5-example
_case4]
0.18s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_16-exampl
e_case15]
0.18s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_3-example
_case2]
0.18s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_4-example
_case26]
0.17s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_10-exampl
e_case9]
0.17s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_5-example
_case27]
0.16s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_8-example
_case30]
0.16s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_2-example
_case1]
0.15s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_4-example
_case3]
0.13s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_15-exampl
e_case14]
0.13s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_21-exampl
e_case20]
0.13s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_8-example
_case7]
0.13s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_25-exampl
e_case22]
0.12s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_7-example
_case6]
0.12s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_9-example
_case8]
0.12s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_12-exampl
e_case34]
0.10s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_CM_18-exampl
e_case17]
0.10s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_14-exampl
e_case36]
0.10s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_10-exampl
e_case32]
0.09s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_2-example
_case24]
0.09s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_13-exampl
e_case35]
0.09s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_11-exampl
e_case33]
0.07s call     src/model_checker/theory_lib/logos/subtheories/counterfactual/tes
ts/test_counterfactual_examples.py::test_counterfactual_examples[CF_TH_1-example
_case23]

(74 durations < 0.005s hidden.  Use -vv to show these durations.)
============================= 37 passed in 11.31s ==============================
      Testing extensional subtheory examples
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 14 items                                                             

src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_CM_1-example_case0] PASSED [  7%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_CM_2-example_case1] PASSED [ 14%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_1-example_case2] PASSED [ 21%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_2-example_case3] PASSED [ 28%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_3-example_case4] PASSED [ 35%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_4-example_case5] PASSED [ 42%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_5-example_case6] PASSED [ 50%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_6-example_case7] PASSED [ 57%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_7-example_case8] PASSED [ 64%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_8-example_case9] PASSED [ 71%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_9-example_case10] PASSED [ 78%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_10-example_case11] PASSED [ 85%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_11-example_case12] PASSED [ 92%]
src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensiona
l_examples.py::test_extensional_examples[EXT_TH_12-example_case13] PASSED [100%]

============================== slowest durations ===============================
0.07s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_CM_2-example_case1]
0.06s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_CM_1-example_case0]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_3-example_case4]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_9-example_case10]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_10-example_case11
]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_7-example_case8]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_2-example_case3]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_1-example_case2]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_8-example_case9]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_4-example_case5]
0.03s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_6-example_case7]
0.02s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_5-example_case6]
0.02s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_12-example_case13
]
0.01s call     src/model_checker/theory_lib/logos/subtheories/extensional/tests/
test_extensional_examples.py::test_extensional_examples[EXT_TH_11-example_case12
]

(28 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 14 passed in 2.09s ==============================
      Testing constitutive subtheory examples
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 34 items                                                             

src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_1-example_case0] PASSED [  2%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_2-example_case1] PASSED [  5%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_3-example_case2] PASSED [  8%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_4-example_case3] PASSED [ 11%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_5-example_case4] PASSED [ 14%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_6-example_case5] PASSED [ 17%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_7-example_case6] PASSED [ 20%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_8-example_case7] PASSED [ 23%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_9-example_case8] PASSED [ 26%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_10-example_case9] PASSED [ 29%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_11-example_case10] PASSED [ 32
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_12-example_case11] PASSED [ 35
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_13-example_case12] PASSED [ 38
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_CM_14-example_case13] PASSED [ 41
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_1-example_case14] PASSED [ 44%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_2-example_case15] PASSED [ 47%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_3-example_case16] PASSED [ 50%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_4-example_case17] PASSED [ 52%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_5-example_case18] PASSED [ 55%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_6-example_case19] PASSED [ 58%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_7-example_case20] PASSED [ 61%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_8-example_case21] PASSED [ 64%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_9-example_case22] PASSED [ 67%
]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_10-example_case23] PASSED [ 70
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_11-example_case24] PASSED [ 73
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_12-example_case25] PASSED [ 76
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_13-example_case26] PASSED [ 79
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_14-example_case27] PASSED [ 82
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_15-example_case28] PASSED [ 85
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_16-example_case29] PASSED [ 88
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_17-example_case30] PASSED [ 91
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_18-example_case31] PASSED [ 94
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_19-example_case32] PASSED [ 97
%]
src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitut
ive_examples.py::test_constitutive_examples[CL_TH_20-example_case33] PASSED [100
%]

============================== slowest durations ===============================
2.03s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_12-example_case
25]
2.00s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_13-example_case
26]
1.04s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_10-example_case
23]
1.00s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_11-example_case
24]
0.62s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_20-example_case
33]
0.37s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_3-example_case2
]
0.36s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_5-example_case4
]
0.33s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_6-example_case5
]
0.17s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_1-example_case0
]
0.15s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_12-example_case
11]
0.14s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_11-example_case
10]
0.13s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_8-example_case7
]
0.13s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_2-example_case1
]
0.13s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_7-example_case6
]
0.12s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_3-example_case1
6]
0.12s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_6-example_case1
9]
0.11s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_4-example_case1
7]
0.11s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_5-example_case1
8]
0.09s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_4-example_case3
]
0.09s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_14-example_case
13]
0.09s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_13-example_case
12]
0.07s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_2-example_case1
5]
0.07s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_14-example_case
27]
0.07s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_15-example_case
28]
0.07s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_1-example_case1
4]
0.06s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_9-example_case2
2]
0.06s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_7-example_case2
0]
0.06s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_8-example_case2
1]
0.04s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_10-example_case
9]
0.04s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_CM_9-example_case8
]
0.03s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_19-example_case
32]
0.03s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_18-example_case
31]
0.02s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_17-example_case
30]
0.02s call     src/model_checker/theory_lib/logos/subtheories/constitutive/tests
/test_constitutive_examples.py::test_constitutive_examples[CL_TH_16-example_case
29]

(68 durations < 0.005s hidden.  Use -vv to show these durations.)
============================= 34 passed in 11.81s ==============================
      Testing relevance subtheory examples
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 20 items                                                             

src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_1-example_case0] PASSED [  5%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_2-example_case1] PASSED [ 10%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_3-example_case2] PASSED [ 15%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_4-example_case3] PASSED [ 20%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_5-example_case4] PASSED [ 25%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_6-example_case5] PASSED [ 30%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_7-example_case6] PASSED [ 35%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_8-example_case7] PASSED [ 40%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_9-example_case8] PASSED [ 45%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_10-example_case9] PASSED [ 50%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_CM_11-example_case10] PASSED [ 55%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_1-example_case11] PASSED [ 60%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_2-example_case12] PASSED [ 65%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_3-example_case13] PASSED [ 70%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_4-example_case14] PASSED [ 75%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_5-example_case15] PASSED [ 80%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_6-example_case16] PASSED [ 85%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_7-example_case17] PASSED [ 90%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_8-example_case18] PASSED [ 95%]
src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_ex
amples.py::test_relevance_examples[REL_TH_9-example_case19] PASSED [100%]

============================== slowest durations ===============================
0.13s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_9-example_case8]
0.13s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_8-example_case7]
0.12s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_1-example_case0]
0.08s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_10-example_case9]
0.07s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_11-example_case10]
0.07s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_1-example_case11]
0.06s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_6-example_case16]
0.06s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_5-example_case15]
0.06s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_3-example_case2]
0.05s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_3-example_case13]
0.05s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_6-example_case5]
0.05s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_2-example_case12]
0.05s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_4-example_case14]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_4-example_case3]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_5-example_case4]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_2-example_case1]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_CM_7-example_case6]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_9-example_case19]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_8-example_case18]
0.04s call     src/model_checker/theory_lib/logos/subtheories/relevance/tests/te
st_relevance_examples.py::test_relevance_examples[REL_TH_7-example_case17]

(40 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 20 passed in 2.88s ==============================

Running unit tests for theories: bimodal, logos
  Running unit tests for bimodal
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 91 items / 16 deselected / 75 selected                               

src/model_checker/theory_lib/bimodal/tests/integration/test_api_consistency.py::
test_find_truth_condition_consistency PASSED [  1%]
src/model_checker/theory_lib/bimodal/tests/integration/test_api_consistency.py::
test_bimodal_proposition_extension_correct_args PASSED [  2%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_evaluation_world PASSED [  4%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_propositions PASSED [  5%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_propositions_no_syntax PASSED [  6%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_relations PASSED [  8%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_states PASSED [  9%]
src/model_checker/theory_lib/bimodal/tests/integration/test_data_extraction.py::
TestBimodalDataExtraction::test_extract_states_no_histories PASSED [ 10%]
src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py::TestBi
modalInjection::test_inject_basic_constraints PASSED [ 12%]
src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py::TestBi
modalInjection::test_inject_task_constraints PASSED [ 13%]
src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py::TestBi
modalInjection::test_inject_truth_condition_constraints PASSED [ 14%]
src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py::TestBi
modalInjection::test_inject_z3_model_values_exists PASSED [ 16%]
src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py::TestBi
modalInjection::test_uses_model_validator PASSED [ 17%]
src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py::test_bas
ic_iteration PASSED [ 18%]
src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py::test_bim
odal_specific_differences PASSED [ 20%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestForAllTi
me::test_foralltime_signature PASSED [ 21%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestForAllTi
me::test_foralltime_wraps_validity PASSED [ 22%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestForAllTi
me::test_foralltime_structure PASSED [ 24%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestExistsTi
me::test_existstime_signature PASSED [ 25%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestExistsTi
me::test_existstime_wraps_validity PASSED [ 26%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestExistsTi
me::test_existstime_structure PASSED [ 28%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestTemporal
OperatorsUsage::test_future_operator_structure_uses_quantifier PASSED [ 29%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestTemporal
OperatorsUsage::test_future_operator_false_structure_uses_quantifier PASSED [ 30
%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestTemporal
OperatorsUsage::test_past_operator_structure_uses_quantifier PASSED [ 32%]
src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py::TestTemporal
OperatorsUsage::test_past_operator_false_structure_uses_quantifier PASSED [ 33%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_witness_registry_initialized PASSED
 [ 34%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_witness_registry_correct_type PASSE
D [ 36%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_witness_registry_has_correct_parame
ters PASSED [ 37%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_constraint_generator_initialized PA
SSED [ 38%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_constraint_generator_correct_type P
ASSED [ 40%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessComponentsInitialization::test_constraint_generator_has_semantics_
reference PASSED [ 41%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestFormulaStringConversion::test_has_formula_string_method PASSED [ 42%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestFormulaStringConversion::test_formula_string_callable PASSED [ 44%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestFormulaStringConversion::test_formula_string_simple_sentence PASSED [ 45%
]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestFormulaStringConversion::test_formula_string_box_operator PASSED [ 46%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessRegistration::test_can_register_witness_manually PASSED [ 48%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestWitnessRegistration::test_can_generate_constraints_for_registered_witness
 PASSED [ 49%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestNegationUnchanged::test_negation_operator_exists PASSED [ 50%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestNegationUnchanged::test_negation_has_simple_semantics PASSED [ 52%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestRegressionBasic::test_semantics_initialization_succeeds PASSED [ 53%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestRegressionBasic::test_has_necessary_semantic_methods PASSED [ 54%]
src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.p
y::TestRegressionBasic::test_frame_constraints_still_generated PASSED [ 56%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tInitialization::test_initialization_stores_semantics PASSED [ 57%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tInitialization::test_initialization_stores_N PASSED [ 58%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tInitialization::test_initialization_stores_M PASSED [ 60%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tGenerateWitnessConstraints::test_generate_returns_list PASSED [ 61%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tGenerateWitnessConstraints::test_generate_returns_z3_constraints PASSED [ 62%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tGenerateWitnessConstraints::test_generate_empty_formula_raises_error PASSED [ 6
4%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tGenerateWitnessConstraints::test_generate_none_predicate_raises_error PASSED [ 
65%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tConstraintStructure::test_constraints_contain_forall PASSED [ 66%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tConstraintStructure::test_constraints_reference_predicate PASSED [ 68%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tConstraintStructure::test_constraints_use_implies PASSED [ 69%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tSemanticReferences::test_constraints_reference_is_world PASSED [ 70%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tSemanticReferences::test_constraints_check_time_validity PASSED [ 72%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py::Tes
tMultipleFormulas::test_different_formulas_different_constraints PASSED [ 73%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestIn
itialization::test_initialization_stores_parameters PASSED [ 74%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestIn
itialization::test_initialization_empty_dicts PASSED [ 76%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_single_predicate PASSED [ 77%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_predicate_signature PASSED [ 78%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_predicate_naming_convention PASSED [ 80%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_multiple_formulas PASSED [ 81%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_same_formula_twice_raises_error PASSED [ 8
2%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_empty_formula_raises_error PASSED [ 84%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestRe
gisterWitnessPredicate::test_register_stores_in_all_structures PASSED [ 85%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tWitnessPredicate::test_get_registered_predicate PASSED [ 86%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tWitnessPredicate::test_get_predicate_uses_cache PASSED [ 88%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tWitnessPredicate::test_get_unregistered_predicate_raises_error PASSED [ 89%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestHa
sWitnessPredicate::test_has_predicate_existing_returns_true PASSED [ 90%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestHa
sWitnessPredicate::test_has_predicate_nonexistent_returns_false PASSED [ 92%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestHa
sWitnessPredicate::test_has_predicate_no_error PASSED [ 93%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tAllPredicates::test_get_all_predicates_empty PASSED [ 94%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tAllPredicates::test_get_all_predicates_returns_copy PASSED [ 96%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestGe
tAllPredicates::test_get_all_predicates_contents PASSED [ 97%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestCl
ear::test_clear_empties_all_structures PASSED [ 98%]
src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py::TestCl
ear::test_clear_allows_reregistration PASSED [100%]

============================== slowest durations ===============================
0.25s call     src/model_checker/theory_lib/bimodal/tests/integration/test_injec
tion.py::TestBimodalInjection::test_inject_truth_condition_constraints
0.23s call     src/model_checker/theory_lib/bimodal/tests/integration/test_injec
tion.py::TestBimodalInjection::test_inject_task_constraints
0.23s call     src/model_checker/theory_lib/bimodal/tests/integration/test_injec
tion.py::TestBimodalInjection::test_inject_basic_constraints
0.21s call     src/model_checker/theory_lib/bimodal/tests/integration/test_injec
tion.py::TestBimodalInjection::test_uses_model_validator
0.21s call     src/model_checker/theory_lib/bimodal/tests/integration/test_injec
tion.py::TestBimodalInjection::test_inject_z3_model_values_exists
0.17s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestTemporalOperatorsUsage::test_past_operator_structure_uses_quantifier
0.16s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestGenerateWitnessConstraints::test_generate_returns_list
0.16s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestFormulaStringConversion::test_formula_string_box_operator
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestInitialization::test_initialization_stores_M
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestExistsTime::test_existstime_wraps_validity
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestFormulaStringConversion::test_formula_string_simple_senten
ce
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestTemporalOperatorsUsage::test_past_operator_false_structure_uses_quantifie
r
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestForAllTime::test_foralltime_wraps_validity
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestFormulaStringConversion::test_formula_string_callable
0.15s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessRegistration::test_can_generate_constraints_for_reg
istered_witness
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestConstraintStructure::test_constraints_use_implies
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestInitialization::test_initialization_stores_N
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestExistsTime::test_existstime_signature
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestSemanticReferences::test_constraints_reference_is_world
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestTemporalOperatorsUsage::test_future_operator_false_structure_uses_quantif
ier
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestConstraintStructure::test_constraints_reference_predicate
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestGenerateWitnessConstraints::test_generate_none_predicate_raises_
error
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_witness_registry_cor
rect_type
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestMultipleFormulas::test_different_formulas_different_constraints
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestForAllTime::test_foralltime_signature
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestTemporalOperatorsUsage::test_future_operator_structure_uses_quantifier
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestForAllTime::test_foralltime_structure
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestConstraintStructure::test_constraints_contain_forall
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestGenerateWitnessConstraints::test_generate_empty_formula_raises_e
rror
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestGenerateWitnessConstraints::test_generate_returns_z3_constraints
0.14s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestSemanticReferences::test_constraints_check_time_validity
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessRegistration::test_can_register_witness_manually
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_witness_registry_ini
tialized
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_constraint_generator
_initialized
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestFormulaStringConversion::test_has_formula_string_method
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_witness_registry_has
_correct_parameters
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_constraint_generator
_has_semantics_reference
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestWitnessComponentsInitialization::test_constraint_generator
_correct_type
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestInitialization::test_initialization_stores_semantics
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestRegressionBasic::test_semantics_initialization_succeeds
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestRegressionBasic::test_frame_constraints_still_generated
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.p
y::TestExistsTime::test_existstime_structure
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestNegationUnchanged::test_negation_has_simple_semantics
0.13s setup    src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnes
s_integration.py::TestRegressionBasic::test_has_necessary_semantic_methods
0.01s call     src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cons
traints.py::TestMultipleFormulas::test_different_formulas_different_constraints

(180 durations < 0.005s hidden.  Use -vv to show these durations.)
====================== 75 passed, 16 deselected in 8.40s =======================
  Running unit tests for logos
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 361 items / 278 deselected / 83 selected                             

src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_inject_possible_constraints PASSED [  1%]
src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_inject_verify_falsify_constraints PASSED [  2%]
src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_inject_world_constraints PASSED [  3%]
src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_inject_z3_model_values_exists PASSED [  4%]
src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_no_theory_concepts_leak PASSED [  6%]
src/model_checker/theory_lib/logos/tests/integration/test_injection.py::TestLogo
sInjection::test_uses_z3_eval_directly PASSED [  7%]
src/model_checker/theory_lib/logos/tests/integration/test_iterate.py::TestLogosI
terator::test_basic_iteration PASSED [  8%]
src/model_checker/theory_lib/logos/tests/integration/test_iterate.py::TestLogosI
terator::test_difference_detection PASSED [  9%]
src/model_checker/theory_lib/logos/tests/integration/test_iterate_generator.py::
TestLogosGeneratorInterface::test_logos_generator_interface PASSED [ 10%]
src/model_checker/theory_lib/logos/tests/integration/test_iterate_generator.py::
TestLogosGeneratorInterface::test_generator_marker_present PASSED [ 12%]
src/model_checker/theory_lib/logos/tests/integration/test_iterate_generator.py::
TestLogosGeneratorInterface::test_generator_yields_incrementally PASSED [ 13%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsMethods::test_semantics_method_availability PASSED [ 14%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsMethods::test_world_related_methods PASSED [ 15%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsMethods::test_compatibility_methods PASSED [ 16%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsMethods::test_product_operations PASSED [ 18%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsCalls::test_semantic_method_calls_dont_crash PASSED [ 19%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosSemanticsCalls::test_alternative_world_calculation PASSED [ 20%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosOperatorRegistryMethods::test_registry_management_methods PASSED [ 21%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosOperatorRegistryMethods::test_operator_access_methods PASSED [ 22%]
src/model_checker/theory_lib/logos/tests/integration/test_semantic_coverage.py::
TestLogosOperatorRegistryMethods::test_operator_validation_methods PASSED [ 24%]
src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py::
TestSolverSwitching::test_z3_available PASSED [ 25%]
src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py::
TestSolverSwitching::test_cvc5_available PASSED [ 26%]
src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py::
TestSolverSwitching::test_switch_to_z3 PASSED [ 27%]
src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py::
TestSolverSwitching::test_switch_to_cvc5 PASSED [ 28%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_all_subtheories_loadable PASSED [ 30%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_subtheory_protocol_compliance PASSED [ 31
%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_operator_protocol_compliance PASSED [ 32%
]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_registry_protocol_compliance PASSED [ 33%
]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_semantics_protocol_compliance PASSED [ 34
%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_dependency_resolution PASSED [ 36%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_no_operator_conflicts PASSED [ 37%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass PASSED [ 38%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_iterator_contract_compliance PASSED [ 39%
]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestSubtheoryOrchestration::test_type_hint_coverage PASSED [ 40%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestProtocolDefinitions::test_protocols_importable PASSED [ 42%]
src/model_checker/theory_lib/logos/tests/integration/test_subtheory_orchestratio
n.py::TestProtocolDefinitions::test_protocol_runtime_checking PASSED [ 43%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestExtensional
Operators::test_extensional_operators_available PASSED [ 44%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestExtensional
Operators::test_operator_properties PASSED [ 45%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestExtensional
Operators::test_negation_operator PASSED [ 46%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestExtensional
Operators::test_binary_operators PASSED [ 48%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestModalOperat
ors::test_modal_operators_available PASSED [ 49%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestModalOperat
ors::test_necessity_operator PASSED [ 50%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestModalOperat
ors::test_possibility_operator PASSED [ 51%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestOperatorSem
anticClauses::test_semantic_clause_structure PASSED [ 53%]
src/model_checker/theory_lib/logos/tests/unit/test_operators.py::TestOperatorSem
anticClauses::test_semantic_clause_execution PASSED [ 54%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
PredicateExtensionOutput::test_predicate_extension_header_appears PASSED [ 55%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
PredicateExtensionOutput::test_predicate_name_appears_in_output PASSED [ 56%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
PredicateExtensionOutput::test_domain_elements_formatted_correctly PASSED [ 57%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
PrintImpossibleSetting::test_print_impossible_false_excludes_impossible_states P
ASSED [ 59%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
BinaryPredicates::test_binary_predicate_enumerates_all_pairs PASSED [ 60%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
HelperMethod::test_get_predicate_extension_returns_tuple PASSED [ 61%]
src/model_checker/theory_lib/logos/tests/unit/test_predicate_extensions.py::Test
OutputFormat::test_output_format_matches_proposition_format PASSED [ 62%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onCreation::test_proposition_creation_valid_args PASSED [ 63%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onCreation::test_proposition_creation_invalid_args PASSED [ 65%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onCreation::test_proposition_attributes PASSED [ 66%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onConstraints::test_proposition_constraints_method PASSED [ 67%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onConstraints::test_constraint_generation_structure PASSED [ 68%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onIntegration::test_proposition_model_integration PASSED [ 69%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onIntegration::test_proposition_sentence_integration PASSED [ 71%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onUtilities::test_proposition_string_representation PASSED [ 72%]
src/model_checker/theory_lib/logos/tests/unit/test_proposition.py::TestPropositi
onUtilities::test_proposition_equality PASSED [ 73%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestRegistryBasi
cs::test_registry_creation PASSED [ 74%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestRegistryBasi
cs::test_registry_initial_state PASSED [ 75%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestSubtheoryLoa
ding::test_load_single_subtheory PASSED [ 77%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestSubtheoryLoa
ding::test_load_multiple_subtheories PASSED [ 78%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestSubtheoryLoa
ding::test_incremental_loading PASSED [ 79%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestDependencyRe
solution::test_automatic_dependency_resolution PASSED [ 80%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestDependencyRe
solution::test_dependency_chain_resolution PASSED [ 81%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestOperatorAcce
ss::test_operator_retrieval PASSED [ 83%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestOperatorAcce
ss::test_operator_collection_structure PASSED [ 84%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestErrorHandlin
g::test_invalid_subtheory_handling PASSED [ 85%]
src/model_checker/theory_lib/logos/tests/unit/test_registry.py::TestErrorHandlin
g::test_empty_subtheory_list PASSED [ 86%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestLogo
sSemanticInstantiation::test_semantics_creation_valid_settings PASSED [ 87%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestLogo
sSemanticInstantiation::test_semantics_missing_required_settings PASSED [ 89%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestLogo
sSemanticInstantiation::test_semantics_invalid_settings PASSED [ 90%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticPrimitives::test_verify_falsify_functions PASSED [ 91%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticPrimitives::test_possible_function PASSED [ 92%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticPrimitives::test_main_world_creation PASSED [ 93%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticOperations::test_fusion_operation PASSED [ 95%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticOperations::test_parthood_operations PASSED [ 96%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestSema
nticOperations::test_compatibility_operations PASSED [ 97%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestFram
eConstraints::test_frame_constraints_generation PASSED [ 98%]
src/model_checker/theory_lib/logos/tests/unit/test_semantic_methods.py::TestFram
eConstraints::test_frame_constraints_structure PASSED [100%]

============================== slowest durations ===============================
35.50s call     src/model_checker/theory_lib/logos/tests/integration/test_subthe
ory_orchestration.py::TestSubtheoryOrchestration::test_all_subtheory_tests_pass
10.04s call     src/model_checker/theory_lib/logos/tests/integration/test_iterat
e_generator.py::TestLogosGeneratorInterface::test_generator_yields_incrementally
0.80s call     src/model_checker/theory_lib/logos/tests/integration/test_iterate
_generator.py::TestLogosGeneratorInterface::test_logos_generator_interface
0.05s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestBinaryPredicates::test_binary_predicate_enumerates_all_pairs
0.04s call     src/model_checker/theory_lib/logos/tests/integration/test_iterate
.py::TestLogosIterator::test_difference_detection
0.04s call     src/model_checker/theory_lib/logos/tests/integration/test_injecti
on.py::TestLogosInjection::test_inject_verify_falsify_constraints
0.03s call     src/model_checker/theory_lib/logos/tests/integration/test_injecti
on.py::TestLogosInjection::test_inject_possible_constraints
0.02s call     src/model_checker/theory_lib/logos/tests/integration/test_injecti
on.py::TestLogosInjection::test_inject_world_constraints
0.02s call     src/model_checker/theory_lib/logos/tests/integration/test_iterate
.py::TestLogosIterator::test_basic_iteration
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestHelperMethod::test_get_predicate_extension_returns_tuple
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestPredicateExtensionOutput::test_predicate_name_appears_in_output
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestPredicateExtensionOutput::test_predicate_extension_header_appears
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestPrintImpossibleSetting::test_print_impossible_false_excludes_impo
ssible_states
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestPredicateExtensionOutput::test_domain_elements_formatted_correctl
y
0.02s call     src/model_checker/theory_lib/logos/tests/unit/test_predicate_exte
nsions.py::TestOutputFormat::test_output_format_matches_proposition_format
0.01s call     src/model_checker/theory_lib/logos/tests/unit/test_proposition.py
::TestPropositionConstraints::test_constraint_generation_structure
0.01s call     src/model_checker/theory_lib/logos/tests/integration/test_injecti
on.py::TestLogosInjection::test_uses_z3_eval_directly
0.01s call     src/model_checker/theory_lib/logos/tests/integration/test_subtheo
ry_orchestration.py::TestSubtheoryOrchestration::test_semantics_protocol_complia
nce

(231 durations < 0.005s hidden.  Use -vv to show these durations.)
===================== 83 passed, 278 deselected in 47.81s ======================

Running package tests for components: builder, iterate, jupyter, models, output,
 output.notebook, settings, solver, syntactic, theory_lib, utils
  Running package tests for builder
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 263 items                                                            

src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::tes
t_error_handling PASSED [  0%]
src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::tes
t_iteration_workflow PASSED [  0%]
src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::tes
t_theory_library_execution PASSED [  1%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestProjectGener
ationEdgeCases::test_project_generation_creates_multiple_projects_independently 
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestProjectGener
ationEdgeCases::test_project_generation_creates_multiple_projects_independently 
PASSED [  1%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestProjectGener
ationEdgeCases::test_project_generation_handles_directories_with_spaces_correctl
y PASSED [  1%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestProjectGener
ationEdgeCases::test_project_generation_handles_special_character_names_correctl
y 
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestProjectGener
ationEdgeCases::test_project_generation_handles_special_character_names_correctl
y PASSED [  2%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestModuleLoadin
gBoundaryConditions::test_module_loading_handles_missing_required_attributes_gra
cefully PASSED [  2%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestModuleLoadin
gBoundaryConditions::test_module_loading_handles_nonexistent_file_with_descripti
ve_error PASSED [  3%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestModuleLoadin
gBoundaryConditions::test_module_loading_handles_syntax_errors_with_descriptive_
error PASSED [  3%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestSystemPathIs
olationBehavior::test_sys_path_modifications_do_not_interfere_between_operations
 PASSED [  3%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestPerformanceA
ndScalabilityScenarios::test_multiple_project_generation_completes_within_reason
able_time PASSED [  4%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestPerformanceA
ndScalabilityScenarios::test_repeated_project_operations_maintain_consistent_per
formance PASSED [  4%]
src/model_checker/builder/tests/e2e/test_project_edge_cases.py::TestCompleteUser
WorkflowSimulation::test_complete_cli_workflow_simulation_executes_successfully 
PASSED [  4%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_flag_overrides PASSED [  5%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_generated_project_detection PASSED [  5%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_module_initialization_bimodal PASSED [  6%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_module_initialization_logos PASSED [  6%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_module_missing_attributes PASSED [  6%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_package_detection PASSED [  7%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_process_example_error_handling PASSED [  7%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_run_model_check_bimodal PASSED [  7%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_run_model_check_logos PASSED [  8%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_translate_example_method PASSED [  8%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModule::test_translate_method PASSED [  9%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModuleIntegration::test_bimodal_theory_integration PASSED [  9%]
src/model_checker/builder/tests/integration/test_build_module_theories.py::TestB
uildModuleIntegration::test_logos_theory_integration PASSED [  9%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestCLIInteractiveFlagIntegration::test_interactive_flag_bypasses_mode_promptin
g_correctly PASSED [ 10%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestCLIInteractiveFlagIntegration::test_interactive_flag_handles_missing_output
_configuration_gracefully PASSED [ 10%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestCLIInteractiveFlagIntegration::test_interactive_flag_integration_with_batch
_mode_settings PASSED [ 11%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestCLIInteractiveFlagIntegration::test_no_interactive_flag_prompts_user_for_mo
de_selection PASSED [ 11%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestInteractiveFlagEdgeCases::test_interactive_flag_behavior_with_empty_example
_range PASSED [ 11%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestInteractiveFlagEdgeCases::test_interactive_flag_with_conflicting_configurat
ion_resolves_appropriately PASSED [ 12%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestInteractiveFlagEdgeCases::test_interactive_flag_with_invalid_module_produce
s_clear_error PASSED [ 12%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestInteractiveModeUserExperience::test_interactive_mode_integration_with_real_
user_workflow PASSED [ 12%]
src/model_checker/builder/tests/integration/test_cli_interactive_integration.py:
:TestInteractiveModeUserExperience::test_interactive_mode_provides_appropriate_u
ser_feedback PASSED [ 13%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestL
oaderRunnerIntegration::test_loader_runner_workflow_processes_examples_correctly
 PASSED [ 13%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestL
oaderRunnerIntegration::test_loader_translation_integration_applies_dictionaries
 PASSED [ 14%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestM
oduleTheoryIntegration::test_module_loads_multiple_theories_correctly PASSED [ 1
4%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestM
oduleTheoryIntegration::test_module_theory_validation_integration PASSED [ 14%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestC
omparisonIntegration::test_comparison_mode_integration_with_multiple_theories PA
SSED [ 15%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestT
ranslationIntegration::test_translation_integration_with_example_processing PASS
ED [ 15%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestT
ranslationIntegration::test_translation_integration_with_multiple_theory_diction
aries PASSED [ 15%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestS
ystemIntegration::test_complete_system_initialization_succeeds PASSED [ 16%]
src/model_checker/builder/tests/integration/test_component_integration.py::TestS
ystemIntegration::test_error_propagation_through_system_integration PASSED [ 16%
]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestModul
eLoadingErrorPropagation::test_module_loader_propagates_file_not_found_error_wit
h_context PASSED [ 17%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestModul
eLoadingErrorPropagation::test_module_loader_propagates_import_errors_from_modul
e_dependencies PASSED [ 17%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestModul
eLoadingErrorPropagation::test_module_loader_propagates_missing_attribute_errors
_descriptively PASSED [ 17%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestModul
eLoadingErrorPropagation::test_module_loader_propagates_syntax_errors_with_locat
ion_info PASSED [ 18%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestTheor
yDiscoveryErrorPropagation::test_theory_discovery_error_includes_available_theor
ies_suggestion PASSED [ 18%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestTheor
yDiscoveryErrorPropagation::test_theory_discovery_propagates_unknown_theory_erro
rs_clearly PASSED [ 19%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestCompo
nentIntegrationErrorPropagation::test_build_module_propagates_component_initiali
zation_errors_appropriately PASSED [ 19%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestCompo
nentIntegrationErrorPropagation::test_error_propagation_preserves_original_error
_context PASSED [ 19%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestError
RecoveryAndGracefulDegradation::test_informative_error_messages_help_debugging_c
ommon_issues 
src/model_checker/builder/tests/integration/test_error_propagation.py::TestError
RecoveryAndGracefulDegradation::test_informative_error_messages_help_debugging_c
ommon_issues PASSED [ 20%]
src/model_checker/builder/tests/integration/test_error_propagation.py::TestError
RecoveryAndGracefulDegradation::test_system_recovers_gracefully_from_partial_mod
ule_loading_failures PASSED [ 20%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_backward_compatibility PASSED [ 20%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_default_project_examples_init_loading PASSED [ 21%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_error_handling_for_generated_projects PASSED [ 21%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_find_project_directory PASSED [ 22%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_generated_project_detection PASSED [ 22%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_logos_project_generation_and_loading PASSED [ 22%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestGene
ratedProjectImports::test_sys_path_configuration PASSED [ 23%]
src/model_checker/builder/tests/integration/test_generated_projects.py::TestProj
ectStructureFlexibility::test_multiple_theory_templates 
src/model_checker/builder/tests/integration/test_generated_projects.py::TestProj
ectStructureFlexibility::test_multiple_theory_templates PASSED [ 23%]
src/model_checker/builder/tests/integration/test_interactive.py::TestBuildModule
InteractiveIntegration::test_batch_mode_initialization_skips_interactive_prompts
 PASSED [ 23%]
src/model_checker/builder/tests/integration/test_interactive.py::TestBuildModule
InteractiveIntegration::test_interactive_mode_handles_all_examples_selection PAS
SED [ 24%]
src/model_checker/builder/tests/integration/test_interactive.py::TestBuildModule
InteractiveIntegration::test_interactive_mode_initialization_creates_manager_cor
rectly PASSED [ 24%]
src/model_checker/builder/tests/integration/test_interactive.py::TestBuildModule
InteractiveIntegration::test_interactive_mode_integrates_with_real_example_proce
ssing PASSED [ 25%]
src/model_checker/builder/tests/integration/test_interactive.py::TestBuildModule
InteractiveIntegration::test_interactive_save_manager_integration_with_output_di
rectory PASSED [ 25%]
src/model_checker/builder/tests/integration/test_interactive.py::TestInteractive
ErrorHandling::test_interactive_mode_handles_invalid_user_input_gracefully PASSE
D [ 25%]
src/model_checker/builder/tests/integration/test_interactive.py::TestInteractive
ErrorHandling::test_interactive_mode_handles_output_manager_initialization_error
s PASSED [ 26%]
src/model_checker/builder/tests/integration/test_interactive.py::TestInteractive
WorkflowIntegration::test_complete_interactive_workflow_processes_multiple_examp
les PASSED [ 26%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputDirectoryGuidanceIntegration::test_batch_mode_output_guidance_provides_
command_line_instructions PASSED [ 26%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputDirectoryGuidanceIntegration::test_build_module_provides_output_directo
ry_guidance_when_saving PASSED [ 27%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputDirectoryGuidanceIntegration::test_output_directory_guidance_handles_no
nexistent_directories_gracefully PASSED [ 27%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estInteractiveOutputDirectoryIntegration::test_interactive_mode_integrates_outpu
t_directory_prompts_correctly PASSED [ 28%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estInteractiveOutputDirectoryIntegration::test_output_directory_guidance_adapts_
to_user_preferences 
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estInteractiveOutputDirectoryIntegration::test_output_directory_guidance_adapts_
to_user_preferences PASSED [ 28%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputGuidanceErrorHandling::test_output_guidance_handles_invalid_directory_p
aths_informatively 
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputGuidanceErrorHandling::test_output_guidance_handles_invalid_directory_p
aths_informatively PASSED [ 28%]
src/model_checker/builder/tests/integration/test_output_directory_guidance.py::T
estOutputGuidanceErrorHandling::test_output_guidance_handles_permission_denied_d
irectories_gracefully PASSED [ 29%]
src/model_checker/builder/tests/integration/test_package_imports.py::TestPackage
Imports::test_package_detection_methods_exist PASSED [ 29%]
src/model_checker/builder/tests/integration/test_package_imports.py::TestPackage
Imports::test_package_marker_now_exists PASSED [ 30%]
src/model_checker/builder/tests/integration/test_package_imports.py::TestPackage
Imports::test_relative_imports_now_work_with_package PASSED [ 30%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_comparison_mode_performance PASSED [ 30%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_constraint_generation_scales_linearly PASSED [ 31%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_large_model_generation_completes_within_timeout PASSED [ 31%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_medium_model_generation_completes_within_timeout PASSED [ 31%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_module_loading_performance PASSED [ 32%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_multiple_examples_process_efficiently PASSED [ 32%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_serialization_performance PASSED [ 33%]
src/model_checker/builder/tests/integration/test_performance.py::TestBuilderPerf
ormance::test_small_model_generation_completes_quickly PASSED [ 33%]
src/model_checker/builder/tests/integration/test_performance.py::TestMemoryUsage
::test_memory_usage_stays_within_bounds PASSED [ 33%]
src/model_checker/builder/tests/integration/test_performance.py::TestMemoryUsage
::test_no_memory_leaks_in_iteration PASSED [ 34%]
src/model_checker/builder/tests/integration/test_workflow.py::TestUserWorkflowIn
tegration::test_multiple_project_creation_workflow_handles_conflicts PASSED [ 34
%]
src/model_checker/builder/tests/integration/test_workflow.py::TestUserWorkflowIn
tegration::test_project_creation_and_module_loading_workflow_succeeds PASSED [ 3
4%]
src/model_checker/builder/tests/integration/test_workflow.py::TestUserWorkflowIn
tegration::test_snake_project_scenario_resolution PASSED [ 35%]
src/model_checker/builder/tests/integration/test_workflow.py::TestBuildModuleInt
egration::test_build_module_handles_comparison_mode_integration PASSED [ 35%]
src/model_checker/builder/tests/integration/test_workflow.py::TestBuildModuleInt
egration::test_build_module_loads_real_module_with_all_components PASSED [ 36%]
src/model_checker/builder/tests/integration/test_workflow.py::TestEndToEndScenar
ios::test_complete_user_session_from_creation_to_execution PASSED [ 36%]
src/model_checker/builder/tests/integration/test_workflow.py::TestEndToEndScenar
ios::test_error_recovery_workflow_handles_invalid_projects PASSED [ 36%]
src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73Fix::test_both_
execution_paths_work PASSED [ 37%]
src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73Fix::test_handl
e_example_script_simulation PASSED [ 37%]
src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73Fix::test_loade
r_handles_generated_packages PASSED [ 38%]
src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73Fix::test_proje
ct_creation_and_example_execution PASSED [ 38%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_buildmodule_with_package PASSED [ 38%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_direct_package_import PASSED [ 39%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_generated_project_detection PASSED [ 39%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_package_import_setup PASSED [ 39%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_package_root_finding PASSED [ 40%]
src/model_checker/builder/tests/test_package_loading.py::TestPackageLoading::tes
t_relative_imports_work PASSED [ 40%]
src/model_checker/builder/tests/test_package_loading.py::TestSubprocessExecution
::test_pythonpath_setup_in_subprocess PASSED [ 41%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_clean_constructor PASSED [ 41%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_clean_loader_exists PASSED [ 41%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_clear_error_messages_with_context PASSED [ 42%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_fail_fast_validation PASSED [ 42%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_no_circular_dependencies PASSED [ 42%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_no_config_py_support PASSED [ 43%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_no_legacy_detection_methods PASSED [ 43%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_no_optional_parameters PASSED [ 44%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_only_modelchecker_marker_support PASSED [ 44%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_performance_improvement PASSED [ 44%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_permanent_sys_path_changes PASSED [ 45%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_separated_detector_class_exists PASSED [ 45%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_simplified_code_structure PASSED [ 46%]
src/model_checker/builder/tests/test_refactoring_target_behavior.py::TestTargetL
oaderBehavior::test_strategy_pattern_for_imports PASSED [ 46%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonCore
::test_model_comparison_has_required_interface_methods PASSED [ 46%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonCore
::test_model_comparison_initializes_with_valid_build_module PASSED [ 47%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonExec
ution::test_model_comparison_compares_semantics_successfully PASSED [ 47%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonExec
ution::test_model_comparison_handles_multiple_example_theories PASSED [ 47%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonInte
gration::test_build_module_enables_comparison_mode_correctly PASSED [ 48%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonInte
gration::test_build_module_integrates_with_comparison_after_refactoring PASSED [
 48%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonErro
rHandling::test_model_comparison_handles_empty_theory_list_gracefully PASSED [ 4
9%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonErro
rHandling::test_model_comparison_handles_invalid_build_module_gracefully PASSED 
[ 49%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonErro
rHandling::test_model_comparison_handles_malformed_theory_tuples 
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonErro
rHandling::test_model_comparison_handles_malformed_theory_tuples PASSED [ 49%]
src/model_checker/builder/tests/unit/test_comparison.py::TestModelComparisonResu
ltAnalysis::test_model_comparison_formats_results_correctly PASSED [ 50%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleBasic::tes
t_build_example_comparison_mode PASSED [ 50%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleBasic::tes
t_build_example_get_result PASSED [ 50%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleBasic::tes
t_build_example_initialization PASSED [ 51%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleBasic::tes
t_build_example_print_model PASSED [ 51%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleBasic::tes
t_build_example_with_no_model PASSED [ 52%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleErrorHandl
ing::test_get_result_without_model_check PASSED [ 52%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleErrorHandl
ing::test_invalid_example_structure PASSED [ 52%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleErrorHandl
ing::test_invalid_theory_structure PASSED [ 53%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegratio
n::test_find_next_model_basic PASSED [ 53%]
src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegratio
n::test_logos_extensional_theory PASSED [ 53%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderCore::test_
module_loader_initializes_with_valid_parameters PASSED [ 54%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderCore::test_
module_loader_loads_module_with_correct_attributes PASSED [ 54%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderCore::test_
module_loader_loads_valid_module_successfully PASSED [ 55%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderErrorHandli
ng::test_module_loader_handles_import_errors_in_module_content PASSED [ 55%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderErrorHandli
ng::test_module_loader_handles_syntax_errors_appropriately PASSED [ 55%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderErrorHandli
ng::test_module_loader_raises_import_error_when_file_not_found PASSED [ 56%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderErrorHandli
ng::test_module_loader_validates_required_module_attributes PASSED [ 56%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderTheoryDisco
very::test_module_loader_discovers_theory_module_successfully PASSED [ 57%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderTheoryDisco
very::test_module_loader_raises_error_for_unknown_theory PASSED [ 57%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderEdgeCases::
test_module_loader_handles_empty_module_files PASSED [ 57%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderEdgeCases::
test_module_loader_handles_unicode_in_module_paths PASSED [ 58%]
src/model_checker/builder/tests/unit/test_loader.py::TestModuleLoaderEdgeCases::
test_module_loader_handles_very_long_file_paths PASSED [ 58%]
src/model_checker/builder/tests/unit/test_package_marker.py::TestPackageMarker::
test_marker_creation_with_metadata PASSED [ 58%]
src/model_checker/builder/tests/unit/test_package_marker.py::TestPackageMarker::
test_marker_file_format PASSED [ 59%]
src/model_checker/builder/tests/unit/test_package_marker.py::TestPackageMarker::
test_marker_metadata_content PASSED [ 59%]
src/model_checker/builder/tests/unit/test_package_structure.py::TestPackageStruc
ture::test_init_file_creation PASSED [ 60%]
src/model_checker/builder/tests/unit/test_package_structure.py::TestPackageStruc
ture::test_package_exports_structure PASSED [ 60%]
src/model_checker/builder/tests/unit/test_package_structure.py::TestPackageStruc
ture::test_subpackage_initialization PASSED [ 60%]
src/model_checker/builder/tests/unit/test_progress.py::TestSpinner::test_spinner
_initialization PASSED [ 61%]
src/model_checker/builder/tests/unit/test_progress.py::TestSpinner::test_spinner
_output PASSED [ 61%]
src/model_checker/builder/tests/unit/test_progress.py::TestSpinner::test_spinner
_start_stop PASSED [ 61%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestProgress
BarOrdering::test_complete_handles_already_stopped_thread PASSED [ 62%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestProgress
BarOrdering::test_current_runner_has_wrong_order SKIPPED [ 62%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestProgress
BarOrdering::test_header_printed_before_progress_bar_completion PASSED [ 63%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestProgress
BarOrdering::test_no_model_found_ordering PASSED [ 63%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestProgress
BarOrdering::test_progress_bar_animation_during_z3_search PASSED [ 63%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestUnifiedP
rogressDeferredCompletion::test_manual_thread_stop_then_complete PASSED [ 64%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestUnifiedP
rogressDeferredCompletion::test_stop_animation_without_printing PASSED [ 64%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestBarOutpu
tBarOrdering::test_deferred_completion_preserves_frozen_state PASSED [ 65%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestBarOutpu
tBarOrdering::test_freeze_complete_time_consistency PASSED [ 65%]
src/model_checker/builder/tests/unit/test_progress_bar_ordering.py::TestBarOutpu
tBarOrdering::test_multiple_bars_maintain_independent_frozen_state PASSED [ 65%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_create_project_handles_special_characters_in_name 
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_create_project_handles_special_characters_in_name PASSED [ 66%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_create_project_validates_theory_selection 
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_create_project_validates_theory_selection PASSED [ 66%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_create_project_with_valid_name_succeeds PASSED [ 66%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_generate_template_creates_valid_content PASSED [ 67%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_invalid_theory_raises_error PASSED [ 67%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_logos_project_generation PASSED [ 68%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_project_initialization_default PASSED [ 68%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_project_initialization_logos PASSED [ 68%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectCore::test
_project_initialization_with_subtheories PASSED [ 69%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_create_project_in_readonly_directory_fails_gracefully PASSED [ 69%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_create_project_with_empty_name_raises_error 
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_create_project_with_empty_name_raises_error PASSED [ 69%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_create_project_with_existing_name_handles_appropriately PASSED [ 70%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_create_project_with_very_long_name PASSED [ 70%]
src/model_checker/builder/tests/unit/test_project.py::TestBuildProjectEdgeCases:
:test_generate_multiple_projects_independently PASSED [ 71%]
src/model_checker/builder/tests/unit/test_project_version.py::TestBuildProjectVe
rsionDetection::test_build_project_retrieves_version_information_successfully PA
SSED [ 71%]
src/model_checker/builder/tests/unit/test_project_version.py::TestBuildProjectVe
rsionDetection::test_version_detection_consistency_with_package_version PASSED [
 71%]
src/model_checker/builder/tests/unit/test_project_version.py::TestBuildProjectVe
rsionDetection::test_version_detection_handles_valid_version_format_correctly PA
SSED [ 72%]
src/model_checker/builder/tests/unit/test_project_version.py::TestBuildProjectVe
rsionDetection::test_version_detection_provides_fallback_for_unknown_versions PA
SSED [ 72%]
src/model_checker/builder/tests/unit/test_project_version.py::TestVersionDetecti
onEdgeCases::test_version_detection_handles_different_theory_names_consistently 
PASSED [ 73%]
src/model_checker/builder/tests/unit/test_project_version.py::TestVersionDetecti
onEdgeCases::test_version_detection_performance_is_reasonable PASSED [ 73%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerCore::test_m
odel_runner_has_required_interface_methods PASSED [ 73%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerCore::test_m
odel_runner_initializes_with_valid_build_module PASSED [ 74%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerExecution::t
est_model_runner_executes_model_check_successfully PASSED [ 74%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerExecution::t
est_model_runner_handles_example_processing_correctly PASSED [ 74%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerIntegration:
:test_build_module_integrates_with_runner_after_refactoring PASSED [ 75%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerErrorHandlin
g::test_model_runner_handles_invalid_build_module_gracefully PASSED [ 75%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerErrorHandlin
g::test_model_runner_handles_missing_translation_gracefully PASSED [ 76%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerEdgeCases::t
est_model_runner_handles_empty_example_cases_appropriately PASSED [ 76%]
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerEdgeCases::t
est_model_runner_handles_malformed_example_structure 
src/model_checker/builder/tests/unit/test_runner.py::TestModelRunnerEdgeCases::t
est_model_runner_handles_malformed_example_structure PASSED [ 76%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationCore::t
est_serialize_semantic_theory_creates_valid_structure PASSED [ 77%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationCore::t
est_serialize_semantic_theory_handles_empty_operators_correctly PASSED [ 77%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationCore::t
est_serialize_semantic_theory_preserves_dictionary_content PASSED [ 77%]
src/model_checker/builder/tests/unit/test_serialize.py::TestDeserializationCore:
:test_deserialize_semantic_theory_handles_missing_imports_with_error PASSED [ 78
%]
src/model_checker/builder/tests/unit/test_serialize.py::TestDeserializationCore:
:test_deserialize_semantic_theory_reconstructs_valid_structure PASSED [ 78%]
src/model_checker/builder/tests/unit/test_serialize.py::TestOperatorSerializatio
n::test_deserialize_operators_creates_operator_collection PASSED [ 79%]
src/model_checker/builder/tests/unit/test_serialize.py::TestOperatorSerializatio
n::test_serialize_operators_creates_correct_structure PASSED [ 79%]
src/model_checker/builder/tests/unit/test_serialize.py::TestOperatorSerializatio
n::test_serialize_operators_handles_operator_collection_input PASSED [ 79%]
src/model_checker/builder/tests/unit/test_serialize.py::TestImportUtility::test_
import_class_handles_builtin_modules_correctly PASSED [ 80%]
src/model_checker/builder/tests/unit/test_serialize.py::TestImportUtility::test_
import_class_imports_valid_classes_successfully PASSED [ 80%]
src/model_checker/builder/tests/unit/test_serialize.py::TestImportUtility::test_
import_class_raises_error_for_nonexistent_class PASSED [ 80%]
src/model_checker/builder/tests/unit/test_serialize.py::TestImportUtility::test_
import_class_raises_error_for_nonexistent_module PASSED [ 81%]
src/model_checker/builder/tests/unit/test_serialize.py::TestRealTheoryIntegratio
n::test_serialize_real_logos_theory_preserves_structure PASSED [ 81%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationErrorHa
ndling::test_deserialize_semantic_theory_handles_invalid_input_types 
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationErrorHa
ndling::test_deserialize_semantic_theory_handles_invalid_input_types PASSED [ 82
%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationErrorHa
ndling::test_serialize_semantic_theory_handles_malformed_theory_structure 
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationErrorHa
ndling::test_serialize_semantic_theory_handles_malformed_theory_structure PASSED
 [ 82%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationEdgeCas
es::test_serialize_semantic_theory_handles_large_operator_collections PASSED [ 8
2%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationEdgeCas
es::test_serialize_semantic_theory_handles_unicode_operators_correctly PASSED [ 
83%]
src/model_checker/builder/tests/unit/test_serialize.py::TestSerializationEdgeCas
es::test_serialize_semantic_theory_preserves_complex_nested_settings PASSED [ 83
%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nCore::test_operator_translation_has_required_interface_methods PASSED [ 84%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nCore::test_operator_translation_initializes_successfully PASSED [ 84%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nExecution::test_operator_translation_handles_complex_formulas_correctly PASSED 
[ 84%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nExecution::test_operator_translation_preserves_untranslated_operators PASSED [ 
85%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nExecution::test_operator_translation_translates_basic_operators_correctly PASSE
D [ 85%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nMultipleTheories::test_operator_translation_handles_multiple_theory_dictionarie
s PASSED [ 85%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nIntegration::test_build_module_integrates_with_translation_after_refactoring PA
SSED [ 86%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nErrorHandling::test_operator_translation_handles_empty_dictionary_gracefully PA
SSED [ 86%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nErrorHandling::test_operator_translation_handles_malformed_example_structure 
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nErrorHandling::test_operator_translation_handles_malformed_example_structure PA
SSED [ 87%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nErrorHandling::test_operator_translation_handles_none_dictionary_gracefully PAS
SED [ 87%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nEdgeCases::test_operator_translation_handles_empty_premises_and_conclusions PAS
SED [ 87%]
src/model_checker/builder/tests/unit/test_translation.py::TestOperatorTranslatio
nEdgeCases::test_operator_translation_handles_unicode_operators_in_input PASSED 
[ 88%]
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_accepts_valid_theory_structure PASSED [ 88%
]
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_identifies_missing_required_components 
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_identifies_missing_required_components PASS
ED [ 88%]
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_rejects_non_dictionary_input 
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_rejects_non_dictionary_input PASSED [ 89%]
src/model_checker/builder/tests/unit/test_validation.py::TestSemanticTheoryValid
ation::test_validate_semantic_theory_validates_component_types_correctly PASSED 
[ 89%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_accepts_valid_example_structure PASSED [ 90%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_rejects_non_list_input 
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_rejects_non_list_input PASSED [ 90%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_conclusions_structure 
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_conclusions_structure PASSED [ 90%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_correct_element_count 
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_correct_element_count PASSED [ 91%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_premises_structure 
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_premises_structure PASSED [ 91%]
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_settings_structure 
src/model_checker/builder/tests/unit/test_validation.py::TestExampleCaseValidati
on::test_validate_example_case_validates_settings_structure PASSED [ 92%]
src/model_checker/builder/tests/unit/test_validation.py::TestValidationEdgeCases
::test_validate_example_case_handles_complex_settings_structures PASSED [ 92%]
src/model_checker/builder/tests/unit/test_validation.py::TestValidationEdgeCases
::test_validate_example_case_handles_empty_premises_and_conclusions PASSED [ 92%
]
src/model_checker/builder/tests/unit/test_validation.py::TestValidationEdgeCases
::test_validate_example_case_handles_unicode_content PASSED [ 93%]
src/model_checker/builder/tests/unit/test_validation.py::TestValidationEdgeCases
::test_validate_semantic_theory_handles_extra_theory_components PASSED [ 93%]
src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3ContextIsolatio
n::test_conflicting_constraints PASSED [ 93%]
src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3ContextIsolatio
n::test_context_reset PASSED [ 94%]
src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3ContextIsolatio
n::test_solver_state_isolation PASSED [ 94%]
src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3ContextIsolatio
n::test_solver_state_leakage_without_reset PASSED [ 95%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ConstraintCreation:
:test_create_difference_constraint_generates_valid_constraint PASSED [ 95%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ConstraintCreation:
:test_create_difference_constraint_handles_single_variable_correctly PASSED [ 95
%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ConstraintCreation:
:test_create_difference_constraint_rejects_empty_variables PASSED [ 96%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ConstraintCreation:
:test_create_difference_constraint_rejects_invalid_variables PASSED [ 96%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ConstraintCreation:
:test_create_difference_constraint_rejects_none_model PASSED [ 96%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ModelValueExtractio
n::test_extract_model_values_handles_unassigned_variables PASSED [ 97%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ModelValueExtractio
n::test_extract_model_values_rejects_none_model PASSED [ 97%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3ModelValueExtractio
n::test_extract_model_values_retrieves_correct_values PASSED [ 98%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3NextModelFinding::t
est_find_next_model_locates_different_model PASSED [ 98%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3NextModelFinding::t
est_find_next_model_rejects_none_previous_model PASSED [ 98%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3NextModelFinding::t
est_find_next_model_rejects_none_solver PASSED [ 99%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3UtilsEdgeCases::tes
t_create_difference_constraint_handles_mixed_variable_types PASSED [ 99%]
src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3UtilsEdgeCases::tes
t_extract_model_values_handles_large_variable_count PASSED [100%]

============================== slowest durations ===============================
2.01s call     src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFu
llPipeline::test_error_handling
1.52s call     src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFu
llPipeline::test_iteration_workflow
1.40s call     src/model_checker/builder/tests/e2e/test_full_pipeline.py::TestFu
llPipeline::test_theory_library_execution
0.98s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_multiple_examples_process_efficiently
0.95s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_constraint_generation_scales_linearly
0.70s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestBarOutputBarOrdering::test_freeze_complete_time_consistency
0.60s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestBarOutputBarOrdering::test_multiple_bars_maintain_independent_frozen_stat
e
0.52s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_large_model_generation_completes_within_timeout
0.51s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_medium_model_generation_completes_within_timeout
0.50s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestBarOutputBarOrdering::test_deferred_completion_preserves_frozen_state
0.31s call     src/model_checker/builder/tests/unit/test_runner.py::TestModelRun
nerEdgeCases::test_model_runner_handles_malformed_example_structure
0.30s call     src/model_checker/builder/tests/unit/test_progress.py::TestSpinne
r::test_spinner_output
0.30s call     src/model_checker/builder/tests/unit/test_progress.py::TestSpinne
r::test_spinner_start_stop
0.23s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_small_model_generation_completes_quickly
0.20s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestProgressBarOrdering::test_complete_handles_already_stopped_thread
0.20s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestUnifiedProgressDeferredCompletion::test_stop_animation_without_printing
0.20s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestProgressBarOrdering::test_progress_bar_animation_during_z3_search
0.12s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estPerformanceAndScalabilityScenarios::test_multiple_project_generation_complete
s_within_reasonable_time
0.10s call     src/model_checker/builder/tests/integration/test_build_module_the
ories.py::TestBuildModule::test_run_model_check_logos
0.10s call     src/model_checker/builder/tests/integration/test_build_module_the
ories.py::TestBuildModule::test_run_model_check_bimodal
0.10s call     src/model_checker/builder/tests/unit/test_runner.py::TestModelRun
nerExecution::test_model_runner_executes_model_check_successfully
0.10s call     src/model_checker/builder/tests/unit/test_runner.py::TestModelRun
nerEdgeCases::test_model_runner_handles_empty_example_cases_appropriately
0.10s call     src/model_checker/builder/tests/unit/test_runner.py::TestModelRun
nerExecution::test_model_runner_handles_example_processing_correctly
0.10s call     src/model_checker/builder/tests/unit/test_progress_bar_ordering.p
y::TestUnifiedProgressDeferredCompletion::test_manual_thread_stop_then_complete
0.08s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_buildmodule_with_package
0.08s call     src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73
Fix::test_both_execution_paths_work
0.08s call     src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73
Fix::test_project_creation_and_example_execution
0.08s call     src/model_checker/builder/tests/integration/test_package_imports.
py::TestPackageImports::test_relative_imports_now_work_with_package
0.07s call     src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73
Fix::test_loader_handles_generated_packages
0.06s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estPerformanceAndScalabilityScenarios::test_repeated_project_operations_maintain
_consistent_performance
0.06s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectCore::test_create_project_handles_special_characters_in_name
0.05s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estProjectGenerationEdgeCases::test_project_generation_handles_special_character
_names_correctly
0.04s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectEdgeCases::test_create_project_with_empty_name_raises_error
0.04s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectEdgeCases::test_generate_multiple_projects_independently
0.04s call     src/model_checker/builder/tests/integration/test_performance.py::
TestBuilderPerformance::test_comparison_mode_performance
0.04s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estProjectGenerationEdgeCases::test_project_generation_creates_multiple_projects
_independently
0.03s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleBasic::test_build_example_print_model
0.03s call     src/model_checker/builder/tests/integration/test_workflow.py::Tes
tUserWorkflowIntegration::test_multiple_project_creation_workflow_handles_confli
cts
0.03s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleBasic::test_build_example_get_result
0.03s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleBasic::test_build_example_with_no_model
0.03s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleBasic::test_build_example_comparison_mode
0.02s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleBasic::test_build_example_initialization
0.02s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleIntegration::test_logos_extensional_theory
0.02s call     src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3
ContextIsolation::test_solver_state_isolation
0.02s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estSystemPathIsolationBehavior::test_sys_path_modifications_do_not_interfere_bet
ween_operations
0.02s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestGeneratedProjectImports::test_default_project_examples_init_loading
0.02s call     src/model_checker/builder/tests/unit/test_package_structure.py::T
estPackageStructure::test_init_file_creation
0.02s call     src/model_checker/builder/tests/unit/test_example.py::TestBuildEx
ampleIntegration::test_find_next_model_basic
0.02s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectCore::test_generate_template_creates_valid_content
0.01s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestGeneratedProjectImports::test_generated_project_detection
0.01s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestGeneratedProjectImports::test_find_project_directory
0.01s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectCore::test_logos_project_generation
0.01s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectCore::test_create_project_with_valid_name_succeeds
0.01s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestGeneratedProjectImports::test_sys_path_configuration
0.01s call     src/model_checker/builder/tests/test_issue_73_fix.py::TestIssue73
Fix::test_handle_example_script_simulation
0.01s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestProjectStructureFlexibility::test_multiple_theory_templates
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestSubp
rocessExecution::test_pythonpath_setup_in_subprocess
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_direct_package_import
0.01s call     src/model_checker/builder/tests/integration/test_workflow.py::Tes
tEndToEndScenarios::test_complete_user_session_from_creation_to_execution
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_generated_project_detection
0.01s call     src/model_checker/builder/tests/unit/test_project.py::TestBuildPr
ojectEdgeCases::test_create_project_with_existing_name_handles_appropriately
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_package_root_finding
0.01s call     src/model_checker/builder/tests/integration/test_generated_projec
ts.py::TestGeneratedProjectImports::test_logos_project_generation_and_loading
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_relative_imports_work
0.01s call     src/model_checker/builder/tests/integration/test_workflow.py::Tes
tUserWorkflowIntegration::test_project_creation_and_module_loading_workflow_succ
eeds
0.01s call     src/model_checker/builder/tests/integration/test_component_integr
ation.py::TestLoaderRunnerIntegration::test_loader_runner_workflow_processes_exa
mples_correctly
0.01s call     src/model_checker/builder/tests/test_package_loading.py::TestPack
ageLoading::test_package_import_setup
0.01s call     src/model_checker/builder/tests/integration/test_workflow.py::Tes
tUserWorkflowIntegration::test_snake_project_scenario_resolution
0.01s call     src/model_checker/builder/tests/integration/test_package_imports.
py::TestPackageImports::test_package_marker_now_exists
0.01s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estCompleteUserWorkflowSimulation::test_complete_cli_workflow_simulation_execute
s_successfully
0.01s call     src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3
ContextIsolation::test_conflicting_constraints
0.01s call     src/model_checker/builder/tests/unit/test_z3_utils.py::TestZ3Util
sEdgeCases::test_extract_model_values_handles_large_variable_count
0.01s call     src/model_checker/builder/tests/e2e/test_project_edge_cases.py::T
estProjectGenerationEdgeCases::test_project_generation_handles_directories_with_
spaces_correctly
0.01s call     src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3
ContextIsolation::test_solver_state_leakage_without_reset
0.01s call     src/model_checker/builder/tests/integration/test_cli_interactive_
integration.py::TestInteractiveModeUserExperience::test_interactive_mode_provide
s_appropriate_user_feedback
0.01s call     src/model_checker/builder/tests/integration/test_build_module_the
ories.py::TestBuildModule::test_module_initialization_bimodal
0.01s call     src/model_checker/builder/tests/integration/test_component_integr
ation.py::TestComparisonIntegration::test_comparison_mode_integration_with_multi
ple_theories
0.01s call     src/model_checker/builder/tests/integration/test_cli_interactive_
integration.py::TestInteractiveModeUserExperience::test_interactive_mode_integra
tion_with_real_user_workflow
0.01s call     src/model_checker/builder/tests/unit/test_z3_isolation.py::TestZ3
ContextIsolation::test_context_reset
0.01s call     src/model_checker/builder/tests/integration/test_component_integr
ation.py::TestModuleTheoryIntegration::test_module_theory_validation_integration
0.01s call     src/model_checker/builder/tests/integration/test_component_integr
ation.py::TestLoaderRunnerIntegration::test_loader_translation_integration_appli
es_dictionaries

(779 durations < 0.005s hidden.  Use -vv to show these durations.)
============= 262 passed, 1 skipped, 71 subtests passed in 15.14s ==============
  Running package tests for iterate
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 207 items                                                            

src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_zero_iterations_requested PASSED [  0%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_negative_iterations_rejected PASSED [  0%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_very_large_iteration_count PASSED [  1%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_empty_formula_iteration PASSED [  1%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_iteration_with_unsatisfiable_formula PASSED [  2%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_iteration_with_missing_settings PASSED [  2%]
src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestIteratorEdgeCases::t
est_concurrent_iteration_safety PASSED [  3%]
src/model_checker/iterate/tests/integration/test_build_example.py::TestIteratorB
uildExample::test_attributes_copied_from_original PASSED [  3%]
src/model_checker/iterate/tests/integration/test_build_example.py::TestIteratorB
uildExample::test_create_with_z3_model PASSED [  4%]
src/model_checker/iterate/tests/integration/test_build_example.py::TestIteratorB
uildExample::test_injection_delegation PASSED [  4%]
src/model_checker/iterate/tests/integration/test_build_example.py::TestIteratorB
uildExample::test_no_class_methods_used PASSED [  5%]
src/model_checker/iterate/tests/integration/test_build_example.py::TestIteratorB
uildExample::test_theory_agnostic_implementation PASSED [  5%]
src/model_checker/iterate/tests/integration/test_constraint_preservation.py::Tes
tConstraintPreservation::test_original_constraints_preserved PASSED [  6%]
src/model_checker/iterate/tests/integration/test_constraint_preservation.py::Tes
tConstraintPreservation::test_premise_conclusion_constraints_added PASSED [  6%]
src/model_checker/iterate/tests/integration/test_constraint_preservation.py::Tes
tConstraintPreservation::test_solver_isolation PASSED [  7%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_constraint_accumulation PASSED [  7%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_error_recovery_during_iteration PASSED [  8%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_full_iteration_with_real_theory PASSED [  8%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_isomorphism_detection_integration PASSED [  9%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_iteration_with_timeout PASSED [  9%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_model_validation_during_iteration PASSED [ 10%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_progress_tracking_integration PASSED [ 10%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
Orchestration::test_state_management_during_iteration PASSED [ 11%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
ErrorPaths::test_initialization_with_invalid_example PASSED [ 11%]
src/model_checker/iterate/tests/integration/test_core_orchestration.py::TestCore
ErrorPaths::test_solver_failure_handling PASSED [ 12%]
src/model_checker/iterate/tests/integration/test_enhanced_tracking.py::TestEnhan
cedTracking::test_search_statistics_creation PASSED [ 12%]
src/model_checker/iterate/tests/integration/test_enhanced_tracking.py::TestEnhan
cedTracking::test_search_statistics_summary_line PASSED [ 13%]
src/model_checker/iterate/tests/integration/test_enhanced_tracking.py::TestEnhan
cedTracking::test_report_generation PASSED [ 13%]
src/model_checker/iterate/tests/integration/test_enhanced_tracking.py::TestEnhan
cedTracking::test_partial_report_with_timeout PASSED [ 14%]
src/model_checker/iterate/tests/integration/test_enhanced_tracking.py::TestEnhan
cedTracking::test_iterator_tracking PASSED [ 14%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_invalid_build_example_no_model_structure PASSED [ 14%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_invalid_build_example_no_z3_model PASSED [ 15%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_invalid_build_example_not_satisfiable PASSED [ 15%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_invalid_settings_iterate_value PASSED [ 16%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_invalid_settings_timeout_value PASSED [ 16%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_iterate_with_unsatisfiable_model PASSED [ 17%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestIterator
ErrorHandling::test_iterate_single_model_requested PASSED [ 17%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestCoreErro
rHandling::test_iterate_with_model_extraction_error PASSED [ 18%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestCoreErro
rHandling::test_iterate_generator_keyboard_interrupt PASSED [ 18%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestCoreErro
rHandling::test_reset_iterator PASSED [ 19%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestCoreErro
rHandling::test_get_debug_messages PASSED [ 19%]
src/model_checker/iterate/tests/integration/test_error_handling.py::TestCoreErro
rHandling::test_get_iteration_summary PASSED [ 20%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_iterate_generator_yields_incrementally PASSED [ 20%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_generator_maintains_history PASSED [ 21%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_backward_compatibility PASSED [ 21%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_generator_with_no_models PASSED [ 22%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_generator_with_single_model PASSED [ 22%]
src/model_checker/iterate/tests/integration/test_generator_interface.py::TestGen
eratorInterface::test_generator_handles_isomorphic_models PASSED [ 23%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_cache_behavior_under_load PASSED [ 23%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_complex_graph_comparison PASSED [ 24%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_graph_conversion_with_missing_attribute
s PASSED [ 24%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_isomorphism_cache_invalidation PASSED [
 25%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_isomorphism_with_attributes PASSED [ 25
%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_isomorphism_with_self_loops PASSED [ 26
%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_large_graph_isomorphism PASSED [ 26%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphIsomorphismIntegration::test_networkx_integration_edge_cases PASSED 
[ 27%]
src/model_checker/iterate/tests/integration/test_graph_isomorphism_integration.p
y::TestGraphManagerCacheBehavior::test_cache_growth_limitation PASSED [ 27%]
src/model_checker/iterate/tests/integration/test_graph_utils.py::TestModelGraph:
:test_create_graph PASSED [ 28%]
src/model_checker/iterate/tests/integration/test_graph_utils.py::TestModelGraph:
:test_invariant_hash PASSED [ 28%]
src/model_checker/iterate/tests/integration/test_graph_utils.py::TestModelGraph:
:test_isomorphism_detection PASSED [ 28%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_initialization PASSED [ 29%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_check_isomorphism_no_networkx PASSED [ 29%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_check_isomorphism_with_networkx PASSED [ 30%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_check_isomorphism_not_isomorphic PASSED [ 30%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_check_isomorphism_multiple_previous PASSED [ 31%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_check_isomorphism_error_handling PASSED [ 31%]
src/model_checker/iterate/tests/integration/test_isomorphism.py::TestIsomorphism
Checker::test_structural_comparison_priority PASSED [ 32%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_initialization PASSED [ 32%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_start_timing PASSED [ 33%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_terminate_max_iterations PASSED [ 33%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_terminate_timeout PASSED [ 34%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_terminate_consecutive_invalid PASSED [ 34%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_terminate_lack_of_progress PASSED [ 35%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_not_terminate PASSED [ 35%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_get_elapsed_time PASSED [ 36%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_should_attempt_escape PASSED [ 36%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestTermi
nationManager::test_get_progress_ratio PASSED [ 37%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestResul
tFormatter::test_format_iteration_summary PASSED [ 37%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestResul
tFormatter::test_format_difference_report PASSED [ 38%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestResul
tFormatter::test_format_empty_difference_report PASSED [ 38%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestResul
tFormatter::test_format_progress_update PASSED [ 39%]
src/model_checker/iterate/tests/integration/test_iteration_control.py::TestResul
tFormatter::test_create_progress_bar PASSED [ 39%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_constraint_accumulation PASSED [ 40%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_debug_mode PASSED [ 40%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_error_handling PASSED [ 41%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_finds_all_models PASSED [ 41%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_handles_isomorphism PASSED [ 42%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_progress_tracking PASSED [ 42%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_respects_limits PASSED [ 42%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_unsat_handling PASSED [ 43%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorGeneratorMethod::test_iterate_with_validation PASSED [ 43%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorEdgeCases::test_iterate_empty_constraints PASSED [ 44%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorEdgeCases::test_iterate_immediate_unsat PASSED [ 44%]
src/model_checker/iterate/tests/integration/test_iterator_generator.py::TestIter
atorEdgeCases::test_iterate_single_state PASSED [ 45%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_initialization PASSED [ 45%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_add_model_basic PASSED [ 46%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_count_differences PASSED [ 46%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_get_summary PASSED [ 47%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_empty_summary PASSED [ 47%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_set_completion_time PASSED [ 48%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_print_summary PASSED [ 48%]
src/model_checker/iterate/tests/integration/test_metrics.py::TestIterationStatis
tics::test_print_empty_summary PASSED [ 49%]
src/model_checker/iterate/tests/integration/test_models.py::TestModelBuilder::te
st_initialization PASSED [ 49%]
src/model_checker/iterate/tests/integration/test_models.py::TestModelBuilder::te
st_build_new_model_structure_success PASSED [ 50%]
src/model_checker/iterate/tests/integration/test_models.py::TestModelBuilder::te
st_build_new_model_structure_error_handling PASSED [ 50%]
src/model_checker/iterate/tests/integration/test_models.py::TestModelBuilder::te
st_initialize_z3_dependent_attributes PASSED [ 51%]
src/model_checker/iterate/tests/integration/test_models.py::TestModelBuilder::te
st_evaluate_z3_boolean PASSED [ 51%]
src/model_checker/iterate/tests/integration/test_models.py::TestDifferenceCalcul
ator::test_calculate_differences_basic PASSED [ 52%]
src/model_checker/iterate/tests/integration/test_models.py::TestDifferenceCalcul
ator::test_calculate_differences_with_removals PASSED [ 52%]
src/model_checker/iterate/tests/integration/test_models.py::TestDifferenceCalcul
ator::test_calculate_differences_error_handling PASSED [ 53%]
src/model_checker/iterate/tests/integration/test_models.py::TestDifferenceCalcul
ator::test_calculate_semantic_differences PASSED [ 53%]
src/model_checker/iterate/tests/integration/test_models.py::TestDifferenceCalcul
ator::test_compare_state_evaluations PASSED [ 54%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_constraint_generation_orchestration PASSED [ 54%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_error_handling_orchestration PASSED [ 55%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_iterate_with_mock_theory PASSED [ 55%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_model_extraction_orchestration PASSED [ 56%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_orchestrated_iteration PASSED [ 56%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_progress_reporting_orchestration PASSED [ 57%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_state_tracking_orchestration PASSED [ 57%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tRealTheoryIntegration::test_termination_conditions_orchestration PASSED [ 57%]
src/model_checker/iterate/tests/integration/test_real_theory_integration.py::Tes
tIteratorCoreWithRealTheory::test_iterate_method_coverage PASSED [ 58%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_abstract_methods_required PASSED [ 58%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_initialization_validation PASSED [ 59%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_timeout_handling PASSED [ 59%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_invalid_model_handling PASSED [ 60%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_consecutive_invalid_limit PASSED [ 60%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_isomorphism_detection PASSED [ 61%]
src/model_checker/iterate/tests/unit/test_base_iterator.py::TestBaseModelIterato
r::test_debug_message_collection PASSED [ 61%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_initialization PASSED [ 62%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_initialization_with_no_solver PASSED [ 62%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_create_extended_constraints PASSED [ 63%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_check_satisfiability PASSED [ 63%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_get_model PASSED [ 64%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_create_difference_constraint_basic PASSED [ 64%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_create_difference_constraint_empty PASSED [ 65%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_create_non_isomorphic_constraint PASSED [ 65%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_create_stronger_constraint PASSED [ 66%]
src/model_checker/iterate/tests/unit/test_constraints.py::TestConstraintGenerato
r::test_preserve_original_constraints PASSED [ 66%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_constraint_generation_with_invalid_model PASSED [ 67%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_non_isomorphic_constraint_attribute_error PASSED [ 67%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_non_isomorphic_constraint_key_error PASSED [ 68%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_non_isomorphic_constraint_z3_exception PASSED [ 68%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_state_difference_with_attribute_error PASSED [ 69%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_state_difference_with_type_error PASSED [ 69%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_state_difference_with_z3_exception PASSED [ 70%]
src/model_checker/iterate/tests/unit/test_constraints_error_paths.py::TestConstr
aintErrorPaths::test_z3_and_operation_failure PASSED [ 70%]
src/model_checker/iterate/tests/unit/test_core.py::TestBaseModelIterator::test_i
nitialization PASSED [ 71%]
src/model_checker/iterate/tests/unit/test_core.py::TestIterateExample::test_iter
ate_example_validation PASSED [ 71%]
src/model_checker/iterate/tests/unit/test_core_abstract_methods.py::TestAbstract
Methods::test_abstract_methods_docstrings PASSED [ 71%]
src/model_checker/iterate/tests/unit/test_core_abstract_methods.py::TestAbstract
Methods::test_abstract_methods_required PASSED [ 72%]
src/model_checker/iterate/tests/unit/test_core_abstract_methods.py::TestAbstract
Methods::test_constraint_methods_called_correctly PASSED [ 72%]
src/model_checker/iterate/tests/unit/test_core_no_state_transfer.py::TestNoState
Transfer::test_no_extract_verify_falsify_method PASSED [ 73%]
src/model_checker/iterate/tests/unit/test_core_no_state_transfer.py::TestNoState
Transfer::test_no_initialize_with_state_call PASSED [ 73%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestConstrai
ntGeneratorCoverage::test_create_extended_constraints_empty PASSED [ 74%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestConstrai
ntGeneratorCoverage::test_generate_input_combinations_higher_arity PASSED [ 74%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestConstrai
ntGeneratorCoverage::test_get_model_with_z3_exception PASSED [ 75%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestModelsUt
ilityCoverage::test_difference_calculator_empty_differences PASSED [ 75%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestModelsUt
ilityCoverage::test_evaluate_z3_boolean_standalone PASSED [ 76%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestMetricsC
overage::test_iteration_statistics_completion_time PASSED [ 76%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestGraphCov
erage::test_graph_init_with_logging PASSED [ 77%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestGraphCov
erage::test_model_graph_init_coverage PASSED [ 77%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestErrorPat
hsCoverage::test_difference_calculator_error_in_semantic_differences PASSED [ 78
%]
src/model_checker/iterate/tests/unit/test_coverage_improvements.py::TestErrorPat
hsCoverage::test_model_builder_initialize_with_missing_solver PASSED [ 78%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterateError::test_basi
c_error_creation PASSED [ 79%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterateError::test_erro
r_with_context PASSED [ 79%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterateError::test_erro
r_string_representation PASSED [ 80%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterationLimitError::te
st_basic_limit_error PASSED [ 80%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterationLimitError::te
st_limit_error_with_reason PASSED [ 81%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterationStateError::te
st_basic_state_error PASSED [ 81%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterationStateError::te
st_state_error_with_suggestion PASSED [ 82%]
src/model_checker/iterate/tests/unit/test_errors.py::TestModelExtractionError::t
est_basic_extraction_error PASSED [ 82%]
src/model_checker/iterate/tests/unit/test_errors.py::TestModelExtractionError::t
est_extraction_error_with_suggestion PASSED [ 83%]
src/model_checker/iterate/tests/unit/test_errors.py::TestConstraintGenerationErr
or::test_basic_constraint_error PASSED [ 83%]
src/model_checker/iterate/tests/unit/test_errors.py::TestConstraintGenerationErr
or::test_constraint_error_with_model_num PASSED [ 84%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIsomorphismCheckError::
test_isomorphism_error PASSED [ 84%]
src/model_checker/iterate/tests/unit/test_errors.py::TestIterationTimeoutError::
test_timeout_error PASSED [ 85%]
src/model_checker/iterate/tests/unit/test_errors.py::TestModelValidationError::t
est_validation_error PASSED [ 85%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_unknown_type PASSED [ 85%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_none PASSED [ 86%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_numeric_one PASSED [ 86%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_real_value PASSED [ 87%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_real_value_error PASSED [ 87%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_string_values PASSED [ 88%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_evaluate_z3_boolean_with_true_string PASSED [ 88%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
EdgeCases::test_initialize_base_attributes_without_solver PASSED [ 89%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
ConstraintApplication::test_verify_falsify_constraint_application PASSED [ 89%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestModelBuilder
ConstraintApplication::test_verify_without_falsify PASSED [ 90%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorEdgeCases::test_calculate_atomic_differences_returns_none PASSED [ 90%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorEdgeCases::test_calculate_differences_with_empty_states PASSED [ 91%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorEdgeCases::test_calculate_state_differences_no_changes PASSED [ 91%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorEdgeCases::test_compare_state_evaluations_no_changes PASSED [ 92%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorStateMethods::test_calculate_differences_comprehensive PASSED [ 92%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorStateMethods::test_compare_evaluations_with_changes PASSED [ 93%]
src/model_checker/iterate/tests/unit/test_models_edge_cases.py::TestDifferenceCa
lculatorStateMethods::test_format_state_changes_with_changes PASSED [ 93%]
src/model_checker/iterate/tests/unit/test_simplified_iterator.py::TestSimplified
Iterator::test_handles_failed_model_creation PASSED [ 94%]
src/model_checker/iterate/tests/unit/test_simplified_iterator.py::TestSimplified
Iterator::test_interpret_called_on_new_structure PASSED [ 94%]
src/model_checker/iterate/tests/unit/test_simplified_iterator.py::TestSimplified
Iterator::test_no_theory_concepts_in_core PASSED [ 95%]
src/model_checker/iterate/tests/unit/test_simplified_iterator.py::TestSimplified
Iterator::test_simplified_method_shorter PASSED [ 95%]
src/model_checker/iterate/tests/unit/test_simplified_iterator.py::TestSimplified
Iterator::test_uses_iterator_build_example PASSED [ 96%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_evaluate_z3_boolean_direct_values PASSED [ 96%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_evaluate_z3_boolean_numeric_values PASSED [ 97%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_evaluate_z3_boolean_z3_expressions PASSED [ 97%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_is_valid_model_basic PASSED [ 98%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_is_valid_model_non_empty PASSED [ 98%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_validate_conclusions_countermodel PASSED [ 99%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_validate_conclusions_theorem PASSED [ 99%]
src/model_checker/iterate/tests/unit/test_validation.py::TestModelValidator::tes
t_validate_premises PASSED [100%]

============================== slowest durations ===============================
0.62s call     src/model_checker/iterate/tests/integration/test_graph_isomorphis
m_integration.py::TestGraphManagerCacheBehavior::test_cache_growth_limitation
0.15s call     src/model_checker/iterate/tests/integration/test_iteration_contro
l.py::TestTerminationManager::test_should_terminate_timeout
0.11s call     src/model_checker/iterate/tests/unit/test_simplified_iterator.py:
:TestSimplifiedIterator::test_handles_failed_model_creation
0.10s call     src/model_checker/iterate/tests/unit/test_base_iterator.py::TestB
aseModelIterator::test_timeout_handling
0.10s call     src/model_checker/iterate/tests/integration/test_iteration_contro
l.py::TestTerminationManager::test_get_elapsed_time
0.04s call     src/model_checker/iterate/tests/integration/test_graph_isomorphis
m_integration.py::TestGraphIsomorphismIntegration::test_cache_behavior_under_loa
d
0.03s call     src/model_checker/iterate/tests/integration/test_graph_isomorphis
m_integration.py::TestGraphIsomorphismIntegration::test_large_graph_isomorphism
0.02s call     src/model_checker/iterate/tests/integration/test_graph_utils.py::
TestModelGraph::test_create_graph
0.01s call     src/model_checker/iterate/tests/unit/test_simplified_iterator.py:
:TestSimplifiedIterator::test_no_theory_concepts_in_core
0.01s call     src/model_checker/iterate/tests/unit/test_base_iterator.py::TestB
aseModelIterator::test_invalid_model_handling
0.01s call     src/model_checker/iterate/tests/integration/test_graph_isomorphis
m_integration.py::TestGraphIsomorphismIntegration::test_complex_graph_comparison
0.01s call     src/model_checker/iterate/tests/e2e/test_edge_cases.py::TestItera
torEdgeCases::test_zero_iterations_requested
0.01s call     src/model_checker/iterate/tests/integration/test_graph_isomorphis
m_integration.py::TestGraphIsomorphismIntegration::test_isomorphism_cache_invali
dation

(608 durations < 0.005s hidden.  Use -vv to show these durations.)
============================= 207 passed in 2.63s ==============================
  Running package tests for jupyter
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 72 items                                                             

src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestMode
lExplorerIntegration::test_model_explorer_initialization PASSED [  1%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestMode
lExplorerIntegration::test_check_button_click PASSED [  2%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestMode
lExplorerIntegration::test_theory_change_handler PASSED [  4%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestMode
lExplorerIntegration::test_setting_update PASSED [  5%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestForm
ulaCheckerIntegration::test_formula_checker_initialization PASSED [  6%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestForm
ulaCheckerIntegration::test_set_formula PASSED [  8%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestForm
ulaCheckerIntegration::test_set_premises_list PASSED [  9%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestForm
ulaCheckerIntegration::test_check_formula_method PASSED [ 11%]
src/model_checker/jupyter/tests/integration/test_widget_interaction.py::TestForm
ulaCheckerIntegration::test_display_method PASSED [ 12%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestTheoryAdapter::test_f
ormat_formula_not_implemented PASSED [ 13%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestTheoryAdapter::test_f
ormat_model_not_implemented PASSED [ 15%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestTheoryAdapter::test_i
nitialization PASSED [ 16%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestTheoryAdapter::test_m
odel_to_graph_not_implemented PASSED [ 18%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestGetTheoryAdapter::tes
t_get_bimodal_adapter PASSED [ 19%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestGetTheoryAdapter::tes
t_get_exclusion_adapter PASSED [ 20%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestGetTheoryAdapter::tes
t_get_imposition_adapter PASSED [ 22%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestGetTheoryAdapter::tes
t_get_logos_adapter PASSED [ 23%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestGetTheoryAdapter::tes
t_get_unknown_adapter_returns_default PASSED [ 25%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestDefaultTheoryAdapter:
:test_format_formula PASSED [ 26%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestDefaultTheoryAdapter:
:test_format_model PASSED [ 27%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestDefaultTheoryAdapter:
:test_model_to_graph PASSED [ 29%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestExclusionTheoryAdapte
r::test_format_formula PASSED [ 30%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestExclusionTheoryAdapte
r::test_format_model PASSED [ 31%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestExclusionTheoryAdapte
r::test_model_to_graph_uses_default PASSED [ 33%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestImpositionTheoryAdapt
er::test_inherits_properly PASSED [ 34%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestImpositionTheoryAdapt
er::test_model_to_graph_uses_default PASSED [ 36%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestBimodalTheoryAdapter:
:test_inherits_properly PASSED [ 37%]
src/model_checker/jupyter/tests/unit/test_adapters.py::TestBimodalTheoryAdapter:
:test_model_to_graph_uses_default PASSED [ 38%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_base_exception PASSED [ 40%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_environment_error PASSED [ 41%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_dependency_error_with_feature PASSED [ 43%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_dependency_error_without_feature PASSED [ 44%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_widget_error PASSED [ 45%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_visualization_error_with_reason PASSED [ 47%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_visualization_error_without_reason PASSED [ 48%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_formula_error PASSED [ 50%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_theory_error PASSED [ 51%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_timeout_error PASSED [ 52%]
src/model_checker/jupyter/tests/unit/test_exceptions.py::TestJupyterExceptions::
test_exception_hierarchy PASSED [ 54%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintModel::t
est_print_model_capture_multiline PASSED [ 55%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintModel::t
est_print_model_capture_output PASSED [ 56%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintModel::t
est_print_model_direct_output PASSED [ 58%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintModel::t
est_print_model_with_empty_output PASSED [ 59%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintAll::tes
t_print_all_capture_output PASSED [ 61%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintAll::tes
t_print_all_direct_output PASSED [ 62%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintAll::tes
t_print_all_handles_exception PASSED [ 63%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestPrintAll::tes
t_print_all_with_complex_model PASSED [ 65%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestIntegration::
test_both_functions_work_with_same_model PASSED [ 66%]
src/model_checker/jupyter/tests/unit/test_notebook_helpers.py::TestIntegration::
test_capture_flag_consistency PASSED [ 68%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestModelExplorerUIBui
lder::test_build_main_ui PASSED [ 69%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestModelExplorerUIBui
lder::test_build_main_ui_without_ipywidgets PASSED [ 70%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestModelExplorerUIBui
lder::test_build_settings_accordion PASSED [ 72%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestFormulaCheckerUIBu
ilder::test_build_main_ui PASSED [ 73%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestFormulaCheckerUIBu
ilder::test_build_formula_input PASSED [ 75%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestFormulaCheckerUIBu
ilder::test_build_check_button PASSED [ 76%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestFormulaCheckerUIBu
ilder::test_theory_dropdown_with_observer PASSED [ 77%]
src/model_checker/jupyter/tests/unit/test_ui_builders.py::TestFormulaCheckerUIBu
ilder::test_theory_dropdown_without_observer PASSED [ 79%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_unicode_to_latex_logical_operators PASSED [ 80%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_unicode_to_latex_modal_operators PASSED [ 81%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_unicode_to_latex_quantifiers PASSED [ 83%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_unicode_to_latex_combined PASSED [ 84%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_unicode_to_latex_unchanged PASSED [ 86%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_latex_to_unicode_logical_operators PASSED [ 87%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_latex_to_unicode_modal_operators PASSED [ 88%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_latex_to_unicode_quantifiers PASSED [ 90%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_latex_to_unicode_combined PASSED [ 91%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_latex_to_unicode_unchanged PASSED [ 93%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_normalize_formula_to_latex PASSED [ 94%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_normalize_formula_to_unicode PASSED [ 95%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_normalize_formula_default PASSED [ 97%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_normalize_formula_non_string PASSED [ 98%]
src/model_checker/jupyter/tests/unit/test_unicode.py::TestUnicodeConversions::te
st_bidirectional_conversion PASSED [100%]

============================== slowest durations ===============================

(216 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 72 passed in 1.68s ==============================
  Running package tests for models
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 60 items                                                             

src/model_checker/models/tests/integration/test_constraints_injection.py::TestCo
nstraintsInjection::test_inject_z3_values_delegates_to_semantics PASSED [  1%]
src/model_checker/models/tests/integration/test_constraints_injection.py::TestCo
nstraintsInjection::test_inject_z3_values_no_delegation_if_not_supported PASSED 
[  3%]
src/model_checker/models/tests/integration/test_constraints_injection.py::TestCo
nstraintsInjection::test_no_theory_concepts_in_injection PASSED [  5%]
src/model_checker/models/tests/integration/test_imports.py::TestModelsImports::t
est_package_import PASSED [  6%]
src/model_checker/models/tests/integration/test_imports.py::TestModelsImports::t
est_submodule_imports PASSED [  8%]
src/model_checker/models/tests/integration/test_integration.py::TestModelsIntegr
ation::test_cross_component_interaction PASSED [ 10%]
src/model_checker/models/tests/integration/test_integration.py::TestModelsIntegr
ation::test_imports_work_correctly PASSED [ 11%]
src/model_checker/models/tests/integration/test_integration.py::TestModelsIntegr
ation::test_inheritance_works_correctly PASSED [ 13%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_constraint_generation PASSED [ 15%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_empty_premises_conclusions PASSED [ 16%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_initialization PASSED [ 18%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_instantiate_method PASSED [ 20%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_instantiate_recursive PASSED [ 21%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_invalid_sentence_letter_raises_error PASSED [ 23%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_load_sentence_letters PASSED [ 25%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_operator_dictionary_copying PASSED [ 26%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_print_enumerate PASSED [ 28%]
src/model_checker/models/tests/unit/test_constraints.py::TestModelConstraints::t
est_str_representation PASSED [ 30%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionDefaults
::test_cannot_instantiate_base_class PASSED [ 31%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionDefaults
::test_complex_sentence_initialization PASSED [ 33%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionDefaults
::test_hash_and_equality PASSED [ 35%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionDefaults
::test_initialization_with_valid_inputs PASSED [ 36%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionDefaults
::test_validates_model_structure PASSED [ 38%]
src/model_checker/models/tests/unit/test_proposition.py::TestPropositionColorFor
matting::test_set_colors_method PASSED [ 40%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_fusion_operation PASSED [ 41%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_initialization PASSED [ 43%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_is_part_of PASSED [ 45%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_is_proper_part_of PASSED [ 46%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_non_null_part_of PASSED [ 48%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_product_operation PASSED [ 50%]
src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaults::test
_z3_set_conversion PASSED [ 51%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_attribute_initialization_order PASSED [ 53%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_check_result PASSED [ 55%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_cleanup_solver_resources PASSED [ 56%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_create_result PASSED [ 58%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_initialization PASSED [ 60%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_interpret_method PASSED [ 61%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_process_solver_results_sat PASSED [ 63%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_process_solver_results_timeout PASSED [ 65%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_process_solver_results_unsat PASSED [ 66%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_re_solve PASSED [ 68%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_setup_solver PASSED [ 70%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_solve_satisfiable PASSED [ 71%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_solve_unsatisfiable PASSED [ 73%]
src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructur
e::test_solver_isolation PASSED [ 75%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintAllMethod:
:test_print_all_calls_required_methods PASSED [ 76%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintAllMethod:
:test_print_all_with_default_output PASSED [ 78%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_get_relevant_constraints_satisfiable PASSED [ 80%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_get_relevant_constraints_unsatisfiable PASSED [ 81%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_get_relevant_constraints_no_model PASSED [ 83%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_print_constraint_summary PASSED [ 85%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_organize_constraint_groups PASSED [ 86%]
src/model_checker/models/tests/unit/test_structure_print.py::TestPrintHelperMeth
ods::test_print_constraint_groups PASSED [ 88%]
src/model_checker/models/tests/unit/test_structure_print.py::TestSentencePrintHe
lpers::test_print_sentence_group_singular_title PASSED [ 90%]
src/model_checker/models/tests/unit/test_structure_print.py::TestSentencePrintHe
lpers::test_print_sentence_group_plural_title PASSED [ 91%]
src/model_checker/models/tests/unit/test_structure_print.py::TestSentencePrintHe
lpers::test_print_sentence_group_empty PASSED [ 93%]
src/model_checker/models/tests/unit/test_structure_print.py::TestModelDifference
Helpers::test_print_sentence_letter_differences PASSED [ 95%]
src/model_checker/models/tests/unit/test_structure_print.py::TestModelDifference
Helpers::test_print_semantic_function_differences PASSED [ 96%]
src/model_checker/models/tests/unit/test_structure_print.py::TestModelDifference
Helpers::test_print_model_structure_differences PASSED [ 98%]
src/model_checker/models/tests/unit/test_structure_print.py::TestModelDifference
Helpers::test_print_structural_metrics PASSED [100%]

============================== slowest durations ===============================
0.03s call     src/model_checker/models/tests/unit/test_structure.py::TestModelD
efaultsStructure::test_attribute_initialization_order
0.01s call     src/model_checker/models/tests/integration/test_integration.py::T
estModelsIntegration::test_cross_component_interaction

(178 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 60 passed in 1.06s ==============================
  Running package tests for output
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 234 items                                                            

src/model_checker/output/tests/integration/test_build_integration.py::TestBuildI
ntegration::test_output_manager_initialization_in_build_module PASSED [  0%]
src/model_checker/output/tests/integration/test_build_integration.py::TestBuildI
ntegration::test_capture_model_output PASSED [  0%]
src/model_checker/output/tests/integration/test_build_integration.py::TestBuildI
ntegration::test_collect_and_format_integration PASSED [  1%]
src/model_checker/output/tests/integration/test_build_integration.py::TestBuildI
ntegration::test_save_workflow PASSED [  1%]
src/model_checker/output/tests/integration/test_build_integration.py::TestBuildI
ntegration::test_sequential_mode_workflow PASSED [  2%]
src/model_checker/output/tests/integration/test_collector_integration.py::TestCo
llectorIntegration::test_collect_no_model PASSED [  2%]
src/model_checker/output/tests/integration/test_collector_integration.py::TestCo
llectorIntegration::test_collect_with_extraction_methods PASSED [  2%]
src/model_checker/output/tests/integration/test_collector_integration.py::TestCo
llectorIntegration::test_collect_without_extraction_methods PASSED [  3%]
src/model_checker/output/tests/integration/test_markdown_relations.py::TestMarkd
ownRelations::test_format_default_relations PASSED [  3%]
src/model_checker/output/tests/integration/test_markdown_relations.py::TestMarkd
ownRelations::test_format_exclusion_relations PASSED [  4%]
src/model_checker/output/tests/integration/test_markdown_relations.py::TestMarkd
ownRelations::test_format_imposition_relations PASSED [  4%]
src/model_checker/output/tests/integration/test_markdown_relations.py::TestMarkd
ownRelations::test_format_mixed_relations PASSED [  5%]
src/model_checker/output/tests/integration/test_markdown_relations.py::TestMarkd
ownRelations::test_format_time_shift_relations PASSED [  5%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_collect_model_data_with_model PASSED [  5%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_collect_model_data_no_model PASSED [  6%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_collect_states PASSED [  6%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_get_evaluation_world PASSED [  7%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_collect_propositions PASSED [  7%]
src/model_checker/output/tests/integration/test_model_data_collection.py::TestMo
delDataCollection::test_collect_relations PASSED [  8%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_output_manager_initialization PASSED [  8%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_output_manager_disabled PASSED [  8%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_output_manager_enabled PASSED [  9%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_create_output_directory PASSED [  9%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_sequential_subdirectory_creation PASSED [ 10%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_batch_mode_no_subdirectory PASSED [ 10%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_custom_output_directory_name PASSED [ 11%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_output_modes PASSED [ 11%]
src/model_checker/output/tests/integration/test_output_directory.py::TestOutputD
irectory::test_sequential_file_options PASSED [ 11%]
src/model_checker/output/tests/integration/test_output_integration.py::TestOutpu
tIntegration::test_bimodal_output_pipeline PASSED [ 12%]
src/model_checker/output/tests/integration/test_output_integration.py::TestOutpu
tIntegration::test_exclusion_output_pipeline PASSED [ 12%]
src/model_checker/output/tests/integration/test_output_integration.py::TestOutpu
tIntegration::test_imposition_output_pipeline PASSED [ 13%]
src/model_checker/output/tests/integration/test_output_integration.py::TestOutpu
tIntegration::test_logos_output_pipeline PASSED [ 13%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_initialization_batch_mode PASSED [ 14%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_initialization_sequential_mode PASSED [ 14%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_create_output_directory_default PASSED [ 14%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_create_output_directory_custom PASSED [ 15%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_save_example_batch_mode PASSED [ 15%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_save_example_sequential_mode PASSED [ 16%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_save_prompted_model PASSED [ 16%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_finalize_batch_mode PASSED [ 17%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_finalize_sequential_mode PASSED [ 17%]
src/model_checker/output/tests/integration/test_output_manager_simple.py::TestOu
tputManager::test_should_save PASSED [ 17%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_initialization PASSED [ 18%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_should_save_yes PASSED [ 18%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_should_save_no PASSED [ 19%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_should_find_more PASSED [ 19%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_get_next_model_number PASSED [ 20%]
src/model_checker/output/tests/integration/test_prompt_manager.py::TestSequentia
lSaveManager::test_prompt_directory_change PASSED [ 20%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_convert_red_text PASSED [ 20%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_convert_green_text PASSED [ 21%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_convert_mixed_colors PASSED [ 21%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_preserve_non_colored_text PASSED [ 22%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_handle_nested_formatting PASSED [ 22%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_strip_unsupported_codes PASSED [ 23%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_handle_color_codes_at_boundaries PASSED [ 23%]
src/model_checker/output/tests/unit/test_color_formatting.py::TestColorFormattin
g::test_convert_state_indicators PASSED [ 23%]
src/model_checker/output/tests/unit/test_config_simple.py::TestOutputConfig::tes
t_config_with_custom_formats PASSED [ 24%]
src/model_checker/output/tests/unit/test_config_simple.py::TestOutputConfig::tes
t_config_with_sequential PASSED [ 24%]
src/model_checker/output/tests/unit/test_config_simple.py::TestOutputConfig::tes
t_default_config PASSED [ 25%]
src/model_checker/output/tests/unit/test_config_simple.py::TestOutputConfig::tes
t_is_format_enabled PASSED [ 25%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_no_save_flag PASSED [ 26%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_no_sequential_by_default PASSED [ 26%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_save_flag_no_formats PASSED [ 26%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_save_flag_with_formats PASSED [ 27%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_sequential_flag PASSED [ 27%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_sequential_flag_overrides_setting PASSED [ 28%]
src/model_checker/output/tests/unit/test_config_simple.py::TestCreateOutputConfi
g::test_sequential_setting PASSED [ 28%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputError::test_init_w
ith_context PASSED [ 29%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputError::test_init_w
ith_message_only PASSED [ 29%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputError::test_init_w
ith_none_context PASSED [ 29%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_auto_suggestion_for_exists_error PASSED [ 30%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_auto_suggestion_for_permission_error PASSED [ 30%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_auto_suggestion_for_space_error PASSED [ 31%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_init_basic PASSED [ 31%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_init_with_custom_suggestion PASSED [ 32%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputDirectoryError::te
st_no_auto_suggestion_for_other_errors PASSED [ 32%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
auto_suggestion_for_json_serialization PASSED [ 32%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
auto_suggestion_for_markdown PASSED [ 33%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
auto_suggestion_for_notebook PASSED [ 33%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
init_basic PASSED [ 34%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
init_with_custom_suggestion PASSED [ 34%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputFormatError::test_
no_auto_suggestion_for_unknown_format PASSED [ 35%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_auto
_suggestion_for_exists_error PASSED [ 35%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_auto
_suggestion_for_permission_error PASSED [ 35%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_auto
_suggestion_for_space_error PASSED [ 36%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_init
_basic PASSED [ 36%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_init
_with_custom_suggestion PASSED [ 37%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputIOError::test_no_a
uto_suggestion_for_other_errors PASSED [ 37%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputStrategyError::tes
t_different_strategies PASSED [ 38%]
src/model_checker/output/tests/unit/test_errors.py::TestOutputStrategyError::tes
t_init PASSED [ 38%]
src/model_checker/output/tests/unit/test_errors.py::TestNotebookGenerationError:
:test_different_examples PASSED [ 38%]
src/model_checker/output/tests/unit/test_errors.py::TestNotebookGenerationError:
:test_inheritance_from_output_error PASSED [ 39%]
src/model_checker/output/tests/unit/test_errors.py::TestNotebookGenerationError:
:test_init PASSED [ 39%]
src/model_checker/output/tests/unit/test_errors.py::TestErrorStringRepresentatio
ns::test_error_context_preservation PASSED [ 40%]
src/model_checker/output/tests/unit/test_errors.py::TestErrorStringRepresentatio
ns::test_multiline_error_messages PASSED [ 40%]
src/model_checker/output/tests/unit/test_helpers.py::TestCreateTimestampedDirect
ory::test_create_handles_existing_directory PASSED [ 41%]
src/model_checker/output/tests/unit/test_helpers.py::TestCreateTimestampedDirect
ory::test_create_raises_on_os_error PASSED [ 41%]
src/model_checker/output/tests/unit/test_helpers.py::TestCreateTimestampedDirect
ory::test_create_with_custom_prefix PASSED [ 41%]
src/model_checker/output/tests/unit/test_helpers.py::TestCreateTimestampedDirect
ory::test_create_with_defaults PASSED [ 42%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_cre
ates_directory PASSED [ 42%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_emp
ty_content PASSED [ 43%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_rai
ses_output_io_error PASSED [ 43%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_sim
ple_file PASSED [ 44%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_wit
h_append_mode PASSED [ 44%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveFile::test_save_wit
h_different_encoding PASSED [ 44%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_com
plex_json PASSED [ 45%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_jso
n_uses_save_file PASSED [ 45%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_non
_serializable_raises_error PASSED [ 46%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_sim
ple_json PASSED [ 46%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_wit
h_custom_indent PASSED [ 47%]
src/model_checker/output/tests/unit/test_helpers.py::TestSaveJson::test_save_wit
h_ensure_ascii PASSED [ 47%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_all_empty_sections_returns_empty_string PASSED [ 47%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_combine_simple_sections PASSED [ 48%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_combine_with_custom_separator PASSED [ 48%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_empty_list_returns_empty_string PASSED [ 49%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_filters_empty_sections PASSED [ 49%]
src/model_checker/output/tests/unit/test_helpers.py::TestCombineMarkdownSections
::test_preserves_whitespace_in_content PASSED [ 50%]
src/model_checker/output/tests/unit/test_helpers.py::TestExtractModelData::test_
extract_from_model_found PASSED [ 50%]
src/model_checker/output/tests/unit/test_helpers.py::TestExtractModelData::test_
extract_from_model_not_found PASSED [ 50%]
src/model_checker/output/tests/unit/test_helpers.py::TestExtractModelData::test_
extract_missing_methods PASSED [ 51%]
src/model_checker/output/tests/unit/test_helpers.py::TestExtractModelData::test_
extract_partial_methods PASSED [ 51%]
src/model_checker/output/tests/unit/test_helpers.py::TestExtractModelData::test_
extract_with_none_values PASSED [ 52%]
src/model_checker/output/tests/unit/test_helpers.py::TestEnsureDirectoryExists::
test_ensure_existing_directory PASSED [ 52%]
src/model_checker/output/tests/unit/test_helpers.py::TestEnsureDirectoryExists::
test_ensure_nested_directory PASSED [ 52%]
src/model_checker/output/tests/unit/test_helpers.py::TestEnsureDirectoryExists::
test_ensure_new_directory PASSED [ 53%]
src/model_checker/output/tests/unit/test_helpers.py::TestEnsureDirectoryExists::
test_ensure_raises_on_os_error PASSED [ 53%]
src/model_checker/output/tests/unit/test_helpers.py::TestGetFileExtension::test_
get_extension_empty_map PASSED [ 54%]
src/model_checker/output/tests/unit/test_helpers.py::TestGetFileExtension::test_
get_known_extensions PASSED [ 54%]
src/model_checker/output/tests/unit/test_helpers.py::TestGetFileExtension::test_
get_unknown_extension PASSED [ 55%]
src/model_checker/output/tests/unit/test_input_provider.py::TestInputProvider::t
est_base_class_requires_implementation PASSED [ 55%]
src/model_checker/output/tests/unit/test_input_provider.py::TestInputProvider::t
est_interface_contract PASSED [ 55%]
src/model_checker/output/tests/unit/test_input_provider.py::TestConsoleInputProv
ider::test_get_input_calls_builtin_input PASSED [ 56%]
src/model_checker/output/tests/unit/test_input_provider.py::TestConsoleInputProv
ider::test_get_input_preserves_prompt_exactly PASSED [ 56%]
src/model_checker/output/tests/unit/test_input_provider.py::TestConsoleInputProv
ider::test_handles_keyboard_interrupt PASSED [ 57%]
src/model_checker/output/tests/unit/test_input_provider.py::TestMockInputProvide
r::test_raises_when_responses_exhausted PASSED [ 57%]
src/model_checker/output/tests/unit/test_input_provider.py::TestMockInputProvide
r::test_reset_functionality PASSED [ 58%]
src/model_checker/output/tests/unit/test_input_provider.py::TestMockInputProvide
r::test_returns_predefined_responses PASSED [ 58%]
src/model_checker/output/tests/unit/test_input_provider.py::TestMockInputProvide
r::test_single_response_convenience PASSED [ 58%]
src/model_checker/output/tests/unit/test_input_provider.py::TestMockInputProvide
r::test_tracks_prompts_received PASSED [ 59%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_save_models_json_structure PASSED [ 59%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_json_formatting PASSED [ 60%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_empty_models_json PASSED [ 60%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_json_encoding PASSED [ 61%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_batch_formatting PASSED [ 61%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_json_formatter_indentation PASSED [ 61%]
src/model_checker/output/tests/unit/test_json_serialization.py::TestJSONSerializ
ation::test_ensure_ascii_option PASSED [ 62%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_state_type_with_colors PASSED [ 62%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_state_type_no_colors PASSED [ 63%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_example_with_model PASSED [ 63%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_example_no_model PASSED [ 64%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_batch PASSED [ 64%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_get_file_extension PASSED [ 64%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_example_with_empty_output PASSED [ 65%]
src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownForm
atter::test_format_complete_example PASSED [ 65%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_format_batch_generates_notebook PASSED [ 66%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_format_batch_requires_context PASSED [ 66%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_format_example_collects_data PASSED [ 67%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_format_for_streaming PASSED [ 67%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_format_for_streaming_requires_context PASSED [ 67%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_formatter_initialization PASSED [ 68%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_get_file_extension PASSED [ 68%]
src/model_checker/output/tests/unit/test_notebook_formatter.py::TestNotebookForm
atter::test_set_context PASSED [ 69%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_progress_animation PASSED [ 69%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_immediate_completion PASSED [ 70%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_timeout_completion PASSED [ 70%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_count_tracking PASSED [ 70%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_progress_bar_visual PASSED [ 71%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_thread_cleanup PASSED [ 71%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_color_support_detection PASSED [ 72%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_color_progress_bar PASSED [ 72%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_custom_start_time PASSED [ 73%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_freeze_at_current PASSED [ 73%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_freeze_without_start PASSED [ 73%]
src/model_checker/output/tests/unit/test_progress_animated.py::TestTimeBasedProg
ress::test_freeze_elapsed_time_consistency PASSED [ 74%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_single_model_progress PASSED [ 74%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_multiple_model_progress PASSED [ 75%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_isomorphic_tracking PASSED [ 75%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_timing_tracking PASSED [ 76%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_not_found_tracking PASSED [ 76%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgress::
test_finish_cleanup PASSED [ 76%]
src/model_checker/output/tests/unit/test_progress_core.py::TestProgressBar::test
_abstract_interface PASSED [ 77%]
src/model_checker/output/tests/unit/test_progress_core.py::TestProgressBar::test
_interface_methods_defined PASSED [ 77%]
src/model_checker/output/tests/unit/test_progress_core.py::TestProgressBar::test
_concrete_implementation PASSED [ 78%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_zero_models PASSED [ 78%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_custom_start_time PASSED [ 79%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_multiple_starts_same_model PASSED [ 79%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_skipped_count_reset PASSED [ 79%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_no_display_provided PASSED [ 80%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_stop_animation_only PASSED [ 80%]
src/model_checker/output/tests/unit/test_progress_core.py::TestUnifiedProgressEd
geCases::test_stop_animation_only_no_bar PASSED [ 81%]
src/model_checker/output/tests/unit/test_progress_display.py::TestProgressDispla
y::test_abstract_methods PASSED [ 81%]
src/model_checker/output/tests/unit/test_progress_display.py::TestProgressDispla
y::test_interface_methods PASSED [ 82%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_initialization_with_stream PASSED [ 82%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_initialization_default_stream PASSED [ 82%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_enabled_always_true PASSED [ 83%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_stream_assignment PASSED [ 83%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_last_length_tracking PASSED [ 84%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_disabled_update_noop PASSED [ 84%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_update_with_carriage_return PASSED [ 85%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_complete PASSED [ 85%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_clear PASSED [ 85%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_clear_without_previous_message PASSED [ 86%]
src/model_checker/output/tests/unit/test_progress_display.py::TestTerminalDispla
y::test_terminal_width_handling PASSED [ 86%]
src/model_checker/output/tests/unit/test_progress_display.py::TestBatchDisplay::
test_initialization PASSED [ 87%]
src/model_checker/output/tests/unit/test_progress_display.py::TestBatchDisplay::
test_update_is_noop PASSED [ 87%]
src/model_checker/output/tests/unit/test_progress_display.py::TestBatchDisplay::
test_complete_is_noop PASSED [ 88%]
src/model_checker/output/tests/unit/test_progress_display.py::TestBatchDisplay::
test_clear_is_noop PASSED [ 88%]
src/model_checker/output/tests/unit/test_progress_display.py::TestBatchDisplay::
test_all_methods_are_noops PASSED [ 88%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
initialization_default PASSED [ 89%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
initialization_custom PASSED [ 89%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
progress_chars PASSED [ 90%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
start_creates_thread PASSED [ 90%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
stop_stops_thread PASSED [ 91%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
spinner_animation PASSED [ 91%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
stop_clears_display PASSED [ 91%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
stop_without_start PASSED [ 92%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
start_stop_behavior PASSED [ 92%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
multiple_start_calls PASSED [ 93%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
current_index_wrapping PASSED [ 93%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
thread_daemon_mode PASSED [ 94%]
src/model_checker/output/tests/unit/test_progress_spinner.py::TestSpinner::test_
custom_message_formatting PASSED [ 94%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_promp
t_yes_responses PASSED [ 94%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_promp
t_no_responses PASSED [ 95%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_promp
t_default_on_empty PASSED [ 95%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_promp
t_invalid_input_retry PASSED [ 96%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_promp
t_message_display PASSED [ 96%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptYesNo::test_keybo
ard_interrupt_handling PASSED [ 97%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_vali
d_choice_selection PASSED [ 97%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_choi
ce_by_letter PASSED [ 97%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_inva
lid_choice_retry PASSED [ 98%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_choi
ce_display_format PASSED [ 98%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_sing
le_choice_auto_select PASSED [ 99%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_empt
y_choices_error PASSED [ 99%]
src/model_checker/output/tests/unit/test_prompts.py::TestPromptChoice::test_keyb
oard_interrupt_returns_none PASSED [100%]

============================== slowest durations ===============================
0.70s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_freeze_elapsed_time_consistency
0.70s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_thread_cleanup
0.40s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_progress_animation
0.30s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_multiple_model_progress
0.30s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_not_found_tracking
0.30s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_spinner_animation
0.30s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_timeout_completion
0.30s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_freeze_at_current
0.20s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_isomorphic_tracking
0.20s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_immediate_completion
0.20s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_timing_tracking
0.20s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_count_tracking
0.20s call     src/model_checker/output/tests/unit/test_progress_animated.py::Te
stTimeBasedProgress::test_custom_start_time
0.20s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgressEdgeCases::test_stop_animation_only
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_stop_stops_thread
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_start_stop_behavior
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_stop_clears_display
0.10s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgressEdgeCases::test_skipped_count_reset
0.10s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_single_model_progress
0.10s call     src/model_checker/output/tests/unit/test_progress_core.py::TestUn
ifiedProgress::test_finish_cleanup
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_multiple_start_calls
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_thread_daemon_mode
0.10s call     src/model_checker/output/tests/unit/test_progress_spinner.py::Tes
tSpinner::test_start_creates_thread

(679 durations < 0.005s hidden.  Use -vv to show these durations.)
============================= 234 passed in 6.75s ==============================
  Running package tests for output.notebook
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 14 items                                                             

src/model_checker/output/notebook/tests/integration/test_notebook_generation.py:
:TestNotebookGeneration::test_generate_notebook_raises_on_missing_template PASSE
D [  7%]
src/model_checker/output/notebook/tests/integration/test_notebook_generation.py:
:TestNotebookGeneration::test_generate_notebook_raises_on_no_theories PASSED [ 1
4%]
src/model_checker/output/notebook/tests/integration/test_notebook_generation.py:
:TestNotebookGeneration::test_generate_notebook_stream_creates_file PASSED [ 21%
]
src/model_checker/output/notebook/tests/integration/test_notebook_generation.py:
:TestNotebookGeneration::test_template_loading_for_different_theories PASSED [ 2
8%]
src/model_checker/output/notebook/tests/integration/test_notebook_generation.py:
:TestNotebookGeneration::test_template_placeholder_substitution PASSED [ 35%]
src/model_checker/output/notebook/tests/unit/test_notebook_writer.py::TestNotebo
okWriter::test_notebook_writer_context_manager PASSED [ 42%]
src/model_checker/output/notebook/tests/unit/test_notebook_writer.py::TestNotebo
okWriter::test_notebook_writer_creates_valid_json PASSED [ 50%]
src/model_checker/output/notebook/tests/unit/test_notebook_writer.py::TestNotebo
okWriter::test_notebook_writer_handles_empty_cells PASSED [ 57%]
src/model_checker/output/notebook/tests/unit/test_notebook_writer.py::TestNotebo
okWriter::test_notebook_writer_metadata_structure PASSED [ 64%]
src/model_checker/output/notebook/tests/unit/test_template_loader_simple.py::Tes
tTemplateLoaderSimple::test_get_template_for_imposition_semantics PASSED [ 71%]
src/model_checker/output/notebook/tests/unit/test_template_loader_simple.py::Tes
tTemplateLoaderSimple::test_get_template_for_logos_semantics PASSED [ 78%]
src/model_checker/output/notebook/tests/unit/test_template_loader_simple.py::Tes
tTemplateLoaderSimple::test_get_template_for_unknown_semantics PASSED [ 85%]
src/model_checker/output/notebook/tests/unit/test_template_loader_simple.py::Tes
tTemplateLoaderSimple::test_get_template_for_witness_semantics PASSED [ 92%]
src/model_checker/output/notebook/tests/unit/test_template_loader_simple.py::Tes
tTemplateLoaderSimple::test_template_loader_returns_instances PASSED [100%]

============================== slowest durations ===============================
0.01s call     src/model_checker/output/notebook/tests/integration/test_notebook
_generation.py::TestNotebookGeneration::test_generate_notebook_stream_creates_fi
le

(41 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 14 passed in 1.70s ==============================
  Running package tests for settings
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 22 items                                                             

src/model_checker/settings/tests/integration/test_settings_pipeline.py::TestSett
ingsPipeline::test_complete_settings_flow PASSED [  4%]
src/model_checker/settings/tests/integration/test_settings_pipeline.py::TestSett
ingsPipeline::test_validation_warnings PASSED [  9%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_error_str_formatting PASSED [ 13%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_extracted_method_integration PASSED [ 18%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_missing_required_error PASSED [ 22%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_non_strict_mode_warns_only PASSED [ 27%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_range_error PASSED [ 31%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_range_validation_success PASSED [ 36%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_strict_mode_raises_on_unknown_setting PASSED [ 40%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_theory_compatibility_error PASSED [ 45%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_type_conversion_error PASSED [ 50%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_type_conversion_success PASSED [ 54%]
src/model_checker/settings/tests/unit/test_error_handling.py::TestErrorHandling:
:test_unknown_setting_error_suggestions PASSED [ 59%]
src/model_checker/settings/tests/unit/test_settings.py::TestSettingsManager::tes
t_apply_flag_overrides PASSED [ 63%]
src/model_checker/settings/tests/unit/test_settings.py::TestSettingsManager::tes
t_get_complete_settings PASSED [ 68%]
src/model_checker/settings/tests/unit/test_settings.py::TestSettingsManager::tes
t_validate_example_settings PASSED [ 72%]
src/model_checker/settings/tests/unit/test_settings.py::TestSettingsManager::tes
t_validate_general_settings PASSED [ 77%]
src/model_checker/settings/tests/unit/test_settings.py::TestSolverValidation::te
st_solver_in_complete_settings PASSED [ 81%]
src/model_checker/settings/tests/unit/test_settings.py::TestSolverValidation::te
st_validate_solver_cvc5 PASSED [ 86%]
src/model_checker/settings/tests/unit/test_settings.py::TestSolverValidation::te
st_validate_solver_default PASSED [ 90%]
src/model_checker/settings/tests/unit/test_settings.py::TestSolverValidation::te
st_validate_solver_invalid_raises PASSED [ 95%]
src/model_checker/settings/tests/unit/test_settings.py::TestSolverValidation::te
st_validate_solver_z3 PASSED [100%]

============================== slowest durations ===============================

(66 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 22 passed in 0.98s ==============================
  Running package tests for solver
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 34 items                                                             

src/model_checker/solver/tests/unit/test_equivalence.py::TestBasicEquivalence::t
est_simple_sat_equivalence PASSED [  2%]
src/model_checker/solver/tests/unit/test_equivalence.py::TestBasicEquivalence::t
est_simple_unsat_equivalence PASSED [  5%]
src/model_checker/solver/tests/unit/test_equivalence.py::TestBitvectorEquivalenc
e::test_bitvec_arithmetic PASSED [  8%]
src/model_checker/solver/tests/unit/test_equivalence.py::TestPushPopEquivalence:
:test_push_pop_sat_transitions PASSED [ 11%]
src/model_checker/solver/tests/unit/test_protocols.py::TestSolverResult::test_re
sult_constants PASSED [ 14%]
src/model_checker/solver/tests/unit/test_protocols.py::TestSolverResult::test_fr
om_z3_sat PASSED [ 17%]
src/model_checker/solver/tests/unit/test_protocols.py::TestSolverResult::test_fr
om_z3_unsat PASSED [ 20%]
src/model_checker/solver/tests/unit/test_protocols.py::TestSolverResult::test_is
_sat PASSED [ 23%]
src/model_checker/solver/tests/unit/test_protocols.py::TestSolverResult::test_is
_unsat PASSED [ 26%]
src/model_checker/solver/tests/unit/test_protocols.py::TestProtocolCompliance::t
est_z3_solver_matches_protocol PASSED [ 29%]
src/model_checker/solver/tests/unit/test_protocols.py::TestProtocolCompliance::t
est_z3_model_matches_protocol PASSED [ 32%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendDetection::test
_detect_z3_returns_true PASSED [ 35%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendDetection::test
_detect_cvc5_returns_bool PASSED [ 38%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendDetection::test
_list_available_backends PASSED [ 41%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendSelection::test
_default_backend_is_z3 PASSED [ 44%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendSelection::test
_cli_override_takes_priority PASSED [ 47%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendSelection::test
_settings_used_when_no_cli_override PASSED [ 50%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendSelection::test
_environment_variable_override PASSED [ 52%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendSelection::test
_invalid_cli_backend_raises PASSED [ 55%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendValidation::tes
t_validate_z3_succeeds PASSED [ 58%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendValidation::tes
t_validate_unknown_backend_raises PASSED [ 61%]
src/model_checker/solver/tests/unit/test_registry.py::TestBackendValidation::tes
t_validate_missing_cvc5_raises PASSED [ 64%]
src/model_checker/solver/tests/unit/test_registry.py::TestClearCliBackend::test_
clear_cli_backend PASSED [ 67%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterBasic::test
_create_adapter PASSED [ 70%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterBasic::test
_adapter_satisfies_protocol PASSED [ 73%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterBasic::test
_simple_sat PASSED [ 76%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterBasic::test
_simple_unsat PASSED [ 79%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterBasic::test
_model_evaluation PASSED [ 82%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterTracking::t
est_assert_tracked PASSED [ 85%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterTracking::t
est_unsat_core_extraction PASSED [ 88%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterPushPop::te
st_push_pop_basic PASSED [ 91%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterOptions::te
st_set_timeout PASSED [ 94%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterOptions::te
st_reset PASSED [ 97%]
src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3AdapterOptions::te
st_raw_solver_access PASSED [100%]

============================== slowest durations ===============================
0.02s setup    src/model_checker/solver/tests/unit/test_equivalence.py::TestBasi
cEquivalence::test_simple_sat_equivalence

(101 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 34 passed in 1.78s ==============================
  Running package tests for syntactic
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 71 items                                                             

src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_empty_collection PASSED [  1%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_add_single_operator PASSED [  2%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_add_multiple_operators PASSED [  4%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_init_with_operators PASSED [  5%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_add_duplicate_operator PASSED [  7%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_add_operator_without_name PASSED [  8%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_add_invalid_type PASSED [  9%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_merge_collections PASSED [ 11%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_iter_collection PASSED [ 12%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestOperatorCo
llection::test_items_method PASSED [ 14%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_atomic_sentence PASSED [ 15%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_extremal_operators PASSED [ 16%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_invalid_atom PASSED [ 18%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_unary_operator PASSED [ 19%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_binary_operator PASSED [ 21%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_nested_operators PASSED [ 22%]
src/model_checker/syntactic/tests/integration/test_collection.py::TestApplyOpera
tor::test_apply_non_string_operator PASSED [ 23%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomSort::test_atom_so
rt_exists PASSED [ 25%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomSort::test_atom_so
rt_name PASSED [ 26%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_creation PASSED [ 28%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_sort PASSED [ 29%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_unique_names PASSED [ 30%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_consistency PASSED [ 32%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_in_constraints PASSED [ 33%]
src/model_checker/syntactic/tests/unit/test_atoms.py::TestAtomVal::test_atom_val
_negative_index PASSED [ 35%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_abstract_class PASSED [ 36%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_missing_name PASSED [ 38%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_missing_arity PASSED [ 39%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_creation PASSED [ 40%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_str_repr PASSED [ 42%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_equality PASSED [ 43%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorBasics::te
st_operator_hash PASSED [ 45%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorPrinting::
test_general_print PASSED [ 46%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestOperatorPrinting::
test_general_print_with_arguments PASSED [ 47%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestDefinedOperator::t
est_defined_operator_abstract PASSED [ 49%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestDefinedOperator::t
est_defined_operator_primitive_false PASSED [ 50%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestDefinedOperator::t
est_defined_operator_arity_validation PASSED [ 52%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestDefinedOperator::t
est_defined_operator_missing_arity PASSED [ 53%]
src/model_checker/syntactic/tests/unit/test_operators.py::TestDefinedOperator::t
est_defined_operator_valid PASSED [ 54%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentenceBasics::tes
t_atomic_sentence PASSED [ 56%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentenceBasics::tes
t_unary_operator PASSED [ 57%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentenceBasics::tes
t_binary_operator PASSED [ 59%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentenceBasics::tes
t_nested_sentence PASSED [ 60%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSentenceBasics::tes
t_str_repr PASSED [ 61%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_prefix_atomic PASSED [ 63%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_prefix_unary PASSED [ 64%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_prefix_binary PASSED [ 66%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_string PASSED [ 67%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_list_atomic PASSED [ 69%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_list_unary PASSED [ 70%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_list_binary PASSED [ 71%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_nested PASSED [ 73%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_sentence_object PASSED [ 74%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestPrefixInfixConversi
on::test_infix_type_error PASSED [ 76%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSpecialOperators::t
est_top_operator PASSED [ 77%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestSpecialOperators::t
est_bot_operator PASSED [ 78%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestUpdateMethods::test
_update_types_atomic PASSED [ 80%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestUpdateMethods::test
_update_types_operator PASSED [ 81%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestUpdateMethods::test
_update_objects PASSED [ 83%]
src/model_checker/syntactic/tests/unit/test_sentence.py::TestUpdateMethods::test
_update_proposition PASSED [ 84%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestSyntaxBasics::test_em
pty_syntax PASSED [ 85%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestSyntaxBasics::test_si
mple_premise PASSED [ 87%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestSyntaxBasics::test_si
mple_conclusion PASSED [ 88%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestSyntaxBasics::test_co
mplex_sentence PASSED [ 90%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestSyntaxBasics::test_sh
ared_subsentences PASSED [ 91%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestOperatorHandling::tes
t_defined_operator PASSED [ 92%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestOperatorHandling::tes
t_extremal_operators PASSED [ 94%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestCircularityCheck::tes
t_no_circularity PASSED [ 95%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestCircularityCheck::tes
t_direct_circularity PASSED [ 97%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestCircularityCheck::tes
t_indirect_circularity PASSED [ 98%]
src/model_checker/syntactic/tests/unit/test_syntax.py::TestCircularityCheck::tes
t_missing_dependency PASSED [100%]

============================== slowest durations ===============================

(213 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 71 passed in 0.98s ==============================
  Running package tests for theory_lib
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 24 items                                                             

src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_v
ersion_utilities PASSED [  4%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_v
erification PASSED [  8%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_p
rint_report PASSED [ 12%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_t
heory_version_format[logos] PASSED [ 16%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_t
heory_version_format[exclusion] PASSED [ 20%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_t
heory_version_format[imposition] PASSED [ 25%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_t
heory_version_format[bimodal] PASSED [ 29%]
src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_m
etadata_files_exist PASSED [ 33%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestTheoryErrorH
ierarchy::test_theory_error_basic_creation PASSED [ 37%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestTheoryErrorH
ierarchy::test_theory_error_with_context PASSED [ 41%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestWitnessError
Handling::test_witness_semantic_error_inherits_theory PASSED [ 45%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestWitnessError
Handling::test_witness_predicate_error_construction PASSED [ 50%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestWitnessError
Handling::test_witness_registry_error_basic PASSED [ 54%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestWitnessError
Handling::test_witness_constraint_error_basic PASSED [ 58%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestImpositionEr
rorHandling::test_imposition_semantic_error_inherits_theory PASSED [ 62%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestImpositionEr
rorHandling::test_imposition_operation_error_basic PASSED [ 66%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestImpositionEr
rorHandling::test_imposition_helper_error_construction PASSED [ 70%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestLogosErrorHa
ndling::test_logos_subtheory_error_basic PASSED [ 75%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestLogosErrorHa
ndling::test_logos_protocol_error_construction PASSED [ 79%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestZ3Integratio
nErrorHandling::test_z3_integration_error_with_status PASSED [ 83%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestZ3Integratio
nErrorHandling::test_z3_timeout_error_construction PASSED [ 87%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestErrorContext
AndSuggestions::test_error_context_preservation PASSED [ 91%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestErrorContext
AndSuggestions::test_error_chaining_preserves_context PASSED [ 95%]
src/model_checker/theory_lib/tests/unit/test_error_handling.py::TestErrorContext
AndSuggestions::test_error_suggestions_are_actionable PASSED [100%]

============================== slowest durations ===============================

(72 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 24 passed in 1.71s ==============================
  Running package tests for utils
============================= test session starts ==============================
platform linux -- Python 3.12.13, pytest-9.0.2, pluggy-1.6.0 -- /nix/store/rhvmf
219ciwqx89q5y2nzbz18xi8m41w-python3-3.12.13-env/bin/python3.12
cachedir: .pytest_cache
hypothesis profile 'default'
rootdir: /home/benjamin/Projects/Logos/ModelChecker/code
configfile: pyproject.toml
plugins: hypothesis-6.150.2, cov-7.0.0, timeout-2.4.0, anyio-4.12.1
collected 75 items                                                             

src/model_checker/utils/tests/unit/test_bitvector.py::TestBinaryBitvector::test_
binary_bitvector_mod4 PASSED [  1%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBinaryBitvector::test_
binary_bitvector_not_mod4 PASSED [  2%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestIntToBinary::test_basi
c_conversion PASSED [  4%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestIntToBinary::test_padd
ing PASSED [  5%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestIndexToSubstate::test_
single_letters PASSED [  6%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestIndexToSubstate::test_
double_letters PASSED [  8%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestIndexToSubstate::test_
multiple_letters PASSED [  9%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToSubstates::tes
t_null_state PASSED [ 10%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToSubstates::tes
t_single_state PASSED [ 12%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToSubstates::tes
t_fusion_state PASSED [ 13%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToSubstates::tes
t_integer_input PASSED [ 14%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToSubstates::tes
t_invalid_input PASSED [ 16%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToWorldstate::te
st_single_letters PASSED [ 17%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToWorldstate::te
st_double_letters PASSED [ 18%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToWorldstate::te
st_integer_input PASSED [ 20%]
src/model_checker/utils/tests/unit/test_bitvector.py::TestBitvecToWorldstate::te
st_invalid_input PASSED [ 21%]
src/model_checker/utils/tests/unit/test_context.py::test_z3_context_manager_exis
ts PASSED [ 22%]
src/model_checker/utils/tests/unit/test_context.py::test_reset_context_method_ex
ists PASSED [ 24%]
src/model_checker/utils/tests/unit/test_context.py::test_reset_context_clears_z3
_state PASSED [ 25%]
src/model_checker/utils/tests/unit/test_context.py::test_reset_context_handles_m
issing_attributes PASSED [ 26%]
src/model_checker/utils/tests/unit/test_context.py::test_multiple_resets PASSED 
[ 28%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
empty_frozenset PASSED [ 29%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
empty_set PASSED [ 30%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
frozenset_input PASSED [ 32%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
mixed_types PASSED [ 33%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
multiple_elements_sorted PASSED [ 34%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
numeric_elements PASSED [ 36%]
src/model_checker/utils/tests/unit/test_formatting.py::TestPrettySetPrint::test_
single_element_set PASSED [ 37%]
src/model_checker/utils/tests/unit/test_formatting.py::TestNotImplementedString:
:test_empty_class_name PASSED [ 38%]
src/model_checker/utils/tests/unit/test_formatting.py::TestNotImplementedString:
:test_generic_class_message PASSED [ 40%]
src/model_checker/utils/tests/unit/test_formatting.py::TestNotImplementedString:
:test_operator_defaults_message PASSED [ 41%]
src/model_checker/utils/tests/unit/test_formatting.py::TestNotImplementedString:
:test_proposition_defaults_message PASSED [ 42%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_deeply_
nested PASSED [ 44%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_empty_l
ist PASSED [ 45%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_empty_n
ested_lists PASSED [ 46%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_flat_li
st PASSED [ 48%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_mixed_t
ypes PASSED [ 49%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_multipl
e_levels_nested PASSED [ 50%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_none_va
lues PASSED [ 52%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_single_
level_nested PASSED [ 53%]
src/model_checker/utils/tests/unit/test_formatting.py::TestFlatten::test_string_
elements PASSED [ 54%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_at
omic_sentence PASSED [ 56%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_nu
llary_operators PASSED [ 57%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_un
ary_operators PASSED [ 58%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_bi
nary_operators PASSED [ 60%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_ne
sted_expressions PASSED [ 61%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_co
mplex_nested_expressions PASSED [ 62%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_em
pty_tokens PASSED [ 64%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_mi
ssing_closing_parenthesis PASSED [ 65%]
src/model_checker/utils/tests/unit/test_parsing.py::TestParseExpression::test_in
complete_expression PASSED [ 66%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_simple
_binary PASSED [ 68%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_nested
_left PASSED [ 69%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_nested
_right PASSED [ 70%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_both_n
ested PASSED [ 72%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_unbala
nced_parentheses PASSED [ 73%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_missin
g_operator PASSED [ 74%]
src/model_checker/utils/tests/unit/test_parsing.py::TestOpLeftRight::test_nullar
y_operators_handling PASSED [ 76%]
src/model_checker/utils/tests/unit/test_parsing.py::TestIntegration::test_logos_
style_formulas PASSED [ 77%]
src/model_checker/utils/tests/unit/test_parsing.py::TestIntegration::test_bimoda
l_formulas PASSED [ 78%]
src/model_checker/utils/tests/unit/test_parsing.py::TestIntegration::test_real_w
orld_example PASSED [ 80%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_colo
r_code_type PASSED [ 81%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_conf
ig_dict_type PASSED [ 82%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_path
like_type PASSED [ 84%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_tabl
e_types PASSED [ 85%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_test
_related_types PASSED [ 86%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_type
_imports PASSED [ 88%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_vers
ion_tuple_type PASSED [ 89%]
src/model_checker/utils/tests/unit/test_types.py::TestTypeDefinitions::test_z3_t
ype_aliases PASSED [ 90%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestForAll::test_forall_s
ingle_variable PASSED [ 92%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestForAll::test_forall_c
ontradiction PASSED [ 93%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestForAll::test_forall_m
ultiple_variables PASSED [ 94%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestExists::test_exists_s
ingle_variable PASSED [ 96%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestExists::test_exists_n
o_solution PASSED [ 97%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestExists::test_exists_m
ultiple_variables PASSED [ 98%]
src/model_checker/utils/tests/unit/test_z3_helpers.py::TestMixedQuantifiers::tes
t_forall_exists_nesting PASSED [100%]

============================== slowest durations ===============================
0.01s setup    src/model_checker/utils/tests/unit/test_z3_helpers.py::TestForAll
::test_forall_multiple_variables
0.01s call     src/model_checker/utils/tests/unit/test_bitvector.py::TestBinaryB
itvector::test_binary_bitvector_mod4
0.01s call     src/model_checker/utils/tests/unit/test_context.py::test_multiple
_resets
0.01s call     src/model_checker/utils/tests/unit/test_context.py::test_reset_co
ntext_clears_z3_state

(221 durations < 0.005s hidden.  Use -vv to show these durations.)
============================== 75 passed in 1.00s ==============================

================================================================================
Test Summary:

Theory Tests:
  bimodal (examples): PASSED
    Time: 5.64s
    Example count: 22 examples
  bimodal (unit): PASSED
    Time: 9.58s
  logos (examples): PASSED
    Time: 36.06s
    Subtheory example counts:
      constitutive: 34 examples (12.87s)
      counterfactual: 37 examples (12.36s)
      extensional: 14 examples (3.13s)
      modal: 18 examples (3.76s)
      relevance: 20 examples (3.93s)
      Total: 123 examples (36.05s)
  logos (unit): PASSED
    Time: 49.63s

Package Tests:
  builder: PASSED
  iterate: PASSED
  jupyter: PASSED
  models: PASSED
  output: PASSED
  output.notebook: PASSED
  settings: PASSED
  solver: PASSED
  syntactic: PASSED
  theory_lib: PASSED
  utils: PASSED

SUCCESS: All tests passed!

