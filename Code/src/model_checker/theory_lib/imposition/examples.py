"""
Examples Module for Imposition Theory (Compatibility wrapper)

This module maintains backward compatibility by re-exporting examples
from the new organized examples package structure.

The imposition theory implements Fine's truthmaker semantics for counterfactuals
through the imposition operation, which imposes a state upon a world to create
alternative worlds. This enables a distinctive approach to counterfactual reasoning.

Usage:
------
This module can be run directly with model-checker or dev_cli.py:

```bash
model-checker path/to/this/examples.py
# or in development:
./dev_cli.py path/to/this/examples.py
```

To use a specific collection of examples, modify the example_range dictionary below.
"""

import os
import sys

from .operators import imposition_operators  # Use the OperatorCollection
from .semantic import ImpositionSemantics, ImpositionModelStructure as ModelStructure
from model_checker.theory_lib.logos.semantic import LogosProposition as Proposition

# Import all examples and configurations from the organized package
from .examples.basic import basic_examples, basic_countermodels, basic_theorems
from .examples.complex import complex_examples, complex_countermodels, complex_theorems
from .examples.edge_cases import edge_case_examples
from .examples.test_suite import (
    all_examples,
    all_countermodels as countermodel_examples,
    all_theorems as theorem_examples,
    unit_tests,
    test_example_range,
    all_imposition_examples,
    general_settings,
    semantic_theories,
    imposition_theory,
)

# Standard imports
sys.path.append(os.path.dirname(__file__))

# Default example range (curated subset for direct execution)
example_range = {

    # COUNTERMODELS
    # "IM_CM_0": basic_examples["IM_CM_0"],    # COUNTERFACTUAL AND MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    "IM_CM_1": basic_examples["IM_CM_1"],    # COUNTERFACTUAL ANTECEDENT STRENGTHENING
    # "IM_CM_2": basic_examples["IM_CM_2"],    # MIGHT COUNTERFACTUAL ANTECEDENT STRENGTHENING
    # "IM_CM_3": basic_examples["IM_CM_3"],    # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH POSSIBILITY
    # "IM_CM_4": basic_examples["IM_CM_4"],    # COUNTERFACTUAL ANTECEDENT STRENGTHENING WITH NEGATION
    # "IM_CM_5": basic_examples["IM_CM_5"],    # COUNTERFACTUAL DOUBLE ANTECEDENT STRENGTHENING
    # "IM_CM_6": basic_examples["IM_CM_6"],    # WEAKENED MONOTONICITY
    # "IM_CM_7": basic_examples["IM_CM_7"],    # COUNTERFACTUAL CONTRAPOSITION
    # "IM_CM_8": basic_examples["IM_CM_8"],    # COUNTERFACTUAL CONTRAPOSITION WITH NEGATION
    # "IM_CM_9": basic_examples["IM_CM_9"],    # COUNTERFACTUAL CONTRAPOSITION WITH TWO NEGATIONS
    # "IM_CM_10": complex_examples["IM_CM_10"],  # TRANSITIVITY
    # "IM_CM_11": complex_examples["IM_CM_11"],  # COUNTERFACTUAL TRANSITIVITY WITH NEGATION
    # "IM_CM_12": complex_examples["IM_CM_12"],  # COUNTERFACTUAL TRANSITIVITY WITH TWO NEGATIONS
    # "IM_CM_13": complex_examples["IM_CM_13"],  # SOBEL SEQUENCE
    # "IM_CM_14": complex_examples["IM_CM_14"],  # SOBEL SEQUENCE WITH POSSIBILITY
    # "IM_CM_15": complex_examples["IM_CM_15"],  # COUNTERFACTUAL EXCLUDED MIDDLE
    # "IM_CM_16": complex_examples["IM_CM_16"],  # SIMPLIFICATION OF DISJUNCTIVE CONSEQUENT
    # "IM_CM_17": complex_examples["IM_CM_17"],  # INTRODUCTION OF DISJUNCTIVE ANTECEDENT
    # "IM_CM_18": complex_examples["IM_CM_18"],  # MUST FACTIVITY
    # "IM_CM_19": complex_examples["IM_CM_19"],  # COUNTERFACTUAL EXPORTATION
    # "IM_CM_20": complex_examples["IM_CM_20"],  # COUNTERFACTUAL EXPORTATION WITH POSSIBILITY
    # "IM_CM_21": complex_examples["IM_CM_21"],  # COUNTERFACTUAL NEGATION DISTRIBUTION
    # "IM_CM_22": complex_examples["IM_CM_22"],  # REVERSE DEFINITION OF NEC
    # "IM_CM_23": complex_examples["IM_CM_23"],  # CONTRADICTION TO IMPOSSIBILITY
    # "IM_CM_24": complex_examples["IM_CM_24"],  # NECESSITY OF COUNTERFACTUALS
    # "IM_CM_25": complex_examples["IM_CM_25"],  # INCOMPATIBILITY TO COUNTERFACTUAL
    # "IM_CM_26": complex_examples["IM_CM_26"],  # IMPOSITION TO LOGOS COUNTERFACTUAL
    # "IM_CM_27": complex_examples["IM_CM_27"],  # LOGOS TO IMPOSITION COUNTERFACTUAL
    # "IM_CM_28": complex_examples["IM_CM_28"],  # REVERSE FLIP DEFINITION OF NEC

    # THEOREMS
    # "IM_TH_1": basic_examples["IM_TH_1"],    # COUNTERFACTUAL IDENTITY
    # "IM_TH_2": basic_examples["IM_TH_2"],    # COUNTERFACTUAL MODUS PONENS
    # "IM_TH_3": basic_examples["IM_TH_3"],    # WEAKENED TRANSITIVITY
    # "IM_TH_4": basic_examples["IM_TH_4"],    # ANTECEDENT DISJUNCTION TO CONJUNCTION
    "IM_TH_5": basic_examples["IM_TH_5"],    # SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    # "IM_TH_6": complex_examples["IM_TH_6"],    # DOUBLE SIMPLIFICATION OF DISJUNCTIVE ANTECEDENT
    # "IM_TH_7": complex_examples["IM_TH_7"],    # COUNTERFACTUAL DISJUNCTION INTRODUCTION
    # "IM_TH_8": complex_examples["IM_TH_8"],    # COUNTERFACTUAL CONSEQUENT WEAKENING
    # "IM_TH_9": complex_examples["IM_TH_9"],    # COUNTERFACTUAL CONJUNCTION INTRODUCTION
    # "IM_TH_10": complex_examples["IM_TH_10"],  # MIGHT FACTIVITY
    # "IM_TH_11": complex_examples["IM_TH_11"],  # DEFINITION OF NEC

    # SPECIAL
    # "IM_TR_0": edge_case_examples["IM_TR_0"],  # NO PREMISES OR CONCLUSIONS

}


# The report will be printed by ModelRunner after all examples complete
# No atexit registration needed - the runner controls when reports print