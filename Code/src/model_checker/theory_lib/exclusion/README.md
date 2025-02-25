# Model-Checker Instructions

This document provides an overview of the package contents for the _exclusion semantics_ defended by [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html).
Further documentation can be found in the `docstrings` and comments.

## Modules

The _exclusion semantics_ includes the following modules:

- `README.md` to document usage and changes.
- `__init__.py` to expose definitions to be imported elsewhere.
- `examples.py` defines a number of examples to test.
- `semantic.py` defines the default semantics for the operators included.
- `operators.py` defines the primitive and derived operators.

These  will be discussed below, beginning with `examples.py` in the following section.

## Usage

The following subsections will describe each of the elements involved in basic usage.

## Testing

Run `pytest` from the project directory to quickly evaluate whether the examples included in `examples.py` return the expected result.

### Examples

Run `model-checker examples.py` from within the project directory to test the examples included the `example_range` defined in `examples.py`.
Here are two such examples:

    # DOUBLE NEGATION ELIMINATION IDENTITY
    EX_CM_1_settings = {
        'N' : 3,
        'possible' : False,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'fusion_closure' : False,
        'max_time' : 1,
    }
    EX_CM_1_example = [
        [], # premises
        ['(A \\uniequiv \\exclude \\exclude A)'], # conclusions
        EX_CM_1_settings,
    ]

    # DISJUNCTIVE SYLLOGISM
    EX_TH_1_settings = {
        'N' : 3,
        'possible' : False,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'fusion_closure' : False,
        'max_time' : 1,
    }
    EX_TH_1_example = [
        ['(A \\univee B)', '\\exclude B'], # premises
        ['A'], # conclusions
        EX_TH_1_settings
    ]

Each example defines the settings followed be a list of premises (treated conjunctively) and list of conclusions (treated disjunctively).
These examples may then be included in the following:

    example_range = {
        # Countermodels
        "EX_CM_1" : EX_CM_1_example,
        # Theorems
        # "EX_TH_1" : EX_TH_1_example,
    }

Whereas `EX_CM_1` will be considered, `EX_TH_1` is excluded from consideration on account of including the hash mark '#' at the beginning of the line.
By removing the hash mark from `EX_TH_1`, both examples will be tested in turn.

### Settings

In addition to the settings included in each example, there are also general settings which control the output:

    general_settings = {
        "print_constraints": False,
        "print_impossible": False,
        "print_z3": False,
        "save_output": False,
    }

The default example settings are also included for reference, though may be omitted if no example includes those settings (e.g., by replacing `EX_TH_1_settings` with `example_settings`):

    example_settings = {
        'N' : 3,
        'possible' : False,
        'contingent' : False,
        'disjoint' : False,
        'non_empty' : False,
        'non_null' : False,
        'fusion_closure' : False,
        'max_time' : 1,
    }

If settings are omitted from an example (e.g., no value of `N` is provided), the defaults above will be assumed, issuing a notification the user.

### Semantic Theories

The semantic theories over which the examples included in `example_range` are composed of a `semantics`, definition of a `proposition`, and collection of `operators` included in the examples under consideration.
In particular, the `exclusion_theory` is defined as follows:

    exclusion_operators = syntactic.OperatorCollection(
        UniAndOperator, UniOrOperator, ExclusionOperator, # extensional
        UniIdentityOperator, # constitutive
    )

    exclusion_theory = {
        "semantics": ExclusionSemantics,
        "proposition": UnilateralProposition,
        "operators": exclusion_operators,
    }

The `ExclusionSemantics` and `UnilateralProposition` are imported from the `semantic.py` module and the operators included in `exclusion_operators` are imported from `exclusion_operators`.
These modules will be discussed in the [Basic Architecture](#basic-architecture) section below.

Given the `exclusion_theory` defined above, we may evaluate examples over this semantic theory as follows:

    semantic_theories = {
        "ChampollionBernard" : exclusion_theory,
    }

Multiple semantic theories may be provided for systematic comparison.
For instance, we may import elements of the default theory provided by the model-checker:

    default_operators = syntactic.OperatorCollection(
        NegationOperator, AndOperator, OrOperator, # extensional
        IdentityOperator, # constitutive
    )

    default_theory = {
        "semantics": Semantics,
        "proposition": Proposition,
        "operators": default_operators,
        "dictionary": default_dictionary,
    }

    default_dictionary = {
        "\\exclude" : "\\neg",
        "\\uniwedge" : "\\wedge",
        "\\univee" : "\\vee",
        "\\uniequiv" : "\\equiv",
    }

    semantic_theories = {
        "Champollion" : exclusion_theory,
        "Brast-McKie" : default_theory,
    }

The `exclusion_theory` did not include a `dictionary` since the examples to be tested are articulated in terms of the `exclusion_operators` (e.g., `\\exclude`, `\\uniwedge`, etc.).
By contrast, the `default_theory` must provide a translation dictionary in order to specify the corresponding operators (e.g., `\\neg`, `\\wedge`, etc.).
If the examples stated in terms of the operators included in the `default_theory` instead, then the `exclusion_theory` would have to include a dictionary (i.e., the inverse of the `default_dictionary` provided above).

Further semantic theories may be included for comparison by following the pattern provided by the `default_theory` above.
Upon testing, each example will be evaluated over each semantic theory included in `semantic_theories` before moving on to the next example.

## Basic Architecture

The `semantics.py` module consists of two classes which define the models of the language and the theory of propositions over which the language is interpreted.

> TO BE CONTINUED...

### Semantics

### Propositions

### Operators
