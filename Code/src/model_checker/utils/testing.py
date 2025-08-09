"""
Testing utility functions for the model checker.

This module provides functions for running model checking tests with various
configurations and collecting detailed results.
"""

import time


def run_test(
    example_case,
    semantic_class,
    proposition_class,
    operator_collection,
    syntax_class,
    model_constraints,
    model_structure,
):
    """Run a model checking test with the given components.
    
    This function creates a complete model checking pipeline by instantiating
    the syntax, semantics, model constraints, and model structure with the
    provided components. It then checks if the resulting model matches the
    expected behavior defined in the example settings.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        semantic_class: The semantic theory class to use
        proposition_class: The proposition class to use
        operator_collection (OperatorCollection): Collection of operators
        syntax_class: The syntax class to use (normally Syntax)
        model_constraints: The model constraints class to use
        model_structure: The model structure class to use
        
    Returns:
        bool: True if the model matches the expected behavior, False otherwise
    """
    premises, conclusions, settings = example_case
    example_syntax = syntax_class(premises, conclusions, operator_collection)
    semantics = semantic_class(settings)
    # Create model constraints
    model_constraints = model_constraints(
        settings,
        example_syntax,
        semantics,
        proposition_class,
    )
    # Create model structure
    model_structure = model_structure(
        model_constraints, 
        settings,
    )
    return model_structure.check_result()


class TestResultData:
    """Data class to hold detailed test analysis results."""
    
    def __init__(self):
        self.model_found = False
        self.check_result = False
        self.premise_evaluations = []
        self.conclusion_evaluations = []
        self.solving_time = 0.0
        self.z3_model_status = None
        self.function_witnesses = {}
        self.error_message = None
        self.strategy_name = None
        
    def is_valid_countermodel(self):
        """Check if this represents a valid countermodel (true premises, false conclusions)."""
        if not self.model_found:
            return False
        
        # All premises must be true
        premises_valid = all(self.premise_evaluations)
        # All conclusions must be false  
        conclusions_valid = all(not c for c in self.conclusion_evaluations)
        
        return premises_valid and conclusions_valid


def run_enhanced_test(
    example_case,
    semantic_class,
    proposition_class,
    operator_collection,
    syntax_class,
    model_constraints,
    model_structure,
    strategy_name="default"
):
    """Run a model checking test with enhanced data collection.
    
    This function extends run_test to capture detailed evaluation data
    for analysis and comparison across different strategies.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        semantic_class: The semantic theory class to use
        proposition_class: The proposition class to use
        operator_collection (OperatorCollection): Collection of operators
        syntax_class: The syntax class to use (normally Syntax)
        model_constraints: The model constraints class to use
        model_structure: The model structure class to use
        strategy_name (str): Name of the strategy being tested
        
    Returns:
        TestResultData: Detailed test results and analysis
    """
    result_data = TestResultData()
    result_data.strategy_name = strategy_name
    
    try:
        start_time = time.time()
        
        premises, conclusions, settings = example_case
        example_syntax = syntax_class(premises, conclusions, operator_collection)
        semantics = semantic_class(settings)
        
        # Create model constraints
        model_constraints_obj = model_constraints(
            settings,
            example_syntax,
            semantics,
            proposition_class,
        )
        
        # Create model structure
        model_structure_obj = model_structure(
            model_constraints_obj, 
            settings,
        )
        
        result_data.solving_time = time.time() - start_time
        result_data.check_result = model_structure_obj.check_result()
        result_data.z3_model_status = model_structure_obj.z3_model_status
        result_data.model_found = model_structure_obj.z3_model is not None
        
        # Extract detailed evaluation data if model was found
        if result_data.model_found and model_structure_obj.z3_model:
            try:
                # Interpret the sentences to get propositions
                model_structure_obj.interpret(example_syntax.premises)
                model_structure_obj.interpret(example_syntax.conclusions)
                
                # Debug: Check if sentences exist and have propositions
                premise_count = len(example_syntax.premises)
                conclusion_count = len(example_syntax.conclusions)
                
                # Evaluate premises
                for i, premise_sentence in enumerate(example_syntax.premises):
                    if hasattr(premise_sentence, 'proposition') and premise_sentence.proposition:
                        eval_result = premise_sentence.proposition.truth_value_at(
                            model_structure_obj.semantics.main_point
                        )
                        result_data.premise_evaluations.append(eval_result)
                    else:
                        # If no proposition was created, this indicates an interpretation issue
                        result_data.premise_evaluations.append(None)
                
                # Evaluate conclusions
                for i, conclusion_sentence in enumerate(example_syntax.conclusions):
                    if hasattr(conclusion_sentence, 'proposition') and conclusion_sentence.proposition:
                        eval_result = conclusion_sentence.proposition.truth_value_at(
                            model_structure_obj.semantics.main_point
                        )
                        result_data.conclusion_evaluations.append(eval_result)
                    else:
                        # If no proposition was created, this indicates an interpretation issue
                        result_data.conclusion_evaluations.append(None)
                        
            except Exception as interpret_error:
                # If interpretation fails, at least record the structure
                result_data.premise_evaluations = [None] * len(premises)
                result_data.conclusion_evaluations = [None] * len(conclusions)
                if result_data.error_message is None:
                    result_data.error_message = f"Interpretation error: {interpret_error}"
        
        # Even if no model found, record the expected counts for analysis
        if not result_data.model_found:
            # Record expected counts based on example structure
            result_data.premise_evaluations = [None] * len(premises)
            result_data.conclusion_evaluations = [None] * len(conclusions)
            
            # Extract function witnesses if available
            if hasattr(model_structure_obj.semantics, 'extract_function_witness'):
                try:
                    result_data.function_witnesses = model_structure_obj.semantics.extract_function_witness(
                        model_structure_obj.z3_model
                    )
                except Exception as e:
                    result_data.function_witnesses = {"error": str(e)}
        
    except Exception as e:
        result_data.error_message = str(e)
        result_data.solving_time = time.time() - start_time if 'start_time' in locals() else 0.0
    
    return result_data


def run_strategy_test(
    example_case,
    strategy_name,
    semantic_class=None,
    proposition_class=None,
    syntax_class=None,
    model_constraints=None,
    model_structure=None
):
    """Run a model checking test with a specific exclusion strategy.
    
    This is a convenience function that automatically creates the operator collection
    for the specified strategy and runs the enhanced test.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        strategy_name (str): Name of exclusion strategy ("QA", "QI", "QI2", "BQI", "NF", "NA")
        semantic_class: The semantic theory class to use (defaults to ExclusionSemantics)
        proposition_class: The proposition class to use (defaults to UnilateralProposition)
        syntax_class: The syntax class to use (defaults to Syntax)
        model_constraints: The model constraints class to use (defaults to ModelConstraints)
        model_structure: The model structure class to use (defaults to ExclusionStructure)
        
    Returns:
        TestResultData: Detailed test results and analysis
        
    Raises:
        ValueError: If strategy_name is not recognized
    """
    # Import default classes if not provided
    if semantic_class is None:
        from model_checker.theory_lib.exclusion import ExclusionSemantics
        semantic_class = ExclusionSemantics
    
    if proposition_class is None:
        from model_checker.theory_lib.exclusion import UnilateralProposition
        proposition_class = UnilateralProposition
    
    if syntax_class is None:
        from model_checker import Syntax
        syntax_class = Syntax
    
    if model_constraints is None:
        from model_checker import ModelConstraints
        model_constraints = ModelConstraints
    
    if model_structure is None:
        from model_checker.theory_lib.exclusion import ExclusionStructure
        model_structure = ExclusionStructure
    
    # Create operator collection for the specified strategy
    from model_checker.theory_lib.exclusion.operators import create_operator_collection
    operator_collection = create_operator_collection(strategy_name)
    
    # Run the enhanced test with the strategy-specific operator collection
    return run_enhanced_test(
        example_case=example_case,
        semantic_class=semantic_class,
        proposition_class=proposition_class,
        operator_collection=operator_collection,
        syntax_class=syntax_class,
        model_constraints=model_constraints,
        model_structure=model_structure,
        strategy_name=strategy_name
    )