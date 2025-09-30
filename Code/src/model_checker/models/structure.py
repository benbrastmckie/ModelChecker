"""Core model structure and Z3 solving.

This module contains the ModelDefaults class which provides the core
model structure and Z3 solving functionality.
"""

import sys
import time
from contextlib import redirect_stdout
from string import Template
from typing import Dict, List, Tuple, Optional, Any, TextIO, Union, TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker.syntactic import Sentence
    from .constraints import ModelConstraints
    import z3


class ModelDefaults:
    """Base class for model structures that handle Z3 solving and result interpretation.
    
    This class provides the core functionality for constraint solving and model generation.
    It interfaces with the Z3 solver to find models that satisfy the logical constraints
    derived from premises and conclusions, and provides methods for interpreting and
    displaying the results.
    
    Specific theories extend this class to implement theory-specific model structures
    with additional functionality and visualization capabilities.
    
    The class implements careful isolation between examples to ensure that each example
    is solved independently with its own Z3 solver instance. This prevents state leakage
    between examples that could affect solver behavior, performance, or results.
    
    Attributes:
        model_constraints (ModelConstraints): The constraints to satisfy in the model
        settings (dict): Configuration settings for model generation
        semantics (Semantics): The semantic theory in use
        result (tuple): Contains solver results after solving
        solved (bool): Whether the model has been successfully solved
        timeout (bool): Whether solving timed out
        satisfiable (bool): Whether the constraints are satisfiable
        z3_model (Z3 model): The Z3 model object (if satisfiable)
        solver (Z3 Solver): The Z3 solver instance
        main_point (dict): The primary evaluation point for the model
    """

    def __init__(self, model_constraints: 'ModelConstraints', settings: Dict[str, Any]) -> None:
        # Define ANSI color codes
        self.COLORS = {
            "default": "\033[37m",  # WHITE
            "world": "\033[34m",    # BLUE
            "possible": "\033[36m", # CYAN
            "impossible": "\033[35m", # MAGENTA
            "initial": "\033[33m",  # YELLOW
        }
        self.RESET = "\033[0m"
        self.WHITE = self.COLORS["default"]

        # Dictionary for tracking constraints for unsat_core
        self.constraint_dict = {}

        # Store arguments
        self.model_constraints = model_constraints
        self.settings = settings
        # Use defensive defaults for required settings
        self.max_time = self.settings.get("max_time", 5)  # Default 5 seconds timeout
        self.expectation = self.settings.get("expectation", True)  # Default expect validity

        # Store from model_constraints.semantics
        self.semantics = self.model_constraints.semantics
        self.main_point = self.semantics.main_point
        self.all_states = self.semantics.all_states
        self.N = self.semantics.N

        # Store from model_constraint.syntax
        self.syntax = self.model_constraints.syntax
        self.start_time = self.syntax.start_time
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions
        self.sentence_letters = self.syntax.sentence_letters

        # Store from model_constraint
        self.proposition_class = self.model_constraints.proposition_class

        # Initialize Z3 attributes - CRITICAL for iterator compatibility
        self.solver = None
        self.stored_solver = None
        self.timeout = False
        self.z3_model = None
        self.unsat_core = None
        self.z3_model_status = None
        self.z3_model_runtime = None
        self.solved = False
        self.satisfiable = None
        self.result = None
        
        # Reset Z3 context before creating a new solver to ensure isolation
        from model_checker.utils import Z3ContextManager
        from ..utils.context import reset_z3_context
        reset_z3_context()

        # Solve Z3 constraints and store results
        solver_results = self.solve(self.model_constraints, self.max_time)
        self._process_solver_results(solver_results)

        # Exit early if no valid model was found
        if self.timeout or self.z3_model is None:
            return

    def _process_solver_results(self, solver_results: Tuple[bool, Any, bool, float]) -> None:
        """Process and store the results from the Z3 solver.
        
        Takes the raw solver results and updates the model's state attributes including
        timeout status, model/unsat core, model status, and runtime.
        
        Args:
            solver_results (tuple): Contains:
                - timeout (bool): Whether solver timed out
                - z3_model (Z3Model/list): Either a satisfying model or unsat core
                - z3_model_status (bool): Whether constraints were satisfiable
                - z3_model_runtime (float): Time taken by solver in seconds
        """
        timeout, z3_model, z3_model_status, z3_model_runtime = solver_results
        
        self.timeout = timeout
        self.z3_model_status = z3_model_status
        self.z3_model_runtime = z3_model_runtime
        self.satisfiable = z3_model_status
        self.solved = True
        self.result = solver_results
        
        # Store either the model or unsat core based on status
        if z3_model_status:
            self.z3_model = z3_model
        else:
            self.unsat_core = z3_model

    def _setup_solver(self, model_constraints: 'ModelConstraints') -> 'z3.Solver':
        """Initialize Z3 solver and add all model constraints with tracking labels.
        
        Sets up a new Z3 solver instance and adds all constraints from the model_constraints
        object, organizing them into labeled groups (frame, model, premises, conclusions).
        Each constraint is tracked with a unique identifier for unsat core extraction.
        
        Args:
            model_constraints (ModelConstraints): Object containing all logical constraints
                                                to be added to the solver
                                                
        Returns:
            z3.Solver: Initialized solver with all constraints added and tracked
            
        Note:
            Constraints are added using assert_and_track() to enable unsat core generation
            when constraints are unsatisfiable.
        """
        from z3 import Solver
        solver = Solver()
            
        # Clear the constraint dict to prevent cross-example contamination
        self.constraint_dict = {}
            
        constraint_groups = [
            (model_constraints.frame_constraints, "frame"),
            (model_constraints.model_constraints, "model"), 
            (model_constraints.premise_constraints, "premises"),
            (model_constraints.conclusion_constraints, "conclusions")
        ]
        
        for constraints, group_name in constraint_groups:
            for ix, constraint in enumerate(constraints):
                c_id = f"{group_name}{ix+1}"
                solver.assert_and_track(constraint, c_id)
                self.constraint_dict[c_id] = constraint
                
        return solver

    def _create_result(self, is_timeout: bool, model_or_core: Any, is_satisfiable: bool, start_time: float) -> Tuple[bool, Any, bool, float]:
        """Creates a standardized tuple containing solver results with runtime.
        
        Args:
            is_timeout (bool): Whether the solver timed out
            model_or_core (Z3Model/list): Either a satisfying model or unsat core
            is_satisfiable (bool): Whether the constraints were satisfiable
            start_time (float): When solving started (used to calculate runtime)
            
        Returns:
            tuple: Contains (is_timeout, model_or_core, is_satisfiable, runtime)
            where runtime is rounded to 4 decimal places
        """
        runtime = round(time.time() - start_time, 4)
        return is_timeout, model_or_core, is_satisfiable, runtime

    def _cleanup_solver_resources(self) -> None:
        """Explicitly clean up Z3 resources to ensure complete isolation between examples.
        
        This method is crucial for preventing state leakage between different examples.
        It explicitly removes references to Z3 objects to ensure that Z3 resources 
        are properly released. This helps prevent unexpected interactions between 
        examples that could affect solving behavior or performance.
        
        IMPORTANT: This is a core part of the solver state isolation system. It should be
        called in the finally block of solve() and related methods to ensure resources
        are always released, even if exceptions occur.
        """
        # Remove references to solver and model
        self.solver = None
        self.z3_model = None
        
        # Clear the context reference (if it exists)
        if hasattr(self, 'example_context'):
            self.example_context = None
    
    def solve(self, model_constraints: 'ModelConstraints', max_time: int) -> Tuple[bool, Any, bool, Optional[float]]:
        """Uses the Z3 solver to find a model satisfying the given constraints.
        
        Creates a completely fresh Z3 context for each example to ensure
        proper isolation and deterministic behavior regardless of which
        examples were run previously.
        
        Args:
            model_constraints (ModelConstraints): The logical constraints to solve
            max_time (int): Maximum solving time in milliseconds (0 for unlimited)
            
        Returns:
            tuple: Contains result information (timeout flag, model/core, satisfiability)
            
        Notes:
            - If the constraints are unsatisfiable, returns the unsatisfiable core
            - If solving times out, sets the timeout flag but still returns partial results
        """
        # Import z3
        import z3
        
        # Create a new solver
        self.solver = z3.Solver()
        self.stored_solver = self.solver

        try:
            # Set up the solver with the constraints
            self.solver = self._setup_solver(model_constraints)

            # Set timeout and solve
            self.solver.set("timeout", int(max_time * 1000))
            start_time = time.time()
            result = self.solver.check()
            
            # Handle different solver outcomes
            if result == z3.sat:
                return self._create_result(False, self.solver.model(), True, start_time)
            
            if self.solver.reason_unknown() == "timeout":
                return self._create_result(True, None, False, start_time)
            
            return self._create_result(False, self.solver.unsat_core(), False, start_time)
            
        except RuntimeError as e:
            from .errors import ModelSolverError
            raise ModelSolverError(f"Z3 solver encountered an error: {e}") from e
        finally:
            # Ensure proper cleanup to prevent any possible state leakage
            self._cleanup_solver_resources()
    
    def re_solve(self) -> Tuple[bool, Any, bool, float]:
        """Re-solve the existing model constraints with the current solver state.
        
        Attempts to find a new solution using the existing solver instance and its
        constraints. This is useful when additional constraints have been added to
        the solver after initial solving.
        
        Returns:
            tuple: Contains (is_timeout, model_or_core, is_satisfiable, runtime) where:
                - is_timeout (bool): Whether solver timed out
                - model_or_core: Either a Z3 model (if satisfiable) or unsat core (if unsatisfiable)
                - is_satisfiable (bool): Whether constraints were satisfiable
                - runtime (float): Time taken by solver in seconds
        """
        import z3

        try:
            assert self.solver is not None
            # Re-apply timeout setting
            self.solver.set("timeout", int(self.max_time * 1000))
            
            start_time = time.time()
            result = self.solver.check()
            
            # Handle different solver outcomes
            if result == z3.sat:
                return self._create_result(False, self.solver.model(), True, start_time)
            
            if self.solver.reason_unknown() == "timeout":
                return self._create_result(True, None, False, start_time)
            
            return self._create_result(False, self.solver.unsat_core(), False, start_time)
            
        except RuntimeError as e:
            from .errors import ModelSolverError
            raise ModelSolverError(f"Re-solve operation failed: {e}") from e

    def check_result(self) -> Optional[bool]:
        """Checks if the model's result matches the expected outcome.
        
        Compares the actual model status (satisfiable/unsatisfiable) against the
        expected outcome specified in the settings. This is used to verify if
        the model checker produced the anticipated result.
        
        Returns:
            bool or None: True if the model status matches expectations, 
                         False otherwise, None if not solved yet
        """
        if not self.solved:
            return None
        return self.z3_model_status == self.settings["expectation"]

    def interpret(self, sentences: List['Sentence']) -> None:
        """Recursively updates sentences with their semantic interpretations in the model.
        
        For each sentence in the input list, creates and attaches a proposition object
        that represents its semantic interpretation in the current model. This process
        recursively handles complex sentences by first interpreting their subformulas.
        
        Args:
            sentences (list): List of Sentence objects to be interpreted
            
        Note:
            - This method should only be called after a valid Z3 model has been found
            - Modifies the sentence objects in-place by calling their update_objects method
            - Skips processing if no valid model exists
        """
        if not self.z3_model:
            return

        for sent_obj in sentences:
            if sent_obj.arguments:
                self.interpret(sent_obj.arguments)
            sent_obj.update_proposition(self)

    def print_grouped_constraints(self, output: TextIO = sys.__stdout__) -> None:
        """Prints all model constraints organized by their logical category.
        
        Displays constraints grouped into four categories:
        1. Frame constraints (defining the logical frame)
        2. Model constraints (atomic propositions and relations)
        3. Premise constraints (from input premises)
        4. Conclusion constraints (from input conclusions)
        
        For each category, prints:
        - Total count of constraints
        - Numbered list of constraints with their Z3 representations
        
        If model is satisfiable, shows all constraints.
        If model is unsatisfiable, shows only the constraints in the unsat core.
        
        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        # Get constraints based on model status
        constraints = self._get_relevant_constraints(output)
        
        # Print summary counts
        self._print_constraint_summary(constraints, output)
        
        # Organize and print constraint groups
        groups = self._organize_constraint_groups(constraints)
        self._print_constraint_groups(groups, output)
    
    def _get_relevant_constraints(self, output: TextIO) -> List[Any]:
        """Get the relevant constraints based on model satisfiability status.
        
        Returns:
            list: Constraints to display (all constraints if SAT, unsat core if UNSAT)
        """
        if self.z3_model:
            print("SATISFIABLE CONSTRAINTS:", file=output)
            return self.model_constraints.all_constraints
        elif self.unsat_core is not None:
            print("UNSATISFIABLE CORE CONSTRAINTS:", file=output)
            return [self.constraint_dict[str(c)] for c in self.unsat_core]
        else:
            print("NO CONSTRAINTS AVAILABLE", file=output)
            return []
    
    def _print_constraint_summary(self, constraints: List[Any], output: TextIO) -> None:
        """Print summary counts for each constraint category.
        
        Args:
            constraints: List of constraints to summarize
            output: Output stream to write to
        """
        frame_count = sum(1 for c in constraints if c in self.model_constraints.frame_constraints)
        model_count = sum(1 for c in constraints if c in self.model_constraints.model_constraints) 
        premise_count = sum(1 for c in constraints if c in self.model_constraints.premise_constraints)
        conclusion_count = sum(1 for c in constraints if c in self.model_constraints.conclusion_constraints)
        
        print(f"- Frame constraints: {frame_count}", file=output)
        print(f"- Model constraints: {model_count}", file=output)
        print(f"- Premise constraints: {premise_count}", file=output)
        print(f"- Conclusion constraints: {conclusion_count}\n", file=output)
    
    def _organize_constraint_groups(self, constraints: List[Any]) -> Dict[str, List[Any]]:
        """Organize constraints into logical groups.
        
        Args:
            constraints: List of constraints to organize
            
        Returns:
            dict: Constraints organized by group (FRAME, MODEL, PREMISES, CONCLUSIONS)
        """
        groups = {
            "FRAME": [],
            "MODEL": [],
            "PREMISES": [],
            "CONCLUSIONS": []
        }
        
        for constraint in constraints:
            if constraint in self.model_constraints.frame_constraints:
                groups["FRAME"].append(constraint)
            elif constraint in self.model_constraints.model_constraints:
                groups["MODEL"].append(constraint)
            elif constraint in self.model_constraints.premise_constraints:
                groups["PREMISES"].append(constraint)
            elif constraint in self.model_constraints.conclusion_constraints:
                groups["CONCLUSIONS"].append(constraint)
        
        return groups
    
    def _print_constraint_groups(self, groups: Dict[str, List[Any]], output: TextIO) -> None:
        """Print each group of constraints with headers and numbering.
        
        Args:
            groups: Dictionary of constraint groups
            output: Output stream to write to
        """
        for group_name, group_constraints in groups.items():
            if group_constraints:  # Only print groups that have constraints
                print(f"{group_name} CONSTRAINTS:", file=output)
                for index, con in enumerate(group_constraints, start=1):
                    print(f"{index}. {con}\n", file=output)

    def print_constraints(self, constraints: List[Any], name: str, output: TextIO = sys.__stdout__) -> None:
        """Prints a numbered list of constraints with appropriate header.
        
        Args:
            constraints (list): List of Z3 constraints to print
            name (str): Name/category of constraints for the header
            output (file, optional): Output stream to write to. Defaults to sys.stdout
            
        Example output:
            Satisfiable frame constraints:
            1. x ∧ y
            2. y → z
            
            or
            
            Unsatisfiable core constraints:
            1. x ∧ ¬x
        """
        if self.z3_model_status:
            print(f"Satisfiable {name} constraints:\n", file=output)
        else:
            print("Unsatisfiable core constraints:\n", file=output)
        for index, con in enumerate(constraints, start=1):
            print(f"{index}. {con}\n", file=output)

    def build_test_file(self, output: TextIO) -> None:
        """Generates a test file from the current model configuration and results.
        
        Creates a Python test file containing the model settings, premises, conclusions,
        and runtime information. The generated file can be used to reproduce the model
        checking results or serve as a regression test.
        
        Args:
            output (file): File-like object to write the test content to
            
        Note:
            Uses the inputs_template to format the test file content with:
            - Model settings
            - Premise sentences
            - Conclusion sentences
            - Z3 solver runtime
        """
        from string import Template

        inputs_template = Template(
        '''Z3 run time: ${z3_model_runtime} seconds
        """

        ################
        ### SETTINGS ###
        ################

        settings = ${settings}


        ###############
        ### EXAMPLE ###
        ###############

        # input sentences
        premises = ${premises}
        conclusions = ${conclusions}


        #########################################
        ### GENERATE Z3 CONSTRAINTS AND PRINT ###
        #########################################

        ### NOTE: run below for individual tests

        model_structure = make_model_for(
            settings,
            premises,
            conclusions,
            Semantics,
            Proposition,
            operators,
        )
        model_structure.print_all()
        '''
        )

        inputs_data = {
            "settings": self.model_constraints.settings,
            "premises": self.premises,
            "conclusions": self.conclusions,
            "z3_model_runtime": self.z3_model_runtime,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)

    def recursive_print(self, sentence: 'Sentence', eval_point: Dict[str, Any], indent_num: int, use_colors: bool) -> None:
        """Recursively prints a sentence and its subformulas with their truth values.

        This method handles both atomic and complex sentences, printing them with
        appropriate indentation and optional color coding. For atomic sentences,
        it directly prints the proposition. For complex sentences, it delegates to
        the operator's print method to handle the recursive printing of subformulas.

        Args:
            sentence (Sentence): The sentence object to print
            eval_point (dict): The evaluation point in the model
            indent_num (int): Current indentation level (1-based)
            use_colors (bool): Whether to use ANSI color codes in output

        Note:
            - Indentation is adjusted for second-level formulas for readability
            - Colors are used to indicate truth values when use_colors is True
            - Atomic sentences are printed directly via their proposition
            - Complex sentences delegate to their operator's print_method
        """
        if indent_num == 2:  # NOTE: otherwise second lines don't indent
            indent_num += 1
        if sentence.sentence_letter is not None:  # Print sentence letter
            sentence.proposition.print_proposition(eval_point, indent_num, use_colors)
            return
        operator = sentence.original_operator
        operator.print_method(sentence, eval_point, indent_num, use_colors)  # Print complex sentence

    def print_input_sentences(self, output: TextIO) -> None:
        """Prints the premises and conclusions with their semantic interpretations.
        
        For each premise and conclusion, recursively prints the sentence along with
        its truth value at the main evaluation point. Complex sentences are broken
        down to show the truth values of their subformulas.
        
        Args:
            output (file): The output stream to write to (e.g., sys.stdout)
            
        Note:
            - Requires a valid Z3 model to interpret sentences
            - Uses color coding when printing to sys.stdout
            - Premises are numbered starting from 1
            - Conclusions continue the numbering after premises
        """
        if not self.z3_model:
            print("No valid model available - cannot interpret sentences", file=output)
            return
            
        # Print premises
        start_index = 1
        self._print_sentence_group(
            "INTERPRETED PREMISE:\n",
            "INTERPRETED PREMISES:\n",
            self.premises,
            start_index,
            output
        )
        
        # Print conclusions  
        continue_index = len(self.premises) + 1
        self._print_sentence_group(
            "INTERPRETED CONCLUSION:\n",
            "INTERPRETED CONCLUSIONS:\n",
            self.conclusions,
            continue_index,
            output
        )
    
    def _print_sentence_group(self, title_singular: str, title_plural: str, sentences: List['Sentence'], start_index: int, output: TextIO) -> None:
        """Print a group of sentences with appropriate title and numbering.
        
        Args:
            title_singular: Title to use if there's only one sentence
            title_plural: Title to use if there are multiple sentences
            sentences: List of sentences to print
            start_index: Starting number for the sentences
            output: Output stream to write to
        """
        from contextlib import redirect_stdout
        
        if not sentences:
            return
            
        title = title_singular if len(sentences) < 2 else title_plural
        print(title, file=output)
        
        for index, sentence in enumerate(sentences, start=start_index):
            print(f"{index}.", end="", file=output)
            with redirect_stdout(output):
                use_colors = output is sys.__stdout__
                self.recursive_print(sentence, self.main_point, 1, use_colors)
                print(file=output)

    def print_model(self, output: TextIO) -> None:
        """Prints the raw Z3 model or unsat core if print_z3 setting is enabled.
        
        This method prints either the complete Z3 model (if constraints are satisfiable)
        or the unsatisfiable core (if constraints are unsatisfiable), but only when
        the print_z3 setting is True in the model settings.
        
        Args:
            output (file): The output stream to write to (e.g., sys.stdout)
            
        Note:
            - Only prints if self.settings["print_z3"] is True
            - For satisfiable models, prints the complete Z3 model
            - For unsatisfiable models, prints the unsat core
        """
        if self.settings["print_z3"]:
            if self.z3_model_status:
                print(self.z3_model, file=output)
            else:
                print(self.unsat_core, file=output)
                
    def calculate_model_differences(self, previous_structure: 'ModelDefaults') -> Optional[Dict[str, Any]]:
        """Calculate theory-specific differences between this model and a previous one.
        
        This method identifies semantic differences that are meaningful in this theory's
        context. The default implementation returns None, indicating that the basic
        difference calculation should be used instead.
        
        Each theory should override this method to detect differences in its specific
        semantic primitives, such as worlds, times, accessibility relations, etc.
        
        Args:
            previous_structure: The previous model structure to compare against
            
        Returns:
            dict: Theory-specific differences between the models, or None to use basic detection
        """
        # Default implementation returns None, meaning use basic difference detection
        return None
        
    def print_model_differences(self, output: TextIO = sys.stdout) -> None:
        """Prints differences between this model and the previous one.
        
        Default implementation that provides basic difference display.
        Theory-specific classes should override this to provide more detailed output.
        
        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return
        
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # Print each category of differences
        self._print_sentence_letter_differences(output)
        self._print_semantic_function_differences(output)
        self._print_model_structure_differences(output)
        self._print_structural_metrics(output)
        
        # Note if model is isomorphic
        if hasattr(self, 'isomorphic_to_previous') and self.isomorphic_to_previous:
            print("NOTE: This model may be isomorphic to a previous model despite syntactic differences.", file=output)
    
    def _print_sentence_letter_differences(self, output: TextIO) -> None:
        """Print differences in sentence letter values."""
        letter_diffs = self.model_differences.get('sentence_letters', {})
        if not letter_diffs:
            return
            
        print("Sentence Letter Changes:", file=output)
        for letter, values in letter_diffs.items():
            try:
                if 'old' in values and 'new' in values:
                    print(f"  {letter}: {values['old']} → {values['new']}", file=output)
                else:
                    print(f"  {letter}: changed from previous model", file=output)
            except (KeyError, TypeError):
                print(f"  {letter}: changed from previous model", file=output)
        print("", file=output)
    
    def _print_semantic_function_differences(self, output: TextIO) -> None:
        """Print differences in semantic functions."""
        func_diffs = self.model_differences.get('semantic_functions', {})
        if not func_diffs:
            return
            
        print("Semantic Function Changes:", file=output)
        for func_name, values in func_diffs.items():
            print(f"  {func_name}:", file=output)
            for input_val, change in values.items():
                try:
                    if 'old' in change and 'new' in change:
                        print(f"    Input {input_val}: {change['old']} → {change['new']}", file=output)
                    else:
                        print(f"    Input {input_val}: changed from previous model", file=output)
                except (KeyError, TypeError):
                    print(f"    Input {input_val}: changed from previous model", file=output)
        print("", file=output)
    
    def _print_model_structure_differences(self, output: TextIO) -> None:
        """Print differences in model structure."""
        struct_diffs = self.model_differences.get('model_structure', {})
        if not struct_diffs:
            return
            
        print("Model Structure Changes:", file=output)
        for component, values in struct_diffs.items():
            try:
                if 'old' in values and 'new' in values:
                    print(f"  {component}: {values['old']} → {values['new']}", file=output)
                else:
                    print(f"  {component}: changed from previous model", file=output)
            except (KeyError, TypeError):
                print(f"  {component}: changed from previous model", file=output)
        print("", file=output)
    
    def _print_structural_metrics(self, output: TextIO) -> None:
        """Print structural properties of the model."""
        print("Structural Properties:", file=output)
        print(f"  Worlds: {len(getattr(self, 'z3_world_states', []))}", file=output)

    def print_info(self, model_status: bool, default_settings: Dict[str, Any], example_name: str, theory_name: str, output: TextIO) -> None:
        """Print comprehensive model information and analysis results.
        
        Displays a formatted output containing the model checking results, including
        example metadata, configuration settings, and performance metrics. The output
        is organized into sections showing:
        
        1. Example name and countermodel status
        2. Model configuration (atomic states, semantic theory)
        3. Non-default settings that were modified
        4. Premises and conclusions
        5. Z3 solver runtime statistics
        
        Args:
            model_status (bool): True if a countermodel was found, False otherwise
            default_settings (dict): Base configuration settings for comparison
            example_name (str): Identifier for the logical example being analyzed
            theory_name (str): Name of the semantic theory implementation used
            output (file): File-like object for writing the output
            
        Note:
            Output is formatted with section headers and separators for readability
        """
        
        # Determine result header
        header = "there is a countermodel." if model_status else "there is no countermodel."
        
        # Print example information
        self._print_section_header(example_name, header, output)
        self._print_model_details(theory_name, output)
        
        # Print constraints and runtime
        self.model_constraints.print_enumerate(output)
        self._print_runtime_footer(output)

    def _print_section_header(self, example_name: str, header: str, output: TextIO) -> None:
        """Print the section header with example name and result."""
        print(f"{'='*40}", file=output)
        print(f"\nEXAMPLE {example_name}: {header}\n", file=output)

    def _print_model_details(self, theory_name: str, output: TextIO) -> None:
        """Print model details including atomic states and semantic theory."""
        print(f"Atomic States: {self.N}\n", file=output)
        print(f"Semantic Theory: {theory_name}\n", file=output)

    def _print_modified_settings(self, default_settings: Dict[str, Any], output: TextIO) -> None:
        """Print settings that have been modified from their default values.
        
        Compares the current settings against the default configuration and prints
        only those settings whose values have been changed. This helps identify
        which configuration parameters were customized for this model instance.
        
        Args:
            default_settings (dict): The baseline configuration settings
            output (file): File-like object to write the output to
            
        Note:
            Settings are printed in 'key = value' format with indentation
            Only modified settings are included in the output
        """
        modified_settings = {
            key: self.settings[key]
            for key, default_value in default_settings.items() 
            if default_value != self.settings[key]
        }
        
        if modified_settings:
            print("Non-Default Settings:", file=output)
            for key, value in modified_settings.items():
                print(f"  {key} = {value}", file=output)
            print()

    def _print_runtime_footer(self, output: TextIO) -> None:
        """Print Z3 runtime and separator footer."""
        print(f"\nZ3 Run Time: {self.z3_model_runtime} seconds", file=output)
        print(f"\n{'='*40}", file=output)
    
    def print_all(self, output: TextIO = sys.stdout) -> None:
        """Print complete model information.
        
        This method provides comprehensive output of the model checking results,
        including interpreted sentences and grouped constraints. It's the primary
        method for displaying full model details to users.
        
        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        # Print interpreted sentences (premises and conclusions)
        self.print_input_sentences(output)
        
        # Add separator between sentences and constraints
        print(file=output)
        
        # Print grouped constraints
        self.print_grouped_constraints(output)
        
        # Print raw Z3 model if requested
        self.print_model(output)
    
    def extract_verify_falsify_state(self) -> Dict[Tuple[int, str], Tuple[bool, bool]]:
        """Extract current verify/falsify function values from Z3 model.
        
        This method extracts the current values of verify and falsify functions
        from the Z3 model. These values are used by the iterator to create
        fresh ModelConstraints that match the current model.
        
        Returns:
            dict: Mapping of (state, letter) -> (verify_value, falsify_value)
            
        Raises:
            ModelStateError: If Z3 model not available
        """
        if not self.z3_model:
            from .errors import ModelStateError
            raise ModelStateError(
                "Cannot extract verify/falsify state: No Z3 model available. "
                "Ensure the model has been solved and is satisfiable before extraction."
            )
        
        import z3
        
        state_map = {}
        for letter in self.sentence_letters:
            letter_str = letter.sentence_letter
            for state in range(2**self.N):
                # Get verify/falsify values from Z3 model
                verify_val = self.z3_model.eval(
                    self.semantics.verify(state, letter_str),
                    model_completion=True
                )
                falsify_val = self.z3_model.eval(
                    self.semantics.falsify(state, letter_str),
                    model_completion=True
                )
                
                # Convert to boolean values
                state_map[(state, letter_str)] = (
                    z3.is_true(verify_val),
                    z3.is_true(falsify_val)
                )
        
        return state_map