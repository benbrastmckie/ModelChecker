"""
Syntax processing for logical formulas.

This module provides the Syntax class which processes logical formulas and
builds a structured representation of logical arguments.
"""

import time
import inspect

from model_checker.utils import flatten

from .sentence import Sentence


class Syntax:
    """Processes logical formulas and builds a structured representation of an argument.
    
    This class takes premises and conclusions in infix notation along with an operator
    collection, and constructs a comprehensive representation of the logical argument.
    It handles parsing sentences, organizing them hierarchically, and preparing them
    for semantic evaluation.
    
    The class performs several key functions:
    1. Parses infix sentences into structured objects
    2. Creates a dictionary of all sentences and subsentences
    3. Links operators in sentences to their operator classes
    4. Extracts all atomic sentence letters used in the argument
    5. Validates that defined operators don't have circular dependencies
    
    Attributes:
        infix_premises (list): Original premise sentences in infix notation
        infix_conclusions (list): Original conclusion sentences in infix notation
        operator_collection (OperatorCollection): Available logical operators
        all_sentences (dict): Maps sentence strings to their Sentence objects
        sentence_letters (list): All atomic sentence letters in the argument
        premises (list): Sentence objects for all premises
        conclusions (list): Sentence objects for all conclusions
        start_time (float): When the syntax processing began
    """

    def __init__(
        self,
        infix_premises,
        infix_conclusions,
        operator_collection,
    ):

        # start timer
        self.start_time = time.time()

        # store inputs
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.operator_collection = operator_collection

        # initialize inputs
        self.all_sentences = {} # updated in build_sentence
        # self.operators_used = []
        self.sentence_letters = [] # updated in build_sentence
        self.premises = self.initialize_sentences(self.infix_premises)
        self.conclusions = self.initialize_sentences(self.infix_conclusions)

        # check for interdefined operators
        self.circularity_check(operator_collection)

    def initialize_sentences(self, infix_sentences):
        """Processes a list of sentences and builds a comprehensive dictionary of all sentences and their subsentences.
        
        This method takes a list of infix sentences and:
        1. Converts each sentence into a Sentence object
        2. Recursively processes all subsentences
        3. Stores all sentences and subsentences in self.all_sentences
        4. Updates sentence types using the operator collection
        5. Identifies and stores atomic sentence letters
        
        Args:
            infix_sentences (list): A list of strings representing logical formulas in infix notation
            
        Returns:
            list: A list of Sentence objects corresponding to the input sentences
            
        Side Effects:
            - Updates self.all_sentences with all sentences and subsentences
            - Updates self.sentence_letters with atomic sentence letters found
        """

        def build_sentence(infix_sentence):
            if infix_sentence in self.all_sentences.keys():
                return self.all_sentences[infix_sentence]
            sentence = Sentence(infix_sentence)
            self.all_sentences[sentence.name] = sentence
            if sentence.original_arguments is None:
                if sentence.name.isalnum():
                    self.sentence_letters.append(sentence)
                return sentence
            sentence_arguments = []
            for infix_arg in sentence.original_arguments:
                sentence_arg = build_sentence(infix_arg)
                sentence_arguments.append(sentence_arg)
            sentence.original_arguments = sentence_arguments
            return sentence

        def initialize_types(sentence):
            """Initializes sentence types using the operator collection.
            
            This method performs two key functions:
            1. Replaces operator strings with their corresponding operator classes from
               the operator collection
            2. Updates the sentence's type information (original_type, arguments)
            
            For non-primitive operators (defined operators), this also processes their
            derived arguments according to their definitions.
            
            Args:
                sentence (Sentence): The sentence object to initialize
                
            Side Effects:
                - Updates sentence.original_type with operator classes
                - Updates sentence.arguments for defined operators
            """
            sentence.update_types(self.operator_collection)
            if sentence.arguments: # NOTE: must happen after arguments are stored
                sentence_arguments = []
                for infix_arg in sentence.arguments:
                    argument = build_sentence(infix_arg)
                    initialize_types(argument)
                    sentence_arguments.append(argument)
                sentence.arguments = sentence_arguments 

        sentence_objects = []
        for infix_sent in infix_sentences:
            sentence = build_sentence(infix_sent)
            initialize_types(sentence)
            sentence_objects.append(sentence)
        return sentence_objects

    def circularity_check(self, operator_collection):
        """Validates operator dependencies and detects circular definitions.
        
        This method performs two key validation checks on the operator collection:
        1. Ensures all operator dependencies are defined within the collection
        2. Detects any circular dependencies between defined operators
        
        For example, if operator A is defined in terms of B, and B is defined in
        terms of A, this would be detected as a circular dependency. Similarly,
        if an operator references an undefined operator C, this would raise an error.
        
        Args:
            operator_collection (OperatorCollection): The collection of operators to validate
            
        Raises:
            ValueError: If an operator depends on undefined operators
            RecursionError: If circular dependencies are detected between operators
            
        Example:
            If operator Implies is defined as (¬p ∨ q) but ¬ is not in the collection,
            this would raise a ValueError. If Implies is defined using Or and Or is
            defined using Implies, this would raise a RecursionError.
        """
        dependency_graph = {}
        operator_set = set(operator_collection.operator_dictionary.values())

        # Build the dependency graph
        for operator_class in operator_collection.operator_dictionary.values():
            if operator_class.primitive:
                continue
            # Ensure derived_definition is callable
            if isinstance(operator_class, type) and callable(getattr(operator_class, 'derived_definition', None)):
                sig = inspect.signature(operator_class.derived_definition)
                num_params = len(sig.parameters)
                dummy_args = [None] * num_params
                dependencies = {
                    elem for elem in flatten(operator_class.derived_definition(*dummy_args))
                    if isinstance(elem, type)
                }
                # Identify missing dependencies if any
                missing_dependencies = dependencies - operator_set
                if missing_dependencies:
                    missing_names = [op.name for op in missing_dependencies]
                    raise ValueError(
                        f"Operator '{operator_class.name}' depends on undefined operators: {missing_names}"
                    )
                # Update the dependency graph
                if operator_class not in dependency_graph:
                    dependency_graph[operator_class] = set()
                dependency_graph[operator_class].update(dependencies)
                continue
            raise ValueError(
                f"Error processing operator '{operator_class.name}'"
            )

        visited = set()
        recursion_stack = []

        def dfs(current):
            if current in recursion_stack:
                cycle = " -> ".join(op.name for op in recursion_stack) + f" -> {current.name}"
                raise RecursionError(
                    f"Circular definition detected in {current.name}.\n\nCYCLE: {cycle}\n"
                )
            if current in visited:
                return
            recursion_stack.append(current)
            for dependent in dependency_graph.get(current, set()):
                dfs(dependent)
            recursion_stack.remove(current)
            visited.add(current)

        # Perform DFS for each operator to detect cycles
        for operator in operator_collection.operator_dictionary.values():
            if not operator.primitive and operator not in visited:
                dfs(operator)