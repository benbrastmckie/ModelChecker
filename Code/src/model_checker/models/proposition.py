"""Proposition management for model checking.

This module contains the PropositionDefaults class which handles
proposition creation, management, and evaluation within models.
"""

from model_checker.utils import not_implemented_string


class PropositionDefaults:
    """Base class for representing propositions in a logical system.
    
    This abstract class provides the foundation for representing propositional content
    in a model. Subclasses must implement the actual semantic behavior specific to each
    logical theory.
    
    Propositions link sentences to their semantic interpretation in a model. They
    contain the necessary methods for calculating truth values and managing verification
    and falsification conditions.
    
    Attributes:
        sentence (Sentence): The sentence object this proposition represents
        model_structure (ModelStructure): The model in which this proposition is interpreted
        N (int): Bit-width for state representation
        main_point (dict): The primary evaluation point for the model
        name (str): The string representation of the sentence
        operator (Operator): The main logical operator of the sentence (None for atoms)
        arguments (list): Sentence objects for the operator's arguments (None for atoms)
        sentence_letter (ExprRef): For atomic sentences, their Z3 representation (None for complex sentences)
        model_constraints (ModelConstraints): Constraints governing the model
        semantics (Semantics): The semantics object used for evaluation
        sentence_letters (list): All atomic sentence letters in the argument
        settings (dict): Model settings
    """

    def __init__(self, sentence, model_structure):

        # Raise error if instantiated directly instead of as a bare class
        if self.__class__ == PropositionDefaults:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))

        # Validate model_structure
        if not hasattr(model_structure, 'semantics'):
            raise TypeError(
                f"Expected model_structure to be a ModelStructure object, got {type(model_structure)}. "
                "Make sure you're passing the correct model_structure object when creating propositions."
            )

        # Store inputs
        self.sentence = sentence
        self.model_structure = model_structure

        # Store values from model_structure
        self.N = self.model_structure.semantics.N
        self.main_point = self.model_structure.main_point

        # Store values from sentence
        self.name = self.sentence.name
        self.operator = self.sentence.operator
        self.arguments = self.sentence.arguments
        self.sentence_letter = self.sentence.sentence_letter

        # Store values from model_constraints
        self.model_constraints = self.model_structure.model_constraints
        self.semantics = self.model_constraints.semantics
        self.sentence_letters = self.model_constraints.sentence_letters
        self.settings = self.model_constraints.settings

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if isinstance(other, PropositionDefaults):
            return self.name == other.name
        return False

    def set_colors(self, name, indent_num, truth_value, world_state, use_colors):
        """Set color formatting for proposition display.
        
        Args:
            name: The proposition name
            indent_num: Indentation level
            truth_value: True/False/None
            world_state: Current world state string
            use_colors: Whether to use color formatting
            
        Returns:
            Tuple of (RESET, FULL, PART) color codes
        """
        if not use_colors:
            VOID = ""
            self.color_name = VOID
            self.color_truth_value = VOID
            return VOID, VOID, VOID
            
        RED, GREEN, RESET = "\033[31m", "\033[32m", "\033[0m" 
        FULL, PART = "\033[37m", "\033[33m"
        
        if indent_num == 1:
            FULL, PART = (GREEN, GREEN) if truth_value else (RED, RED)
            if truth_value is None:
                print(
                    f"\n{RED}WARNING:{RESET}"
                    f"{name} is neither true nor false at {world_state}.\n"
                )
        
        # Store for later use
        self.color_name = FULL
        self.color_truth_value = FULL if truth_value else RED
        
        return RESET, FULL, PART