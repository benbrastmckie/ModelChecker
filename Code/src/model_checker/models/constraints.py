"""Model constraints generation for modal logic systems.

This module handles the linking of syntactic structures to semantic constraints
for model generation. It serves as the bridge between syntax and semantics in
the model checking process.
"""

import sys
from z3 import ExprRef


class ModelConstraints:
    """Links syntactic structures to semantic constraints for model generation.
    
    This class connects the syntactic representation of an argument (premises and conclusions)
    with a specific semantics implementation to generate constraints for model finding.
    It serves as the bridge between syntax and semantics in the model checking process.
    
    The class is responsible for instantiating operators with the appropriate semantics,
    generating Z3 constraints that represent the logical content of sentences, and
    managing the settings that govern the model generation process.
    
    Attributes:
        settings (dict): Configuration settings for model generation
        syntax (Syntax): The syntactic representation of the argument # TODO: Not sure this is right?
        semantics (Semantics): The semantic theory being used
        proposition_class (class): The class used to create propositions
        sentences (dict): All sentences in the argument
        sentence_letters (list): All atomic sentence letters in the argument
        operators (dict): Instantiated operator objects with the selected semantics
        premises (list): Sentence objects for premises
        conclusions (list): Sentence objects for conclusions

    Takes semantics and proposition_class as arguments to build generate
    and storing all Z3 constraints. This class is passed to ModelStructure."""

    def __init__(
        self,
        settings,
        syntax,
        semantics,
        proposition_class,
    ):

        # Store inputs
        self.syntax = syntax
        self.semantics = semantics
        self.proposition_class = proposition_class
        self.settings = settings
        # self.old_z3_models = None

        # Store syntax values
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions

        self.sentence_letters = self._load_sentence_letters()

        # Store operator dictionary
        self.operators = self.copy_dictionary(self.syntax.operator_collection)

        # use semantics to recursively update all derived_objects
        self.instantiate(self.premises + self.conclusions)

        # Use semantics to generate and store Z3 constraints
        self.frame_constraints = self.semantics.frame_constraints
        self.model_constraints = [
            constraint
            for sentence_letter in self.sentence_letters
            for constraint in self.proposition_class.proposition_constraints(
                self,
                sentence_letter,
            )
        ]
        self.premise_constraints = [
            self.semantics.premise_behavior(premise)
            for premise in self.premises
        ]
        self.conclusion_constraints = [
            self.semantics.conclusion_behavior(conclusion)
            for conclusion in self.conclusions
        ]
        self.all_constraints = (
            self.frame_constraints
            + self.model_constraints
            + self.premise_constraints
            + self.conclusion_constraints
        )

    def __str__(self):
        """Returns a string representation of the ModelConstraints object.
        
        This method is useful when using the model-checker programmatically in Python scripts.
        It provides a concise description of the ModelConstraints object by showing its
        premises and conclusions.
        
        Returns:
            str: A string in the format "ModelConstraints for premises [p1, p2, ...] and conclusions [c1, c2, ...]"
        """
        premises = list(self.syntax.premises)
        conclusions = list(self.syntax.conclusions)
        return f"ModelConstraints for premises {premises} and conclusions {conclusions}"

    # def _store_z3_model(self, old_z3_model):
    #     if self.old_z3_models is None:
    #         self.old_z3_models = [old_z3_model]
    #     else:
    #         self.old_z3_models.append(old_z3_model)

    def _load_sentence_letters(self):
        """Extracts and validates atomic sentence letters from the syntax object.
        
        Unpacks each sentence letter from the syntax object and verifies it is a valid
        Z3 expression (ExprRef type). Returns a list of all atomic sentence letters
        used in the argument.
        
        Returns:
            list: A list of Z3 ExprRef objects representing atomic sentence letters
            
        Raises:
            TypeError: If any sentence letter is not a valid Z3 ExprRef object
        """
        sentence_letters = []
        for packed_letter in self.syntax.sentence_letters:
            unpacked_letter = packed_letter.sentence_letter
            if not isinstance(unpacked_letter, ExprRef):
                raise TypeError("The sentence letter {letter} is not of type z3.ExprRef")
            sentence_letters.append(unpacked_letter) 
        return sentence_letters

    def copy_dictionary(self, operator_collection):
        """Creates a new dictionary by copying operators from the operator collection.
        
        Takes an operator collection and creates a new dictionary where each operator
        is instantiated with the current semantics. This ensures each operator has
        its own instance with the appropriate semantic interpretation.
        
        Args:
            operator_collection (dict): Dictionary mapping operator names to operator classes
            
        Returns:
            dict: New dictionary with instantiated operator objects using current semantics
        """
        return {
            op_name : op_class(self.semantics)
            for (op_name, op_class) in operator_collection.items()
        }

    def instantiate(self, sentences):
        """Recursively updates each sentence in the given list with its proposition.
        
        This method traverses through the sentence tree and updates each sentence object
        with its corresponding proposition based on the current model constraints and
        semantics. This process links the syntactic structure with its semantic
        interpretation.
        
        Args:
            sentences (list): A list of Sentence objects to be updated
            
        Returns:
            list: The input sentences, now updated with their propositions
            
        Note:
            This method should only be called after a valid Z3 model has been found.
        """
        for sent_obj in sentences:
            if sent_obj.arguments:
                self.instantiate(sent_obj.arguments)
            sent_obj.update_objects(self)

    def inject_z3_values(self, z3_model, original_semantics):
        """Delegate Z3 value injection to theory-specific semantics.
        
        This method provides a hook for theories to inject concrete
        values from iteration. The actual injection logic MUST be
        implemented in the theory's semantics class.
        
        This method contains NO theory-specific logic and makes NO
        assumptions about model structure or any theory concepts.
        
        Args:
            z3_model: Z3 model with concrete values from iteration
            original_semantics: Original semantics instance that created the Z3 functions
            
        Note:
            The semantics.inject_z3_model_values method receives the z3_model,
            original_semantics, and self (ModelConstraints) to allow updating
            the constraint list.
        """
        # Store for potential use by model structure
        self.injected_z3_model = z3_model
        
        # Delegate to theory-specific injection if available
        if hasattr(self.semantics, 'inject_z3_model_values'):
            # Pass original semantics and self so semantics can update constraints
            self.semantics.inject_z3_model_values(z3_model, original_semantics, self)
        # No else - if theory doesn't implement injection, nothing happens

    def print_enumerate(self, output=sys.__stdout__):
        """Prints the premises and conclusions with enumerated numbering.
        
        Formats and displays the premises and conclusions with sequential numbering.
        Premises are numbered starting from 1, and conclusions continue the numbering
        sequence after premises.
        
        Args:
            output (file): Output stream to write to (defaults to sys.stdout)
            
        Example output:
            Premises:
            1. A
            2. B
            
            Conclusion:
            3. C
        """
        premises = self.syntax.premises
        conclusions = self.syntax.conclusions
        start_con_num = len(premises) + 1
        if conclusions:
            if len(premises) < 2:
                print("Premise:", file=output)
            else:
                print("Premises:", file=output)
            for index, sent in enumerate(premises, start=1):
                print(f"{index}. {sent}", file=output)
        if conclusions:
            if len(conclusions) < 2:
                print("\nConclusion:", file=output)
            else:
                print("\nConclusions:", file=output)
            for index, sent in enumerate(conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)