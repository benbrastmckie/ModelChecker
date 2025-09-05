"""Operator translation utilities.

This module handles translation of logical operators in formulas
according to theory-specific dictionaries.
"""


class OperatorTranslation:
    """Handles translation of logical operators in formulas."""
    
    def translate(self, example_case, dictionary):
        """Use dictionary to replace logical operators in logical formulas.
        
        Takes a dictionary mapping old operators to new operators and replaces all
        occurrences of old operators with their new versions in the premises and
        conclusions.
        
        Args:
            example_case (list): A list containing [premises, conclusions, settings]
            dictionary (dict): Mapping of old operators to new operators
            
        Returns:
            list: New example case with translated operators in premises and conclusions
        """
        premises, conclusions, settings = example_case
        
        def replace_operators(logical_list, dictionary):
            for old, new in dictionary.items():
                logical_list = [sentence.replace(old, new) for sentence in logical_list]
            return logical_list
            
        new_premises = replace_operators(premises, dictionary)
        new_conclusion = replace_operators(conclusions, dictionary)
        return [new_premises, new_conclusion, settings]
    
    def translate_example(self, example_case, semantic_theories):
        """Translates example case for each semantic theory using their dictionaries.

        Takes an example case and applies any operator translations defined in each semantic
        theory's dictionary to create theory-specific versions of the example.

        Args:
            example_case (list): List containing [premises, conclusions, settings]
            semantic_theories (dict): Dictionary mapping theory names to their implementations

        Returns:
            list: List of tuples (theory_name, semantic_theory, translated_case) where:
                - theory_name (str): Name of the semantic theory
                - semantic_theory (dict): The semantic theory implementation
                - translated_case (list): Example case with operators translated for that theory
        """
        example_theory_tuples = []
        for theory_name, semantic_theory in semantic_theories.items():
            translated_case = example_case.copy()
            dictionary = semantic_theory.get("dictionary", None)
            if dictionary:
                translated_case = self.translate(translated_case, dictionary)
            example_tuple = (theory_name, semantic_theory, translated_case)
            example_theory_tuples.append(example_tuple)
        return example_theory_tuples