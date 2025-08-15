"""Imposition theory specific model iteration implementation.

This module provides the ImpositionModelIterator implementation which handles:
1. Detecting differences between models using imposition theory semantics
2. Creating constraints to differentiate models with imposition theory primitives
3. Checking model isomorphism for imposition theory models
"""

import z3
import sys
import logging

from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_substates, pretty_set_print

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[IMPOSITION-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class ImpositionModelIterator(BaseModelIterator):
    """Model iterator for the imposition theory.
    
    This class extends CoreModelIterator with imposition theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for imposition theory models.
    
    The imposition theory uses a state-based semantics with:
    - States represented as bit vectors
    - Verification and falsification as primitive relations
    - Imposition relation between states
    - Part-whole relationships via imposition
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two imposition theory model structures.
        
        For imposition theory, this focuses on:
        - Changes in which states are worlds
        - Changes in which states are possible
        - Changes in verification and falsification of sentence letters
        - Changes in imposition relationships between states
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Use imposition theory-specific difference detection
        differences = self._calculate_imposition_differences(new_structure, previous_structure)
        
        return differences
    
    def _calculate_imposition_differences(self, new_structure, previous_structure):
        """Imposition theory specific implementation of difference detection.
        
        This is more sophisticated than the base _calculate_basic_differences method
        as it understands imposition theory semantics like verification, falsification,
        and imposition relations.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences with imposition theory semantics
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        semantics = new_structure.semantics
        
        # Initialize imposition theory-specific differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "verification": {},  # Changed from "sentence_letters" to match logos
            "falsification": {},
            "imposition_relations": {}
        }
        
        # Compare worlds and possible states
        old_worlds = set(getattr(previous_structure, "z3_world_states", []))
        new_worlds = set(getattr(new_structure, "z3_world_states", []))
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Compare possible states
        old_states = set(getattr(previous_structure, "z3_possible_states", []))
        new_states = set(getattr(new_structure, "z3_possible_states", []))
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare verification and falsification for each sentence letter
        all_states = list(old_states.union(new_states))
        
        for letter in new_structure.sentence_letters:
            try:
                # Get the atom for this letter
                atom = None
                if hasattr(letter, 'sentence_letter') and letter.sentence_letter is not None:
                    atom = letter.sentence_letter
                else:
                    continue
                
                letter_str = str(letter)
                
                # Check verification changes
                verify_added = []
                verify_removed = []
                
                for state in all_states:
                    try:
                        old_verify = False
                        new_verify = False
                        
                        if state in old_states:
                            old_verify = bool(previous_model.eval(semantics.verify(state, atom), model_completion=True))
                        if state in new_states:
                            new_verify = bool(new_model.eval(semantics.verify(state, atom), model_completion=True))
                        
                        if not old_verify and new_verify:
                            verify_added.append(state)
                        elif old_verify and not new_verify:
                            verify_removed.append(state)
                    except:
                        pass
                
                if verify_added or verify_removed:
                    differences["verification"][letter_str] = {
                        "added": verify_added,
                        "removed": verify_removed
                    }
                
                # Check falsification changes
                falsify_added = []
                falsify_removed = []
                
                for state in all_states:
                    try:
                        old_falsify = False
                        new_falsify = False
                        
                        if state in old_states:
                            old_falsify = bool(previous_model.eval(semantics.falsify(state, atom), model_completion=True))
                        if state in new_states:
                            new_falsify = bool(new_model.eval(semantics.falsify(state, atom), model_completion=True))
                        
                        if not old_falsify and new_falsify:
                            falsify_added.append(state)
                        elif old_falsify and not new_falsify:
                            falsify_removed.append(state)
                    except:
                        pass
                
                if falsify_added or falsify_removed:
                    differences["falsification"][letter_str] = {
                        "added": falsify_added,
                        "removed": falsify_removed
                    }
                    
            except Exception:
                continue
                
        # Compare imposition relationships if available
        if hasattr(semantics, 'imposition'):
            for i, state1 in enumerate(all_states):
                for j, state2 in enumerate(all_states[i:], i):
                    if state1 == state2:
                        continue
                        
                    try:
                        # Check if imposition relationship changed
                        old_imposes = False
                        new_imposes = False
                        
                        if state1 in old_states and state2 in old_states:
                            # Imposition takes three arguments: (imposed_state, world, outcome_world)
                            for outcome in all_states:
                                if bool(previous_model.eval(semantics.imposition(state1, state2, outcome), model_completion=True)):
                                    old_imposes = True
                                    break
                            
                        if state1 in new_states and state2 in new_states:
                            for outcome in all_states:
                                if bool(new_model.eval(semantics.imposition(state1, state2, outcome), model_completion=True)):
                                    new_imposes = True
                                    break
                            
                        if old_imposes != new_imposes:
                            state_pair = f"{state1},{state2}"
                            differences["imposition_relations"][state_pair] = {
                                "old": old_imposes,
                                "new": new_imposes
                            }
                    except Exception:
                        pass
                
        return differences
    
    def display_model_differences(self, model_structure, output=sys.stdout):
        """Format differences for display using imposition theory semantics.
        
        Args:
            model_structure: The model structure with differences
            output: Output stream for writing output
        """
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return
            
        differences = model_structure.model_differences
        
        # Use colors like logos theory
        print("\n\033[33m=== DIFFERENCES FROM PREVIOUS MODEL ===\033[0m\n", file=output)
        
        # Print world changes
        if 'worlds' in differences and (differences['worlds'].get('added') or differences['worlds'].get('removed')):
            print("\033[34mWorld Changes:\033[0m", file=output)
            
            if differences['worlds'].get('added'):
                for world in differences['worlds']['added']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  \033[32m+ {world_str} (now a world)\033[0m", file=output)
                    except:
                        print(f"  \033[32m+ {world} (now a world)\033[0m", file=output)
            
            if differences['worlds'].get('removed'):
                for world in differences['worlds']['removed']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  \033[31m- {world_str} (no longer a world)\033[0m", file=output)
                    except:
                        print(f"  \033[31m- {world} (no longer a world)\033[0m", file=output)
        
        # Print possible state changes
        if 'possible_states' in differences and (differences['possible_states'].get('added') or differences['possible_states'].get('removed')):
            print("\n\033[34mPossible State Changes:\033[0m", file=output)
            
            if differences['possible_states'].get('added'):
                for state in differences['possible_states']['added']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  \033[32m+ {state_str} (now possible)\033[0m", file=output)
                    except:
                        print(f"  \033[32m+ {state} (now possible)\033[0m", file=output)
            
            if differences['possible_states'].get('removed'):
                for state in differences['possible_states']['removed']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  \033[31m- {state_str} (now impossible)\033[0m", file=output)
                    except:
                        print(f"  \033[31m- {state} (now impossible)\033[0m", file=output)
        
        # Print verification changes
        if 'verification' in differences and differences['verification']:
            print("\n\033[34mVerification Changes:\033[0m", file=output)
            
            for letter_str, changes in differences['verification'].items():
                # Extract just the letter name (A, B, C, etc.)
                letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                print(f"  Letter {letter_name}:", file=output)
                
                if changes.get('added'):
                    for state in changes['added']:
                        try:
                            state_str = bitvec_to_substates(state, model_structure.semantics.N)
                            print(f"    \033[32m+ {state_str} now verifies {letter_name}\033[0m", file=output)
                        except:
                            print(f"    \033[32m+ {state} now verifies {letter_name}\033[0m", file=output)
                
                if changes.get('removed'):
                    for state in changes['removed']:
                        try:
                            state_str = bitvec_to_substates(state, model_structure.semantics.N)
                            print(f"    \033[31m- {state_str} no longer verifies {letter_name}\033[0m", file=output)
                        except:
                            print(f"    \033[31m- {state} no longer verifies {letter_name}\033[0m", file=output)
        
        # Print falsification changes
        if 'falsification' in differences and differences['falsification']:
            print("\n\033[34mFalsification Changes:\033[0m", file=output)
            
            for letter_str, changes in differences['falsification'].items():
                # Extract just the letter name (A, B, C, etc.)
                letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                print(f"  Letter {letter_name}:", file=output)
                
                if changes.get('added'):
                    for state in changes['added']:
                        try:
                            state_str = bitvec_to_substates(state, model_structure.semantics.N)
                            print(f"    \033[32m+ {state_str} now falsifies {letter_name}\033[0m", file=output)
                        except:
                            print(f"    \033[32m+ {state} now falsifies {letter_name}\033[0m", file=output)
                
                if changes.get('removed'):
                    for state in changes['removed']:
                        try:
                            state_str = bitvec_to_substates(state, model_structure.semantics.N)
                            print(f"    \033[31m- {state_str} no longer falsifies {letter_name}\033[0m", file=output)
                        except:
                            print(f"    \033[31m- {state} no longer falsifies {letter_name}\033[0m", file=output)
        
        # Print imposition relationship changes
        if 'imposition_relations' in differences and differences['imposition_relations']:
            print("\n\033[34mImposition Changes:\033[0m", file=output)
            
            for pair, change in differences['imposition_relations'].items():
                # Try to parse the state pair
                try:
                    states = pair.split(',')
                    if len(states) == 2:
                        state1_bitvec = int(states[0])
                        state2_bitvec = int(states[1])
                        
                        state1_str = bitvec_to_substates(state1_bitvec, model_structure.semantics.N)
                        state2_str = bitvec_to_substates(state2_bitvec, model_structure.semantics.N)
                        
                        if change.get('new'):
                            print(f"  \033[32m+ {state1_str} can now impose on {state2_str}\033[0m", file=output)
                        else:
                            print(f"  \033[31m- {state1_str} can no longer impose on {state2_str}\033[0m", file=output)
                        continue
                except:
                    pass
                
                # Fall back to simple representation
                if isinstance(change, dict) and 'old' in change and 'new' in change:
                    if change['new']:
                        print(f"  \033[32m+ {pair}: can now impose\033[0m", file=output)
                    else:
                        print(f"  \033[31m- {pair}: can no longer impose\033[0m", file=output)
                else:
                    print(f"  {pair}: changed", file=output)

    
    def _create_difference_constraint(self, previous_models):
        """Create constraints requiring difference from previous models.
        
        For imposition theory, focuses on verify/falsify and imposition relations.
        
        Args:
            previous_models: List of Z3 models found so far
            
        Returns:
            Z3 constraint requiring structural difference
        """
        constraints = []
        semantics = self.build_example.model_constraints.semantics
        
        for prev_model in previous_models:
            model_constraints = []
            
            # Letter value constraints (verify/falsify)
            syntax = self.build_example.example_syntax
            if hasattr(syntax, 'sentence_letters'):
                for letter_obj in syntax.sentence_letters:
                    if hasattr(letter_obj, 'sentence_letter'):
                        atom = letter_obj.sentence_letter
                        
                        for state in range(2**semantics.N):
                            prev_verify = prev_model.eval(
                                semantics.verify(state, atom), 
                                model_completion=True
                            )
                            prev_falsify = prev_model.eval(
                                semantics.falsify(state, atom), 
                                model_completion=True
                            )
                            
                            model_constraints.append(
                                semantics.verify(state, atom) != prev_verify
                            )
                            model_constraints.append(
                                semantics.falsify(state, atom) != prev_falsify
                            )
            
            # Imposition relation constraints  
            # NOTE: imposition takes 3 arguments (x, y, z) not 2
            # We need to vary over all three states to find differences
            if hasattr(semantics, 'imposition'):
                for s1 in range(2**semantics.N):
                    for s2 in range(2**semantics.N):
                        for s3 in range(2**semantics.N):
                            prev_imp = prev_model.eval(
                                semantics.imposition(s1, s2, s3),
                                model_completion=True
                            )
                            model_constraints.append(
                                semantics.imposition(s1, s2, s3) != prev_imp
                            )
            
            if model_constraints:
                constraints.append(z3.Or(*model_constraints))
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraint preventing isomorphic models."""
        # For now, simple implementation
        return z3.BoolVal(True)
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models."""
        # For now, simple implementation
        return z3.BoolVal(True)
    
    def iterate_generator(self):
        """Override to add theory-specific differences to imposition theory models.
        
        This method extends the base iterator's generator to merge imposition-specific
        differences (verification, falsification, imposition relations) with
        the generic differences calculated by the base iterator.
        
        Yields:
            Model structures with both generic and theory-specific differences
        """
        for model in super().iterate_generator():
            # Calculate theory-specific differences if we have a previous model
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_differences(
                    model, self.model_structures[-2]
                )
                # Merge theory-specific differences with existing generic ones
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs
            
            yield model


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for an imposition theory example.
    
    This function creates a ImpositionModelIterator for the given example
    and uses it to find up to max_iterations distinct models.
    
    Args:
        example: A BuildExample instance with an imposition theory model
        max_iterations: Maximum number of models to find (optional)
        
    Returns:
        list: List of distinct model structures
    """
    # Create the iterator with the example
    iterator = ImpositionModelIterator(example)
    
    # Set max iterations if provided
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    
    # Perform iteration
    model_structures = iterator.iterate()
    
    # Attach the display method to each structure so it can be called by module.py
    for structure in model_structures:
        if hasattr(structure, 'model_differences') and structure.model_differences:
            # Create a bound method that calls the iterator's display_model_differences
            # Use a closure to capture the correct structure reference
            def create_print_method(struct):
                def print_method(output=None):
                    iterator.display_model_differences(struct, output or sys.stdout)
                    return True  # Return True to indicate successful display
                return print_method
            structure.print_model_differences = create_print_method(structure)
    
    return model_structures


def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example that yields models incrementally.
    
    This function provides a generator interface for finding multiple models,
    yielding each model as it's discovered rather than returning them all at once.
    This enables proper progress tracking and iteration reports.
    
    Args:
        example: A BuildExample instance with imposition theory.
        max_iterations: Maximum number of models to find.
        
    Yields:
        Model structures as they are discovered.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator - use ImpositionModelIterator for theory-specific logic
    iterator = ImpositionModelIterator(example)
    
    # Store the iterator on the example for access to debug messages
    example._iterator = iterator
    
    # Use the generator interface
    yield from iterator.iterate_generator()

# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator