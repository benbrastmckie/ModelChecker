"""Exclusion theory specific model iteration implementation.

This module provides the ExclusionModelIterator implementation which handles:
1. Detecting differences between models using exclusion theory semantics
2. Creating constraints to differentiate models with exclusion theory primitives
3. Checking model isomorphism for exclusion theory models
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
    formatter = logging.Formatter('[EXCLUSION-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class ExclusionModelIterator(BaseModelIterator):
    """Model iterator for the exclusion theory.
    
    This class extends BaseModelIterator with exclusion theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for exclusion theory models.
    
    The exclusion theory uses a state-based semantics with:
    - States represented as bit vectors
    - Verification (but not falsification) as primitive relation
    - Exclusion relation between states
    - Incompatibility as a derived relation from exclusion
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two exclusion theory model structures.
        
        For exclusion theory, this focuses on:
        - Changes in which states are worlds
        - Changes in which states are possible
        - Changes in verification of sentence letters
        - Changes in exclusion relationships between states
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Try to use the theory-specific detect_model_differences method on the structure
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    return differences
            except Exception as e:
                logger.warning(f"Error in exclusion theory difference detection: {e}")
        
        # Fall back to our own implementation
        differences = self._calculate_exclusion_differences(new_structure, previous_structure)
        
        return differences
    
    def _calculate_exclusion_differences(self, new_structure, previous_structure):
        """Exclusion theory specific implementation of difference detection.
        
        This is more sophisticated than the base _calculate_basic_differences method
        as it understands exclusion theory semantics like verification and exclusion.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences with exclusion theory semantics
        """
        # For debugging
        import sys
        print("\nDEBUG: Starting exclusion difference calculation", file=sys.stderr)
        
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize exclusion theory-specific differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "sentence_letters": {},
            "exclusion_relations": {}
        }
        
        # Compare worlds
        old_worlds = set(getattr(previous_structure, "z3_world_states", []))
        new_worlds = set(getattr(new_structure, "z3_world_states", []))
        
        print(f"DEBUG: Old worlds: {list(old_worlds)}", file=sys.stderr)
        print(f"DEBUG: New worlds: {list(new_worlds)}", file=sys.stderr)
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Compare possible states - use the standard z3_possible_states attribute name
        old_states = set(getattr(previous_structure, "z3_possible_states", []))
        new_states = set(getattr(new_structure, "z3_possible_states", []))
            
        print(f"DEBUG: Old possible states: {list(old_states)}", file=sys.stderr)
        print(f"DEBUG: New possible states: {list(new_states)}", file=sys.stderr)
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare verification for each sentence letter
        semantics = new_structure.semantics
        for letter in new_structure.sentence_letters:
            old_verifiers = []
            new_verifiers = []
            
            # Check verifiers
            for state in old_states.union(new_states):
                try:
                    # For previously possible states
                    if state in old_states:
                        if bool(previous_model.eval(semantics.verifies(letter, state), model_completion=True)):
                            old_verifiers.append(state)
                
                    # For currently possible states
                    if state in new_states:
                        if bool(new_model.eval(semantics.verifies(letter, state), model_completion=True)):
                            new_verifiers.append(state)
                except Exception:
                    # Skip problematic states
                    pass
            
            # Only record differences if something changed
            old_verifiers_set = set(old_verifiers)
            new_verifiers_set = set(new_verifiers)
            
            added_verifiers = [state for state in new_verifiers if state not in old_verifiers_set]
            removed_verifiers = [state for state in old_verifiers if state not in new_verifiers_set]
            
            if added_verifiers or removed_verifiers:
                differences["sentence_letters"][str(letter)] = {
                    "old": old_verifiers,
                    "new": new_verifiers,
                    "verifiers": {
                        "added": added_verifiers,
                        "removed": removed_verifiers
                    }
                }
                
        # Compare exclusion relationships if available
        if hasattr(semantics, 'excludes'):
            all_states = list(old_states.union(new_states))
            for i, state1 in enumerate(all_states):
                for j, state2 in enumerate(all_states[i:], i):
                    # Skip identical states
                    if state1 == state2:
                        continue
                        
                    try:
                        # Check if exclusion relationship changed
                        old_excludes = False
                        new_excludes = False
                        
                        if state1 in old_states and state2 in old_states:
                            old_excludes = bool(previous_model.eval(semantics.excludes(state1, state2), model_completion=True))
                            
                        if state1 in new_states and state2 in new_states:
                            new_excludes = bool(new_model.eval(semantics.excludes(state1, state2), model_completion=True))
                            
                        if old_excludes != new_excludes:
                            state_pair = f"{state1},{state2}"
                            differences["exclusion_relations"][state_pair] = {
                                "old": old_excludes,
                                "new": new_excludes
                            }
                    except Exception:
                        # Skip problematic state pairs
                        pass
        
        # Final check for actual differences
        has_differences = (
            differences["worlds"]["added"] or 
            differences["worlds"]["removed"] or
            differences["possible_states"]["added"] or 
            differences["possible_states"]["removed"] or
            differences["sentence_letters"] or
            differences["exclusion_relations"]
        )
        
        print(f"DEBUG: Has differences: {has_differences}", file=sys.stderr)
        if has_differences:
            print(f"DEBUG: Difference summary:", file=sys.stderr)
            print(f"  Worlds added: {len(differences['worlds']['added'])}", file=sys.stderr)
            print(f"  Worlds removed: {len(differences['worlds']['removed'])}", file=sys.stderr)
            print(f"  Possible states added: {len(differences['possible_states']['added'])}", file=sys.stderr)
            print(f"  Possible states removed: {len(differences['possible_states']['removed'])}", file=sys.stderr)
            print(f"  Sentence letter changes: {len(differences['sentence_letters'])}", file=sys.stderr)
            print(f"  Exclusion relation changes: {len(differences['exclusion_relations'])}", file=sys.stderr)
        
        return differences
    
    def _create_difference_constraint(self, previous_models):
        """Create exclusion theory-specific constraints to differentiate models.
        
        This focuses on the key relationships in exclusion theory:
        - Verification
        - Exclusion relationships
        - Possible states and worlds
        
        Args:
            previous_models: List of Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint requiring difference from previous models
        """
        logger.debug("Creating difference constraints for exclusion theory")
        
        # Get key structures from build_example
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # For each previous model, create a constraint requiring at least one difference
        model_diff_constraints = []
        
        for prev_model in previous_models:
            # Focus on verification and exclusion functions
            diff_components = []
            
            # 1. Differences in verification
            for letter in model_structure.sentence_letters:
                for state in model_structure.all_states:
                    try:
                        prev_value = prev_model.eval(semantics.verifies(letter, state), model_completion=True)
                        diff_components.append(semantics.verifies(letter, state) != prev_value)
                    except Exception:
                        pass
            
            # 2. Differences in exclusion relationships
            if hasattr(semantics, 'excludes'):
                for state1 in model_structure.all_states:
                    for state2 in model_structure.all_states:
                        try:
                            prev_value = prev_model.eval(semantics.excludes(state1, state2), model_completion=True)
                            diff_components.append(semantics.excludes(state1, state2) != prev_value)
                        except Exception:
                            pass
            
            # 3. Differences in possible states
            for state in model_structure.all_states:
                try:
                    prev_value = prev_model.eval(semantics.possible(state), model_completion=True)
                    diff_components.append(semantics.possible(state) != prev_value)
                except Exception:
                    pass
            
            # 4. Differences in worlds
            for state in model_structure.all_states:
                try:
                    prev_value = prev_model.eval(semantics.is_world(state), model_completion=True)
                    diff_components.append(semantics.is_world(state) != prev_value)
                except Exception:
                    pass
            
            # The new model must be different in at least one way
            if diff_components:
                model_diff_constraints.append(z3.Or(diff_components))
            
        # The new model must be different from ALL previous models
        if model_diff_constraints:
            return z3.And(model_diff_constraints)
        else:
            raise RuntimeError("Could not create any difference constraints for exclusion theory")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints that force structural differences for exclusion theory.
        
        For exclusion theory models, this focuses on:
        - Different patterns of verification
        - Different numbers of worlds and possible states
        - Different exclusion relationship patterns
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        # Get model structure
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # Create constraints to force structural differences
        constraints = []
        
        # Try to force a different number of worlds
        try:
            # Count current worlds
            current_worlds = sum(1 for state in model_structure.all_states 
                               if bool(z3_model.eval(semantics.is_world(state), model_completion=True)))
            
            # Force either more or fewer worlds
            world_count = z3.Sum([z3.If(semantics.is_world(state), 1, 0) 
                                 for state in model_structure.all_states])
            
            if current_worlds > 1:
                constraints.append(world_count < current_worlds)
            
            if current_worlds < len(model_structure.all_states) - 1:
                constraints.append(world_count > current_worlds)
        except Exception as e:
            logger.debug(f"Error creating world count constraint: {e}")
        
        # Try to force different verification pattern
        try:
            for letter in model_structure.sentence_letters:
                # Force different verification pattern
                ver_count = z3.Sum([z3.If(semantics.verifies(letter, state), 1, 0) 
                                   for state in model_structure.all_states])
                
                # Count current verifiers
                current_ver = sum(1 for state in model_structure.all_states 
                                if bool(z3_model.eval(semantics.verifies(letter, state), model_completion=True)))
                
                if current_ver > 1:
                    constraints.append(ver_count < current_ver - 1)
                elif current_ver < len(model_structure.all_states) - 1:
                    constraints.append(ver_count > current_ver + 1)
        except Exception as e:
            logger.debug(f"Error creating verification constraint: {e}")
        
        # Try to force different exclusion patterns
        if hasattr(semantics, 'excludes'):
            try:
                # Count current exclusions
                exclusion_count = 0
                for state1 in model_structure.all_states:
                    for state2 in model_structure.all_states:
                        if state1 != state2:
                            try:
                                if bool(z3_model.eval(semantics.excludes(state1, state2), model_completion=True)):
                                    exclusion_count += 1
                            except:
                                pass
                
                # Exclusion count expression
                excl_count = z3.Sum([z3.If(semantics.excludes(s1, s2), 1, 0) 
                                   for s1 in model_structure.all_states 
                                   for s2 in model_structure.all_states 
                                   if s1 != s2])
                
                # Force significantly different exclusion count
                max_possible = len(model_structure.all_states) * (len(model_structure.all_states) - 1)
                
                if exclusion_count > max_possible // 2:
                    # If many exclusions, force few
                    constraints.append(excl_count < exclusion_count // 2)
                else:
                    # If few exclusions, force many
                    constraints.append(excl_count > max_possible - exclusion_count // 2)
            except Exception as e:
                logger.debug(f"Error creating exclusion constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints to escape isomorphic models for exclusion theory.
        
        This creates more dramatic constraints when multiple consecutive
        isomorphic models have been found.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Stronger constraint or None if creation fails
        """
        # Get model structure and semantics
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # The approach varies depending on the escape attempt
        escape_attempt = getattr(self, 'escape_attempts', 1)
        
        # Create constraints that force major structural changes
        constraints = []
        
        # 1. Force dramatically different number of worlds
        try:
            # Count current worlds
            current_worlds = sum(1 for state in model_structure.all_states 
                              if bool(isomorphic_model.eval(semantics.is_world(state), model_completion=True)))
            
            # World count expression
            world_count = z3.Sum([z3.If(semantics.is_world(state), 1, 0) 
                                for state in model_structure.all_states])
            
            # Force minimal or maximal number of worlds
            if escape_attempt == 1:
                # First attempt: force significantly different world count
                if current_worlds > len(model_structure.all_states) // 2:
                    # If many worlds, force few worlds
                    constraints.append(world_count <= 2)
                else:
                    # If few worlds, force many worlds
                    constraints.append(world_count >= len(model_structure.all_states) - 2)
            else:
                # Later attempts: extreme values
                constraints.append(world_count == 1)  # Minimal
                constraints.append(world_count == len(model_structure.all_states))  # Maximal
        except Exception as e:
            logger.debug(f"Error creating world count constraint: {e}")
        
        # 2. Force dramatically different verification patterns
        try:
            # Attempt to flip all verifications
            flip_constraints = []
            for letter in model_structure.sentence_letters:
                letter_flip = []
                for state in model_structure.all_states:
                    try:
                        prev_value = isomorphic_model.eval(semantics.verifies(letter, state), model_completion=True)
                        letter_flip.append(semantics.verifies(letter, state) != prev_value)
                    except:
                        pass
                
                # Flip all or most verifications for this letter
                if letter_flip:
                    flip_constraints.append(z3.And(letter_flip))
            
            # Add constraints to flip verifications for either all letters or each letter individually
            if flip_constraints:
                if len(flip_constraints) > 1:
                    # Either flip all letters or flip each letter individually
                    constraints.append(z3.And(flip_constraints))  # Flip all
                    for flip in flip_constraints:
                        constraints.append(flip)  # Flip individual letters
                else:
                    constraints.append(flip_constraints[0])
        except Exception as e:
            logger.debug(f"Error creating verification flip constraint: {e}")
        
        # 3. Force dramatically different exclusion relations
        if hasattr(semantics, 'excludes'):
            try:
                # Try to flip exclusion relations
                exclusion_flips = []
                for state1 in model_structure.all_states:
                    for state2 in model_structure.all_states:
                        if state1 != state2:
                            try:
                                prev_value = isomorphic_model.eval(semantics.excludes(state1, state2), model_completion=True)
                                exclusion_flips.append(semantics.excludes(state1, state2) != prev_value)
                            except:
                                pass
                
                if exclusion_flips:
                    constraints.append(z3.And(exclusion_flips))
            except Exception as e:
                logger.debug(f"Error creating exclusion flip constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
    def display_model_differences(self, model_structure, output=sys.stdout):
        """Format differences for display using exclusion theory semantics.
        
        Args:
            model_structure: The model structure with differences
            output: Output stream for writing output
        """
        if not hasattr(model_structure, 'model_differences'):
            return
            
        differences = model_structure.model_differences
        if not differences:
            return
            
        # Check if there are actual differences
        has_diffs = (
            differences.get('worlds', {}).get('added') or 
            differences.get('worlds', {}).get('removed') or
            differences.get('possible_states', {}).get('added') or 
            differences.get('possible_states', {}).get('removed') or
            differences.get('sentence_letters') or 
            differences.get('exclusion_relations')
        )
        
        if not has_diffs:
            return
        
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # Print world changes
        if 'worlds' in differences and (differences['worlds'].get('added') or differences['worlds'].get('removed')):
            print("World Changes:", file=output)
            
            # Dump the actual world list for debugging
            print(f"DEBUG DISPLAY: Added worlds: {differences['worlds']['added']}", file=sys.stderr)
            print(f"DEBUG DISPLAY: Removed worlds: {differences['worlds']['removed']}", file=sys.stderr)
            
            if differences['worlds'].get('added'):
                for world in differences['worlds']['added']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  + {world_str} (world)", file=output)
                    except Exception as e:
                        print(f"  + {world} (world) [Error: {e}]", file=output)
            
            if differences['worlds'].get('removed'):
                for world in differences['worlds']['removed']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  - {world_str} (world)", file=output)
                    except Exception as e:
                        print(f"  - {world} (world) [Error: {e}]", file=output)
        
        # Print possible state changes
        if 'possible_states' in differences and (differences['possible_states'].get('added') or differences['possible_states'].get('removed')):
            print("\nPossible State Changes:", file=output)
            
            if differences['possible_states'].get('added'):
                for state in differences['possible_states']['added']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  + {state_str}", file=output)
                    except:
                        print(f"  + {state}", file=output)
            
            if differences['possible_states'].get('removed'):
                for state in differences['possible_states']['removed']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  - {state_str}", file=output)
                    except:
                        print(f"  - {state}", file=output)
        
        # Print sentence letter verification changes
        if 'sentence_letters' in differences and differences['sentence_letters']:
            print("\nSentence Letter Changes:", file=output)
            
            for letter, changes in differences['sentence_letters'].items():
                # Get the right letter name
                letter_name = letter
                if hasattr(model_structure, '_get_friendly_letter_name'):
                    try:
                        letter_name = model_structure._get_friendly_letter_name(letter)
                    except:
                        pass
                
                # Print letter changes
                print(f"  {letter_name}:", file=output)
                
                # Handle detailed verifier changes
                if isinstance(changes, dict) and 'verifiers' in changes:
                    # Verifier changes
                    if changes['verifiers'].get('added') or changes['verifiers'].get('removed'):
                        if changes['verifiers'].get('added'):
                            added_states = []
                            for state in changes['verifiers']['added']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    added_states.append(state_str)
                                except:
                                    added_states.append(str(state))
                            added_str = ', '.join(added_states)
                            print(f"    Verifiers: + {{{added_str}}}", file=output)
                            
                        if changes['verifiers'].get('removed'):
                            removed_states = []
                            for state in changes['verifiers']['removed']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    removed_states.append(state_str)
                                except:
                                    removed_states.append(str(state))
                            removed_str = ', '.join(removed_states)
                            print(f"    Verifiers: - {{{removed_str}}}", file=output)
                
                # Simpler format showing old and new values
                elif isinstance(changes, dict) and 'old' in changes and 'new' in changes:
                    old_verifiers = changes['old']
                    new_verifiers = changes['new']
                    
                    try:
                        old_ver_str = pretty_set_print([bitvec_to_substates(v, model_structure.semantics.N) for v in old_verifiers])
                        new_ver_str = pretty_set_print([bitvec_to_substates(v, model_structure.semantics.N) for v in new_verifiers])
                        
                        print(f"    Verifiers: {old_ver_str} -> {new_ver_str}", file=output)
                    except:
                        # Fall back to simple representation
                        print(f"    Verifiers: {old_verifiers} -> {new_verifiers}", file=output)
                
                # Handle very simple changes
                else:
                    print(f"    Changed from previous model", file=output)
        
        # Print exclusion relationship changes
        if 'exclusion_relations' in differences and differences['exclusion_relations']:
            print("\nExclusion Relationship Changes:", file=output)
            
            for pair, change in differences['exclusion_relations'].items():
                # Try to parse the state pair
                try:
                    states = pair.split(',')
                    if len(states) == 2:
                        state1_bitvec = int(states[0])
                        state2_bitvec = int(states[1])
                        
                        state1_str = bitvec_to_substates(state1_bitvec, model_structure.semantics.N)
                        state2_str = bitvec_to_substates(state2_bitvec, model_structure.semantics.N)
                        
                        if change.get('new'):
                            print(f"  {state1_str} now excludes {state2_str}", file=output)
                        else:
                            print(f"  {state1_str} no longer excludes {state2_str}", file=output)
                        continue
                except:
                    pass
                
                # Fall back to simple representation
                if isinstance(change, dict) and 'old' in change and 'new' in change:
                    status = "now excludes" if change['new'] else "no longer excludes"
                    print(f"  {pair}: {status}", file=output)
                else:
                    print(f"  {pair}: changed", file=output)


# Static function for displaying model differences
def display_model_differences(model_structure, output=sys.stdout):
    """Display differences between models using exclusion theory semantics.
    
    This static function can be called directly from the model structure.
    
    Args:
        model_structure: Model structure with differences to display
        output: Output stream for displaying differences
    """
    if not hasattr(model_structure, 'model_differences'):
        return
        
    differences = model_structure.model_differences
    if not differences:
        return
        
    # Check if we have actual differences
    has_diffs = (
        differences.get('worlds', {}).get('added') or 
        differences.get('worlds', {}).get('removed') or
        differences.get('possible_states', {}).get('added') or 
        differences.get('possible_states', {}).get('removed') or
        differences.get('sentence_letters') or 
        differences.get('exclusion_relations')
    )
    
    if not has_diffs:
        return
    
    print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
    
    # Print world changes
    if 'worlds' in differences and (differences['worlds'].get('added') or differences['worlds'].get('removed')):
        print("World Changes:", file=output)
        
        if differences['worlds'].get('added'):
            for world in differences['worlds']['added']:
                try:
                    world_str = bitvec_to_substates(world, model_structure.semantics.N)
                    print(f"  + {world_str} (world)", file=output)
                except:
                    print(f"  + {world} (world)", file=output)
        
        if differences['worlds'].get('removed'):
            for world in differences['worlds']['removed']:
                try:
                    world_str = bitvec_to_substates(world, model_structure.semantics.N)
                    print(f"  - {world_str} (world)", file=output)
                except:
                    print(f"  - {world} (world)", file=output)
    
    # Print possible state changes
    if 'possible_states' in differences and (differences['possible_states'].get('added') or differences['possible_states'].get('removed')):
        print("\nPossible State Changes:", file=output)
        
        if differences['possible_states'].get('added'):
            for state in differences['possible_states']['added']:
                try:
                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                    print(f"  + {state_str}", file=output)
                except:
                    print(f"  + {state}", file=output)
        
        if differences['possible_states'].get('removed'):
            for state in differences['possible_states']['removed']:
                try:
                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                    print(f"  - {state_str}", file=output)
                except:
                    print(f"  - {state}", file=output)
    
    # Print exclusion relationship changes
    if 'exclusion_relations' in differences and differences['exclusion_relations']:
        print("\nExclusion Relationship Changes:", file=output)
        
        for pair, change in differences['exclusion_relations'].items():
            # Try to parse the state pair
            try:
                states = pair.split(',')
                if len(states) == 2:
                    state1_bitvec = int(states[0])
                    state2_bitvec = int(states[1])
                    
                    state1_str = bitvec_to_substates(state1_bitvec, model_structure.semantics.N)
                    state2_str = bitvec_to_substates(state2_bitvec, model_structure.semantics.N)
                    
                    if change.get('new'):
                        print(f"  {state1_str} now excludes {state2_str}", file=output)
                    else:
                        print(f"  {state1_str} no longer excludes {state2_str}", file=output)
                    continue
            except:
                pass
            
            # Fall back to simple representation
            if isinstance(change, dict) and 'old' in change and 'new' in change:
                status = "now excludes" if change['new'] else "no longer excludes"
                print(f"  {pair}: {status}", file=output)
            else:
                print(f"  {pair}: changed", file=output)

# Static function for displaying differences without an iterator instance
def display_differences(model_structure, output=sys.stdout):
    """Display differences between models using exclusion theory semantics.
    
    This static function can be called directly without creating an iterator instance.
    
    Args:
        model_structure: Model structure with differences to display
        output: Output stream for displaying differences
    """
    # Check if we have differences to display
    if not hasattr(model_structure, 'model_differences'):
        print("No model_differences attribute", file=output)
        return
        
    # Get the model differences
    differences = model_structure.model_differences
    
    # Check if differences exist
    has_diffs = False
    if differences and isinstance(differences, dict):
        # Check for actual content in the difference categories
        if ((differences.get('worlds', {}).get('added') or 
             differences.get('worlds', {}).get('removed') or
             differences.get('possible_states', {}).get('added') or
             differences.get('possible_states', {}).get('removed') or
             differences.get('sentence_letters') or 
             differences.get('exclusion_relations'))):
            has_diffs = True
            
    if not has_diffs:
        print("No differences found between models", file=output)
        return
        
    # Use the ExclusionModelIterator's display method with a temporary instance
    temp_iterator = object.__new__(ExclusionModelIterator)
    temp_iterator.display_model_differences(model_structure, output)

# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for an exclusion theory example.
    
    This function creates a ExclusionModelIterator for the given example
    and uses it to find up to max_iterations distinct models.
    
    Args:
        example: A BuildExample instance with an exclusion theory model
        max_iterations: Maximum number of models to find (optional)
        
    Returns:
        list: List of distinct model structures
    """
    # Create the iterator with the example
    iterator = ExclusionModelIterator(example)
    
    # Set max iterations if provided
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    
    # Print debug info
    import sys
    print("DEBUG CORE: Setting model_differences = True", file=sys.stderr)
    
    # Perform iteration
    model_structures = iterator.iterate()
    
    # Enable difference display on the model structures
    for i in range(1, len(model_structures)):
        # Explicitly call the difference calculation between consecutive models
        if i > 0:
            previous_structure = model_structures[i-1] 
            current_structure = model_structures[i]
            
            # Calculate differences and store them in the current structure
            differences = iterator._calculate_exclusion_differences(current_structure, previous_structure)
            current_structure.model_differences = differences
            current_structure.previous_structure = previous_structure
            
            # Directly display the differences
            print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n")
            
            # World changes
            if differences.get('worlds', {}).get('added') or differences.get('worlds', {}).get('removed'):
                print("World Changes:")
                
                if differences.get('worlds', {}).get('added'):
                    for world in differences['worlds']['added']:
                        try:
                            world_str = bitvec_to_substates(world, current_structure.N)
                            print(f"  + {world_str} (world)")
                        except:
                            print(f"  + {world} (world)")
                
                if differences.get('worlds', {}).get('removed'):
                    for world in differences['worlds']['removed']:
                        try:
                            world_str = bitvec_to_substates(world, current_structure.N)
                            print(f"  - {world_str} (world)")
                        except:
                            print(f"  - {world} (world)")
            
            # Possible state changes
            if differences.get('possible_states', {}).get('added') or differences.get('possible_states', {}).get('removed'):
                print("\nPossible State Changes:")
                
                if differences.get('possible_states', {}).get('added'):
                    for state in differences['possible_states']['added']:
                        try:
                            state_str = bitvec_to_substates(state, current_structure.N)
                            print(f"  + {state_str}")
                        except:
                            print(f"  + {state}")
                
                if differences.get('possible_states', {}).get('removed'):
                    for state in differences['possible_states']['removed']:
                        try:
                            state_str = bitvec_to_substates(state, current_structure.N)
                            print(f"  - {state_str}")
                        except:
                            print(f"  - {state}")
            
            # Exclusion relationship changes
            if differences.get('exclusion_relations', {}):
                print("\nExclusion Relationship Changes:")
                
                for pair, change in differences['exclusion_relations'].items():
                    # Try to parse the state pair
                    try:
                        states = pair.split(',')
                        if len(states) == 2:
                            state1_bitvec = int(states[0])
                            state2_bitvec = int(states[1])
                            
                            state1_str = bitvec_to_substates(state1_bitvec, current_structure.N)
                            state2_str = bitvec_to_substates(state2_bitvec, current_structure.N)
                            
                            if change.get('new'):
                                print(f"  {state1_str} now excludes {state2_str}")
                            else:
                                print(f"  {state1_str} no longer excludes {state2_str}")
                            continue
                    except:
                        pass
                    
                    # Fall back to simple representation
                    if isinstance(change, dict) and 'old' in change and 'new' in change:
                        status = "now excludes" if change['new'] else "no longer excludes"
                        print(f"  {pair}: {status}")
                    else:
                        print(f"  {pair}: changed")
                        
            print("") # Extra line after differences
    
    return model_structures