# Graph Isomorphism Checks for Model Comparison

## Current Situation

The isomorphism checking feature for the ModelIterator in `iterate.py` has been successfully implemented. This feature identifies when models are syntactically different but structurally isomorphic, allowing users to find genuinely different models that represent distinct logical possibilities.

### Completed Features

1. **Graph Representation**
   - The `ModelGraph` class in `graph_utils.py` creates graph representations of logical models.
   - Nodes represent worlds with proposition truth values as attributes.
   - Edges represent accessibility relations between worlds.
   - Theory-specific properties are supported via extension methods.

2. **Isomorphism Detection**
   - Efficiently detects isomorphic models despite different variable assignments.
   - Uses quick filtering with invariant hashing before full isomorphism checking.
   - Provides clear output when isomorphic models are detected.

3. **Non-Isomorphic Constraint Generation**
   - When an isomorphic model is found, generates constraints to find a structurally different model.
   - Uses multiple constraint strategies (edge flipping, truth value modifications).
   - Handles cases where no more non-isomorphic models exist.

4. **Stability Improvements**
   - Added timeout handling to prevent hanging during iterative search.
   - Implemented recursion depth limiting to avoid infinite loops.
   - Added comprehensive error handling and debugging output.

## Current Limitations

Despite the successful implementation, there are still a few areas that need improvement:

1. **Model Difference Presentation**
   - Differences between models are currently shown using atom sorts (AtomSort!val!X) rather than user-friendly proposition names.
   - Differences are only shown at the end of the iteration, not immediately after each model is found.
   - The presentation doesn't clearly show which states (represented as bit vectors) differ in their proposition assignments.

2. **Performance Considerations**
   - For very large models, isomorphism checking may still be computationally expensive.
   - The current constraint generation might not always find the most interesting non-isomorphic models.

## Next Steps

### 1. Improve Difference Reporting

1. **Immediate Difference Display**
   - Modify the `iterate.py` process to print model differences immediately after each new model is found (not including the first model).
   - Make this automatic rather than requiring an explicit `print_differences` setting.

2. **Enhance Difference Representation**
   - Update the difference reporting to use the state representations of bitvectors with letters (e.g., 'a.d', 'b.c').
   - Clearly show just those sentences that differ in the propositions (ordered pairs of states) to which they are assigned.
   - Format the output to highlight which world states have changed in their proposition assignments.

3. **Implementation Plan**
   ```python
   # Example enhanced difference reporting
   def print_enhanced_model_differences(self, prev_model, current_model, output=sys.__stdout__):
       """Print user-friendly differences between models using state notation."""
       print("\n=== MODEL DIFFERENCES ===\n", file=output)
       
       # Check for isomorphism
       if hasattr(current_model, 'isomorphic_to_previous') and current_model.isomorphic_to_previous:
           print("NOTE: This model is isomorphic to a previous model despite syntactic differences.", 
                 file=output)
           print("      The structural properties are the same but variable assignments differ.", 
                 file=output)
           print("", file=output)
       
       # Extract world states as readable strings
       world_states = [bitvec_to_substates(w, self.N) for w in current_model.z3_world_states]
       
       # Print sentence letter value changes using readable state notation
       print("Changed Proposition Assignments:", file=output)
       for letter, old_new in current_model.model_differences.get('sentence_letters', {}).items():
           letter_name = str(letter).replace('AtomSort!val!', 'p')
           print(f"  {letter_name}:", file=output)
           
           # Show verifiers (states where proposition is true)
           old_verifiers = self._get_state_names_for_letter(prev_model, letter, True)
           new_verifiers = self._get_state_names_for_letter(current_model, letter, True)
           if old_verifiers != new_verifiers:
               print(f"    Verifiers: {old_verifiers} → {new_verifiers}", file=output)
           
           # Show falsifiers (states where proposition is false)
           old_falsifiers = self._get_state_names_for_letter(prev_model, letter, False)
           new_falsifiers = self._get_state_names_for_letter(current_model, letter, False)
           if old_falsifiers != new_falsifiers:
               print(f"    Falsifiers: {old_falsifiers} → {new_falsifiers}", file=output)
   ```

### 2. Optimize Isomorphism Detection

1. **Performance Optimization**
   - Implement more efficient graph comparison for larger models.
   - Add caching of intermediate results during isomorphism checks.
   - Consider parallel processing for checking multiple models simultaneously.

2. **Enhanced Constraint Generation**
   - Develop more sophisticated constraints to generate more interesting non-isomorphic models.
   - Add theory-specific constraints to focus on semantically relevant differences.
   - Provide options to control the types of differences sought (e.g., focus on relationship changes vs. proposition changes).

### 3. User Control Enhancements

1. **API Improvements**
   - Simplify the isomorphism checking API to make it a standard part of model iteration.
   - Add options to control isomorphism detection behavior (strict/relaxed, timeout settings).
   - Provide methods to export and visualize the graph representations.

2. **Documentation**
   - Update user documentation to describe the isomorphism checking features.
   - Add examples showing how to interpret model differences.
   - Provide guidance on when to use different isomorphism-related settings.

## Conclusion

The graph isomorphism checking feature has substantially improved the model iteration system by filtering out structurally equivalent models. The next phase of development will focus on enhancing the user experience through better presentation of differences and optimizing the performance for larger models. These improvements will further strengthen the ModelChecker's capabilities for exploring logical semantic spaces.
