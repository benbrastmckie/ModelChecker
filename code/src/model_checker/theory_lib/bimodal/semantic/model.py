"""Model structure implementation for the bimodal theory.

This module contains BimodalStructure, which manages the overall semantic
model structure for bimodal logic, including world arrays that map times to
world states and the derived time-shift relations between worlds.
"""

import sys
import time

from model_checker import z3_shim as z3

from model_checker.models.structure import ModelDefaults
from model_checker.utils import bitvec_to_worldstate


class BimodalStructure(ModelDefaults):
    """Represents the model structure for a bimodal logic system.
    
    This class extends ModelDefaults to handle the specific structures needed
    for bimodal logic, including world arrays that map times to world states.
    It extracts world histories from the Z3 model and maintains consistent
    world array references for evaluation using world_ids as primary keys.
    
    Attributes:
        main_world (int): The world_id of the main world for evaluation
        main_time (int): The main time point for evaluation
        M (int): Number of time points
        all_times (range): Range of available time points
        world_arrays (dict): Maps world_id (int) to world array (Z3 object)
        world_histories (dict): Maps world_id (int) to {time: world_state} mappings
    """
    def __init__(self, model_constraints, max_time=1):
        """Initialize a BimodalStructure with model constraints.
        
        Args:
            model_constraints (ModelConstraints): Constraints for model generation
            max_time (int): Maximum solving time in seconds
        """
        # Explicitly reset any Z3 resources before initializing
        import gc
        gc.collect()

        # Initialize parent class first
        super().__init__(model_constraints, max_time)

        # We don't want to reset semantics again here as it would 
        # remove necessary attributes already defined in __init__

        # Initialize temporal and world attributes
        self.M = self.semantics.M
        # Update time range to be centered around 0: [-M+1, M-1]
        self.all_times = range(-self.M + 1, self.M)
        
        # Initialize world_id based dictionaries
        self.world_arrays = {}  # Maps world_id (int) to world array (Z3 object)
        self.world_histories = {}  # Maps world_id (int) to {time: world_state} mappings
        self.time_shift_relations = {}  # Maps source_id to {shift: target_id}
        self.main_world = 0  # Default main world_id
        
        # Initialize Z3 model values
        self.z3_main_time = None
        self.z3_main_world_state = None
        # Initialize main_time with a default value (0) to avoid AttributeError
        self.main_time = 0
        
        # Force another garbage collection to ensure no Z3 resources leak
        gc.collect()

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            # Give semantics a reference to this model structure for helper methods
            self.semantics.model_structure = self
            
            # Extract all world histories, arrays, and time-shift relations from the model
            self.world_histories, self.main_world_history, self.world_arrays, self.time_shift_relations = (
                self.semantics.extract_model_elements(self.z3_model)
            )
            
            # Get the main time and world
            self.z3_main_time = self.z3_model.evaluate(self.main_point["time"])
            
            # Convert Z3 time to Python int for easier handling in other places
            if hasattr(self.z3_main_time, 'as_long'):
                self.main_time = self.z3_main_time.as_long()
            else:
                # If not convertible, keep the Z3 value
                self.main_time = self.z3_main_time
            
            # Update the main point to use consistent keys with world as ID
            self.main_point = {
                "time": self.main_time,
                "world": self.main_world  # Use world_id (integer)
            }
            
            # Get the main world state if available
            if self.main_world in self.world_arrays:
                # Evaluate the world state of the main world at the main time
                main_world_array = self.world_arrays[self.main_world]
                
                try:
                    # Use the original Z3 time value directly - not the converted int
                    self.z3_main_world_state = self.semantics.safe_select(
                        self.z3_model, 
                        main_world_array,
                        self.z3_main_time  # Use original Z3 time value
                    )
                except (TypeError, z3.Z3Exception) as e:
                    # Fail with a clear error message
                    error_msg = (f"Failed to extract main world state at time {self.main_time}. "
                              f"This indicates a fundamental model access issue: {str(e)}")
                    raise ValueError(error_msg) from e
            else:
                # TODO: make fail-fast with error report
                # Set a placeholder value
                self.z3_main_world_state = None
            
            # Initialize the all_true and all_false dictionaries in the semantics
            # These provide truth values for extremal operators (Top/Bot)
            self.semantics.all_true = {}
            self.semantics.all_false = {}
            
            for world_id in self.world_arrays:
                self.semantics.all_true[world_id] = (list(self.all_times), [])
                self.semantics.all_false[world_id] = ([], list(self.all_times))
    
    def get_world_array(self, world_id):
        """Get the world array for a given world_id.
        
        Args:
            world_id (int): The world identifier
            
        Returns:
            Z3 Array: The world array mapping times to world states
            
        Raises:
            KeyError: If the world_id doesn't exist in world_arrays
        """
        # Direct dictionary access - will raise KeyError if the world_id doesn't exist
        return self.world_arrays[world_id]
    
    def get_world_history(self, world_id):
        """Get the time-to-state mapping for a given world_id.
        
        Args:
            world_id (int): The world identifier (integer)
            
        Returns:
            dict: Mapping from time points to world states
            
        Raises:
            KeyError: If the world_id doesn't exist in world_histories
            TypeError: If world_id is not an integer
        """
        if not isinstance(world_id, int):
            raise TypeError(f"world_id must be an integer, not {type(world_id)}")
            
        # Direct dictionary access - will raise KeyError if the world_id doesn't exist
        return self.world_histories[world_id]
    
    def get_world_state_at(self, world_id, time):
        """Get the world state at a specific time in a specific world.
        
        Args:
            world_id (int): The world identifier (integer)
            time (int): The time point
            
        Returns:
            Z3 BitVec: The world state at the specified time
            
        Raises:
            KeyError: If the world_id doesn't exist in world_histories
            KeyError: If the time doesn't exist in the history for world_id
            TypeError: If world_id is not an integer
        """
        history = self.get_world_history(world_id)
        return history[time]

    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and time information.
        
        Displays the main world timeline, current evaluation time, and 
        the current world state at that time.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
        if self.z3_model is None:
            raise ValueError(f"Cannot print_evaluation when z3_model is None.")

        BLUE = ""
        RESET = ""
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        if self.z3_main_world_state is None:
            print("No evaluation world state available - no valid model found\n", file=output)
            return

        # Get the main world history for display
        main_world_history = self.world_histories[self.main_world]

        # Create the sequence of states connected by duration-annotated arrows
        sorted_times = sorted(main_world_history.keys())
        parts = []
        for i, time in enumerate(sorted_times):
            parts.append(str(main_world_history[time]))
            if i < len(sorted_times) - 1:
                dur = sorted_times[i + 1] - time
                parts.append(f" ⟹{self._to_subscript(dur)} ")
        world_line = "".join(parts)

        # Get evaluation time and state
        eval_time = self.main_time
        eval_world_state = self.z3_main_world_state
        
        print(
            f"\nEvaluation Point:\n"
            + f"  {BLUE}World History W_{self.main_world}: {world_line}{RESET}\n"
            + f"  {BLUE}Time: {eval_time}{RESET}\n"
            + f"  {BLUE}World State: {bitvec_to_worldstate(eval_world_state)}{RESET}\n",
            file=output,
        )

    @staticmethod
    def _to_subscript(n):
        """Convert an integer to Unicode subscript characters."""
        sub = {'0': '₀', '1': '₁', '2': '₂', '3': '₃', '4': '₄',
               '5': '₅', '6': '₆', '7': '₇', '8': '₈', '9': '₉', '-': '₋'}
        return ''.join(sub.get(c, c) for c in str(n))

    def format_time(self, time):
        """Format time with appropriate sign for display.

        Args:
            time: Time point to format

        Returns:
            str: Formatted time string with sign prefix
        """
        if time > 0:
            return f"+{time}"  # Add + prefix for positive non-zero times
        return f"{time}"  # Negative times already have - prefix, zero is just 0
    
    def _get_time_range(self, world_histories):
        """Get the minimum and maximum time points across all world histories.
        
        Args:
            world_histories: Dictionary mapping world_ids to time-state mappings
            
        Returns:
            tuple: (min_time, max_time)
        """
        min_time = float('inf')
        max_time = float('-inf')
        for world_id, time_states in world_histories.items():
            for time in time_states:
                min_time = min(min_time, time)
                max_time = max(max_time, time)
        return min_time, max_time
    
    def _create_formatted_states(self, world_histories, all_times):
        """Format states for each world at each time.
        
        Args:
            world_histories: Dictionary mapping world_ids to time-state mappings
            all_times: List of all time points to consider
            
        Returns:
            dict: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
        """
        formatted_states = {}
        for world_id, time_states in world_histories.items():
            formatted_states[world_id] = {}
            for time in all_times:
                if time in time_states:
                    # Format time with appropriate sign
                    formatted_time = self.format_time(time)
                    # Create formatted state string
                    formatted_states[world_id][time] = f"({formatted_time}:{time_states[time]})"
        return formatted_states
    
    def _calculate_column_widths(self, all_times, formatted_states):
        """Calculate the maximum width needed for each time column.
        
        Args:
            all_times: List of all time points to consider
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            
        Returns:
            dict: Dictionary mapping time points to column widths
        """
        column_widths = {}
        for time in all_times:
            max_width = 0
            for world_id in formatted_states:
                if time in formatted_states[world_id]:
                    max_width = max(max_width, len(formatted_states[world_id][time]))
            column_widths[time] = max_width
        return column_widths
    
    def _create_time_positions(self, all_times, column_widths):
        """Calculate starting position for each time column.
        
        Args:
            all_times: List of all time points to consider
            column_widths: Dictionary mapping time points to column widths
            
        Returns:
            dict: Dictionary mapping time points to their starting positions
        """
        time_positions = {}
        current_pos = 0
        for time in all_times:
            time_positions[time] = current_pos
            current_pos += column_widths[time] + 4  # Width + space for " ==> "
        return time_positions
    
    def _create_world_line(self, world_id, all_times, formatted_states, time_positions, column_widths):
        """Create a formatted line for a world history with proper alignment.
        
        Args:
            world_id: The world ID to create a line for
            all_times: List of all time points to consider
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            time_positions: Dictionary mapping time points to their starting positions
            column_widths: Dictionary mapping time points to column widths
            
        Returns:
            str: Formatted world line with properly aligned states
        """
        # Initialize the line with spaces
        total_width = max(time_positions.values()) + column_widths.get(all_times[-1], 0)
        line = [" "] * total_width
        
        # Add each visible state at its appropriate position
        visible_times = sorted([t for t in all_times if t in formatted_states[world_id]])
        
        for i, time in enumerate(visible_times):
            state_str = formatted_states[world_id][time]
            pos = time_positions[time]
            
            # Add the state
            for j, char in enumerate(state_str):
                if pos + j < len(line):
                    line[pos + j] = char
            
            # Add arrow with duration subscript if not the last state
            if i < len(visible_times) - 1:
                arrow_pos = pos + len(state_str)
                dur = visible_times[i + 1] - time
                arrow = f" ⟹{self._to_subscript(dur)} "
                for j, char in enumerate(arrow):
                    if arrow_pos + j < len(line):
                        line[arrow_pos + j] = char
        
        # Convert to string and remove trailing whitespace
        return "".join(line).rstrip()
        
    def print_world_histories(self, output=sys.__stdout__):
        """Print all world histories with time-aligned columns.
        
        This method prints world histories in a format where states at the same
        time points are vertically aligned, making it easier to compare states
        across different world histories.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
        print("World Histories:", file=output)
        if self.z3_model is None or not hasattr(self, 'world_histories') or self.world_histories is None:
            print("No valid world histories available", file=output)
            return

        # Set up colors
        GRAY = ""
        RESET = ""
        if output is sys.__stdout__:
            GRAY = "\033[37m"
            RESET = "\033[0m"
        
        # 1. Determine the full time range
        min_time, max_time = self._get_time_range(self.world_histories)
        
        # 2. Create a list of all times in ascending order
        all_times = sorted(range(int(min_time), int(max_time) + 1))
        
        # 3. Format states for each world at each time
        formatted_states = self._create_formatted_states(self.world_histories, all_times)
        
        # 4. Determine column width for each time
        column_widths = self._calculate_column_widths(all_times, formatted_states)
        
        # 5. Calculate starting position for each time column
        time_positions = self._create_time_positions(all_times, column_widths)
        
        # 6. Print each world history with aligned columns
        for world_id in sorted(self.world_histories.keys()):
            # Create the world line with proper alignment
            world_line = self._create_world_line(
                world_id, all_times, formatted_states, time_positions, column_widths
            )
            
            # Print the formatted world line
            print(f"  {GRAY}W_{world_id}: {world_line}{RESET}", file=output)
        
    def _calculate_world_column_widths(self, world_ids, formatted_states, all_times):
        """Calculate the maximum width needed for each world's column.
        
        Args:
            world_ids: List of world IDs
            formatted_states: Dictionary mapping world_ids to dictionaries mapping times to formatted state strings
            all_times: List of all time points to consider
            
        Returns:
            dict: Dictionary mapping world_ids to column widths
        """
        world_column_widths = {}
        for world_id in world_ids:
            max_width = 0
            for time in all_times:
                if time in formatted_states.get(world_id, {}):
                    max_width = max(max_width, len(formatted_states[world_id][time]))
            world_column_widths[world_id] = max_width
        return world_column_widths
        
    def print_world_histories_vertical(self, output=sys.__stdout__):
        """Print world histories with time flowing vertically (top to bottom).
        
        This method arranges world histories in columns with time flowing from top 
        (earlier) to bottom (later), making it easier to visualize temporal evolution.
        
        Args:
            output: Output stream to print to. Defaults to sys.stdout.
        """
        print("World Histories:", file=output)
        if self.z3_model is None or not hasattr(self, 'world_histories') or self.world_histories is None:
            print("No valid world histories available", file=output)
            return

        # Set up colors
        GRAY = ""
        HIGHLIGHT = ""
        RESET = ""
        if output is sys.__stdout__:
            GRAY = "\033[37m"
            HIGHLIGHT = "\033[1;33m"  # Bold yellow for time 0
            RESET = "\033[0m"
        
        # Find time range and world IDs
        min_time, max_time = self._get_time_range(self.world_histories)
        all_times = sorted(range(int(min_time), int(max_time) + 1))
        world_ids = sorted(self.world_histories.keys())
        
        # Create formatted states and determine column widths
        formatted_states = self._create_formatted_states(self.world_histories, all_times)
        
        # Calculate maximum width needed for each world column
        column_widths = {}
        for world_id in world_ids:
            max_width = 0
            for time in all_times:
                if time in formatted_states.get(world_id, {}):
                    state_width = len(formatted_states[world_id][time])
                    max_width = max(max_width, state_width)
            column_widths[world_id] = max_width
        
        # Fixed width for the Time column (reduced for compactness)
        time_col_width = 6  # Reduced from 10
        
        # Calculate positions for each column separator to ensure alignment
        separator_positions = [time_col_width]  # Start after the time column
        for world_id in world_ids[:-1]:  # No separator needed after the last column
            separator_positions.append(
                separator_positions[-1] + column_widths[world_id] + 3  # +3 for " | "
            )
        
        # Create the header row
        header = "Time".ljust(time_col_width)
        for i, world_id in enumerate(world_ids):
            # Add separator if not the first column
            header += " | "
            # Add world ID with proper padding
            header += f"W_{world_id}".ljust(column_widths[world_id])
        
        print(f"  {GRAY}{header}{RESET}", file=output)
        
        # Create a separator line matching the header length with pipe characters
        separator_parts = ["=" * time_col_width]
        for world_id in world_ids:
            separator_parts.append("=|=" + "=" * column_widths[world_id])
            
        separator = "".join(separator_parts)
        print(f"  {GRAY}{separator}{RESET}", file=output)
        
        # Print each time row
        for time in all_times:
            # Format time with appropriate sign
            formatted_time = self.format_time(time)
            
            # Use highlighting for time 0
            time_prefix = HIGHLIGHT if time == 0 else GRAY
            
            # Start the row with the time column
            row_parts = [f"{formatted_time.ljust(time_col_width)}"]
            
            # Add each world's state at this time
            for world_id in world_ids:
                if time in formatted_states.get(world_id, {}):
                    # Get the state and pad it to match the column width
                    state = formatted_states[world_id][time]
                    padded_state = state.ljust(column_widths[world_id])
                else:
                    # Empty placeholder for missing state
                    padded_state = "".ljust(column_widths[world_id])
                
                # Add the separator and the padded state
                row_parts.append(" | " + padded_state)
            
            # Combine all parts and print
            row = "".join(row_parts)
            print(f"  {time_prefix}{row}{RESET}", file=output)
            
            # Add arrow between rows (except after the last time)
            if time < max_time:
                arrow_parts = [" " * time_col_width]  # Space for time column using updated width
                
                for i, world_id in enumerate(world_ids):
                    # Calculate position for the arrow in this column
                    arrow_position = (column_widths[world_id] - 1) // 2
                    
                    # Only show arrow if this world has a state at this time AND the next time
                    if (time in formatted_states.get(world_id, {}) and 
                        time + 1 in formatted_states.get(world_id, {})):
                        # Create a string with pipe, spaces and an arrow at the calculated position
                        arrow_str = " | "  # Keep the pipe separator
                        arrow_str += " " * arrow_position + "↓" + " " * (column_widths[world_id] - arrow_position - 1)
                    else:
                        # Keep the pipe separator but no arrow
                        arrow_str = " | " + " " * column_widths[world_id]
                    
                    arrow_parts.append(arrow_str)
                
                arrow_row = "".join(arrow_parts)
                print(f"  {GRAY}{arrow_row}{RESET}", file=output)
    
    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print complete model information including worlds, evaluation point, and sentences.
        
        Args:
            default_settings: Default settings for the model
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            output: Output stream to print to. Defaults to sys.stdout.
        """
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            # Choose the appropriate history display format based on settings
            align_vertically = self.settings.get("align_vertically", False)
            if align_vertically:
                self.print_world_histories_vertical(output)
            else:
                self.print_world_histories(output)
                
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
            # Always print closing separator for countermodels
            print(f"\n{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print all model elements to the provided output stream.
        
        Args:
            default_settings: Default settings for the model
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            print_constraints: Whether to print constraints. Defaults to value in settings.
            output: Output stream to print to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
            
        # Check if we actually timed out (runtime >= max_time)
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime >= self.max_time
        
        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
        
        self.print_all(self.settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(self, example_name, theory_name, include_constraints, output):
        """Save all model elements to the provided output file.
        
        Args:
            example_name: Name of the example being evaluated
            theory_name: Name of the theory being used
            include_constraints: Whether to include constraints in the output
            output: Output file to save to
        """
        constraints = self.model_constraints.all_constraints
        self.print_all(example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
    
    def extract_states(self):
        """Extract categorized states for output.
        
        In bimodal logic, all states are world states (no possible/impossible distinction).
        
        Returns:
            Dict with keys 'worlds', 'possible', 'impossible'
        """
        states = {"worlds": [], "possible": [], "impossible": []}
        
        if hasattr(self, 'world_histories') and self.world_histories:
            for world_id in self.world_histories:
                states["worlds"].append(f"s{world_id}")
        
        return states
    
    def extract_evaluation_world(self):
        """Extract the main evaluation world.
        
        Returns:
            State name (e.g., 's3') or None if not set
        """
        if hasattr(self, 'main_world') and self.main_world is not None:
            return f"s{self.main_world}"
        return None
    
    def extract_relations(self):
        """Extract time shift relations between worlds.
        
        Returns:
            Dict containing time_shift relations
        """
        relations = {}
        
        if hasattr(self, 'time_shift_relations') and self.time_shift_relations:
            relations['time_shift'] = {}
            for source, shifts in self.time_shift_relations.items():
                source_name = f"s{source}"
                relations['time_shift'][source_name] = {}
                for shift, target in shifts.items():
                    relations['time_shift'][source_name][str(shift)] = f"s{target}"
        
        return relations
    
    def extract_propositions(self):
        """Extract proposition truth values at worlds.
        
        Returns:
            Dict mapping propositions to their truth values at each world
        """
        propositions = {}
        
        if not hasattr(self, 'syntax') or not hasattr(self.syntax, 'propositions'):
            return propositions
        
        # Get all worlds
        worlds = []
        if hasattr(self, 'world_histories'):
            worlds = list(self.world_histories.keys())
        
        # Extract truth values for each proposition
        for prop_name, prop_obj in self.syntax.propositions.items():
            if hasattr(prop_obj, 'letter'):
                letter = prop_obj.letter
                propositions[letter] = {}
                
                for world in worlds:
                    world_name = f"s{world}"
                    if hasattr(prop_obj, 'evaluate_at'):
                        try:
                            # Evaluate at time 0 by default
                            propositions[letter][world_name] = prop_obj.evaluate_at(world, 0)
                        except:
                            # If evaluation fails, skip this world
                            pass
        
        return propositions
    
    def print_model_differences(self, output=sys.stdout):
        """Print differences from previous model using bimodal theory semantics.
        
        Args:
            output: Output stream for printing
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return
            
        diffs = self.model_differences
        
        # Skip if all difference categories are empty
        if not any([
            diffs.get('world_histories'),
            diffs.get('truth_conditions'),
            diffs.get('task_relations'),
            diffs.get('time_intervals'),
            diffs.get('time_shifts')
        ]):
            return
        
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # 1. Print world history changes
        if 'world_histories' in diffs and diffs['world_histories']:
            print("World History Changes:", file=output)
            
            for world_id, changes in diffs['world_histories'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    # New world added
                    print(f"  + World W_{world_id} added", file=output)
                    history = changes.get('history', {})
                    
                    time_states = []
                    for time, state in sorted(history.items()):
                        time_states.append(f"({time}:{state})")
                    
                    if time_states:
                        print(f"    History: {' -> '.join(time_states)}", file=output)
                
                elif isinstance(changes, dict) and changes.get('removed', False):
                    # World removed
                    print(f"  - World W_{world_id} removed", file=output)
                
                else:
                    # World changed
                    print(f"  World W_{world_id} changed:", file=output)
                    
                    for time, change in sorted(changes.items()):
                        if isinstance(change, dict):
                            old_state = change.get('old')
                            new_state = change.get('new')
                            
                            if old_state is None:
                                # Time point added
                                print(f"    + Time {time}: {new_state}", file=output)
                            elif new_state is None:
                                # Time point removed
                                print(f"    - Time {time}: {old_state}", file=output)
                            else:
                                # State changed at this time
                                print(f"    Time {time}: {old_state} -> {new_state}", file=output)
        
        # 2. Print truth condition changes
        if 'truth_conditions' in diffs and diffs['truth_conditions']:
            print("\nTruth Condition Changes:", file=output)
            
            for letter, changes in diffs['truth_conditions'].items():
                print(f"  Letter {letter}:", file=output)
                
                for state, change in changes.items():
                    old_value = change.get('old', False)
                    new_value = change.get('new', False)
                    
                    print(f"    State {state}: {old_value} -> {new_value}", file=output)
        
        # 3. Print task relation changes (with duration parameter)
        # Format: "state1--[duration]-->state2" where duration is explicit
        if 'task_relations' in diffs and diffs['task_relations']:
            print("\nTask Relation Changes:", file=output)

            for transition, change in diffs['task_relations'].items():
                old_value = change.get('old', False)
                new_value = change.get('new', False)

                status = "added" if new_value and not old_value else "removed" if old_value and not new_value else "changed"
                print(f"  TaskRel {transition}: {status}", file=output)
        
        # 4. Print time interval changes
        if 'time_intervals' in diffs and diffs['time_intervals']:
            print("\nTime Interval Changes:", file=output)
            
            for world_id, change in diffs['time_intervals'].items():
                old_interval = change.get('old')
                new_interval = change.get('new')
                
                if old_interval is None:
                    print(f"  + World W_{world_id} interval: {new_interval}", file=output)
                elif new_interval is None:
                    print(f"  - World W_{world_id} interval: {old_interval}", file=output)
                else:
                    print(f"  World W_{world_id} interval: {old_interval} -> {new_interval}", file=output)
        
        # 5. Print time shift relation changes
        if 'time_shifts' in diffs and diffs['time_shifts']:
            print("\nTime Shift Relation Changes:", file=output)
            
            for world_id, changes in diffs['time_shifts'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    # New world added
                    print(f"  + Time shifts for World W_{world_id} added", file=output)
                    shifts = changes.get('shifts', {})
                    
                    for shift, target in sorted(shifts.items()):
                        print(f"    Shift {shift}: -> W_{target}", file=output)
                
                elif isinstance(changes, dict) and changes.get('removed', False):
                    # World removed
                    print(f"  - Time shifts for World W_{world_id} removed", file=output)
                
                else:
                    # Shifts changed
                    print(f"  Time shifts for World W_{world_id} changed:", file=output)
                    
                    for shift, change in sorted(changes.items()):
                        if isinstance(change, dict):
                            old_target = change.get('old')
                            new_target = change.get('new')
                            
                            if old_target is None:
                                # Shift added
                                print(f"    + Shift {shift}: -> W_{new_target}", file=output)
                            elif new_target is None:
                                # Shift removed
                                print(f"    - Shift {shift}: -> W_{old_target}", file=output)
                            else:
                                # Target changed
                                print(f"    Shift {shift}: W_{old_target} -> W_{new_target}", file=output)
