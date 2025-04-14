# Strategy for Aligning World State Columns in BimodalStructure.print_world_histories

## Current Implementation

The current implementation of `print_world_histories` in `BimodalStructure` prints world histories sequentially with time indices and world states in parentheses. Each world history is displayed as a sequence of states connected by arrows, but there is no vertical alignment of states at the same time points.

Current format:
```
World Histories:
  W_0: (0:{a}) ==> (1:{b}) ==> (2:{c})
  W_1: (-1:{x}) ==> (0:{y}) ==> (1:{z})
```

## Proposed Solution

The improved implementation should vertically align world states at the same time point, particularly at time 0, which is the evaluation time. This will make it easier to compare world states across different world histories.

### Key Improvements:

1. **Determine Time Range**: Find the minimum and maximum time points across all world histories.
2. **Pre-compute Column Widths**: For each time point, determine the maximum width required to display any world state at that time.
3. **Format with Fixed-Width Columns**: Format each world history's output with fixed-width columns based on the pre-computed widths.
4. **Align at Time 0**: Ensure special attention to aligning world states at time 0 (the evaluation time).
5. **Add '+' Prefix for Positive Times**: Format positive non-zero times with a '+' prefix to align better with negative times.

## Implementation Strategy

1. **Collect Time Range Information**:
   - Scan all world histories to determine the full time range.
   - Create a map of time points to their maximum state representation widths.

2. **Create Position Map**:
   - Create a map of time points to their positions in the output line.
   - This ensures that states at the same time point appear in the same column.

3. **Format World Histories**:
   - For each world history, create a formatted line with states at their correct positions.
   - Format times with appropriate signs: negative with '-', positive non-zero with '+', zero as '0'.
   - Handle missing time points by leaving spaces.

## Code Structure

```python
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
    min_time = float('inf')
    max_time = float('-inf')
    for world_id, time_states in self.world_histories.items():
        for time in time_states:
            min_time = min(min_time, time)
            max_time = max(max_time, time)
    
    # 2. Create a list of all times in ascending order
    all_times = sorted(range(min_time, max_time + 1))
    
    # 3. Map each time to its position in the output
    # Store formatted states for each world at each time
    formatted_states = {}
    for world_id, time_states in self.world_histories.items():
        formatted_states[world_id] = {}
        for time in all_times:
            if time in time_states:
                # Format time with appropriate sign
                formatted_time = self.format_time(time)
                # Create formatted state string
                formatted_states[world_id][time] = f"({formatted_time}:{time_states[time]})"
    
    # 4. Determine column width for each time
    column_widths = {}
    for time in all_times:
        max_width = 0
        for world_id in formatted_states:
            if time in formatted_states[world_id]:
                max_width = max(max_width, len(formatted_states[world_id][time]))
        column_widths[time] = max_width
    
    # 5. Print each world history with aligned columns
    for world_id in sorted(self.world_histories.keys()):
        line_parts = []
        
        # Handle each time point
        for time in all_times:
            if time in formatted_states[world_id]:
                # Add state with padding to align
                state_str = formatted_states[world_id][time].ljust(column_widths[time])
                line_parts.append(state_str)
            else:
                # Empty space for missing time
                line_parts.append(" " * column_widths[time])
        
        # Join with arrows and print
        arrow = " ==> "
        world_line = arrow.join(line_parts)
        print(f"  {GRAY}W_{world_id}: {world_line}{RESET}", file=output)

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
```

## Expected Output

The improved implementation should produce output similar to:

```
World Histories:
  W_0:              (-1:{p}) ==> (0:{a}) ==> (+1:{b}) ==> (+2:{c})
  W_1: (-2:{w}) ==> (-1:{x}) ==> (0:{y}) ==> (+1:{z})
  W_2:                           (0:{m}) ==> (+1:{n}) ==> (+2:{o})
```

## Considerations

1. **Missing Time Points**: Some world histories might not have states at all time points. The implementation handles this by using empty space of the correct width.

2. **Terminal Width Limitations**: For models with many time points, the output might exceed terminal width. This concern will be addressed in future improvements if needed.

3. **Time Formatting**: Positive non-zero times are displayed with '+' prefix to maintain consistent width with negative times, which helps with alignment.

4. **Arrow Spacing**: The spacing between time columns is kept consistent with the "==>" arrow separator.

## Testing Strategy

To validate the improvement:
1. Test with models having world histories with different time ranges
2. Test with both positive and negative time points
3. Compare with the original implementation to verify correctness
4. Verify proper alignment of time 0 states across all world histories

This aligned display will significantly improve readability when analyzing model structures, especially when comparing world states at the same time point across multiple worlds.

# Vertical Time Display Strategy

## Current Implementation (Post-Horizontal Alignment)

The improved horizontal implementation aligns world states at the same time point vertically, which makes it easier to compare world states across different world histories. However, states are still arranged horizontally within each world history.

Current format (after horizontal alignment improvements):
```
World Histories:
  W_0:              (-1:{p}) ==> (0:{a}) ==> (+1:{b}) ==> (+2:{c})
  W_1: (-2:{w}) ==> (-1:{x}) ==> (0:{y}) ==> (+1:{z})
  W_2:                           (0:{m}) ==> (+1:{n}) ==> (+2:{o})
```

## Proposed Vertical Display

A vertical representation of time would arrange states chronologically from top to bottom, with earlier times (more negative) at the top and later times (more positive) at the bottom. This would make it easier to visualize the temporal evolution of the system.

### Key Improvements:

1. **Vertical Time Representation**: Display time as flowing from top to bottom rather than left to right.
2. **Horizontal World Alignment**: Each column represents one world history.
3. **Evaluation Time Highlight**: Ensure the evaluation time (time 0) is prominently displayed or highlighted.
4. **Consistent Row Spacing**: Maintain even spacing between time points, even when a world doesn't have a state at a particular time.
5. **Arrow Direction**: Use vertical arrows (↓) to represent the flow of time between states.

## Implementation Strategy

1. **Organize Data by Time Instead of World**:
   - Create a structure that maps each time point to a map of world IDs and their states.
   - This inverses the current data organization to prioritize time.

2. **Print Time Points in Order**:
   - Loop through time points from earliest (most negative) to latest (most positive).
   - For each time point, print a row showing the state of each world at that time.

3. **Handle Missing States**:
   - For worlds that don't have a state at a particular time, show empty space or a placeholder.

4. **Connect States with Vertical Arrows**:
   - Add vertical arrows (↓) between consecutive time rows to show the flow of time.

## Code Structure Overview

```python
def print_world_histories_vertical(self, output=sys.__stdout__):
    """Print world histories with time flowing vertically (top to bottom).
    
    This method arranges world histories in columns with time flowing from top 
    (earlier) to bottom (later), making it easier to visualize temporal evolution.
    
    Args:
        output: Output stream to print to. Defaults to sys.stdout.
    """
    print("World Histories (Time Flows ↓):", file=output)
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
    all_times = sorted(range(min_time, max_time + 1))
    world_ids = sorted(self.world_histories.keys())
    
    # Create formatted states and determine column widths
    formatted_states = self._create_formatted_states(self.world_histories, all_times)
    world_column_widths = self._calculate_world_column_widths(world_ids, formatted_states, all_times)
    
    # Print header with world IDs
    header = "Time"
    header = header.ljust(10)  # Fixed width for time column
    for world_id in world_ids:
        header += f" | W_{world_id}".ljust(world_column_widths[world_id] + 3)
    print(f"  {GRAY}{header}{RESET}", file=output)
    print(f"  {GRAY}{'=' * len(header)}{RESET}", file=output)
    
    # Print each time row
    for time in all_times:
        # Format time with appropriate sign
        formatted_time = self.format_time(time)
        
        # Use highlighting for time 0
        time_prefix = HIGHLIGHT if time == 0 else GRAY
        
        # Create the row for this time point
        row = f"{time_prefix}{formatted_time.ljust(10)}{RESET}"
        
        # Add each world's state at this time
        for world_id in world_ids:
            if time in formatted_states.get(world_id, {}):
                state = formatted_states[world_id][time]
                row += f" | {state}".ljust(world_column_widths[world_id] + 3)
            else:
                # Empty placeholder for missing state
                row += f" | ".ljust(world_column_widths[world_id] + 3)
        
        print(f"  {row}", file=output)
        
        # Add arrow between rows (except after the last time)
        if time < max_time:
            arrow_row = " " * 10
            for world_id in world_ids:
                # Only show arrow if this world has a state at this time AND the next time
                if (time in formatted_states.get(world_id, {}) and 
                    time + 1 in formatted_states.get(world_id, {})):
                    arrow_row += f" | {' ' * (world_column_widths[world_id] // 2)}↓"
                else:
                    arrow_row += f" | {' ' * (world_column_widths[world_id] // 2)} "
            print(f"  {GRAY}{arrow_row}{RESET}", file=output)

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
```

## Expected Output

The vertical implementation should produce output similar to:

```
World Histories (Time Flows ↓):
  Time       | W_0        | W_1        | W_2       
  =============================================
  -2         |            | (-2:{w})   |           
             |            | ↓          |           
  -1         | (-1:{p})   | (-1:{x})   |           
             | ↓          | ↓          |           
  0          | (0:{a})    | (0:{y})    | (0:{m})   
             | ↓          | ↓          | ↓         
  +1         | (+1:{b})   | (+1:{z})   | (+1:{n})  
             | ↓          |            | ↓         
  +2         | (+2:{c})   |            | (+2:{o})  
```

## Considerations

1. **Terminal Width**: The vertical format may require more horizontal space to display all worlds side by side.

2. **Visual Clarity**: The vertical flow of time may be more intuitive for visualizing temporal evolution.

3. **Evaluation Time Highlighting**: Time 0 (evaluation time) should be highlighted to make it stand out.

4. **Arrow Visibility**: Ensure arrows are only shown where transitions between states exist.

5. **Flexibility**: Consider making this display an optional alternative to the horizontal format, allowing users to choose their preferred view.

## Implementation Plan

1. **Implement as Separate Method**: Create a new method `print_world_histories_vertical()` rather than replacing the existing `print_world_histories()` method.

2. **Add Command-Line Flag**: Add a flag to choose between horizontal and vertical display formats.

3. **Consider Interactive Navigation**: For very large models with many time points, consider ways to navigate through time points or collapse sections.

This vertical display would complement the existing horizontal display, giving users multiple ways to visualize and analyze world histories in the model checker.

## Current Vertical Implementation Output

Below is the current output of the vertical display implementation:

```
World Histories (Time Flows ↓):
  Time   | W_0    | W_1   
  =======|========|=======
  -1     |        | (-1:b)
         |        |   ↓   
  0      | (0:b)  | (0:a) 
         |   ↓    |       
  +1     | (+1:a) |       
```

## Alternative Display Ideas

Here is the alternative example to explain how the vertical display is to be formatted:

```
World Histories (Time Flows ↓):
  Time   | W_0    | W_1   
  =======|========|=======
   -1    |        | (-1:b)
         |        |   ↓   
    0    | (0:b)  | (0:a) 
         |   ↓    |       
   +1    | (+1:a) |       
```

