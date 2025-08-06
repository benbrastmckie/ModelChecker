# Implementation Plan: Batch Mode Output Enhancement via Dynamic Data Extraction

## Overview

This plan implements Option C: Dynamic Data Extraction to enhance batch mode output while maintaining backward compatibility. The approach adds theory-specific data extractors in each theory directory while keeping the output system theory-agnostic.

## Design Philosophy

Following the style guide principles:
- **No decorators** - Use explicit method calls and clear interfaces
- **Theory isolation** - Each theory implements its own data extractor
- **Fail fast** - Let errors occur naturally rather than masking
- **Explicit parameters** - No hidden conversions or implicit state
- **Test-driven development** - Write tests first for each phase

## Architecture

### Core Components

1. **Data Extraction Methods in Model Structures** (in each theory's `semantic.py`)
   - Add extraction methods directly to existing model structure classes
   - BimodalStructure, LogosModelStructure, ExclusionModelStructure, ImpositionModelStructure
   - No separate files needed - integrates with existing output methods

2. **Enhanced ModelDataCollector** (`src/model_checker/output/collectors.py`)
   - Checks if model structure has extraction methods
   - Calls methods directly on model structure instance
   - Falls back to basic extraction for theories without these methods

## Implementation Phases

### Phase 1: Base Infrastructure and Directory Prompt Fix (Day 1)

#### Objective
Fix the batch mode directory prompt and prepare for data extraction enhancements.

#### Tests to Write First
```python
# src/model_checker/output/tests/test_batch_directory_prompt.py
class TestBatchDirectoryPrompt(unittest.TestCase):
    def test_batch_mode_prompts_directory_change(self):
        """Test that batch mode shows directory change prompt."""
        
    def test_interactive_mode_still_prompts(self):
        """Test that interactive mode prompt still works."""
```

#### Implementation Tasks

1. **Fix Directory Prompt for Batch Mode**
```python
# In src/model_checker/builder/module.py around line 1005
# Change the condition to prompt in both modes:
if self.interactive_manager:
    self.interactive_manager.prompt_change_directory(full_path)
else:
    # Also prompt in non-interactive batch mode
    print(f"\nOutput saved to: {full_path}")
    print(f"To change to output directory, run:")
    print(f"  cd {full_path}")
```

#### Success Criteria
- [ ] Base extractor interface defined without decorators
- [ ] Batch mode shows directory change instructions
- [ ] All unit tests pass

### Phase 2: Add Data Extraction Methods to Model Structures (Day 2)

#### Objective
Add data extraction methods directly to each theory's model structure class.

#### Tests to Write First
```python
# src/model_checker/theory_lib/bimodal/tests/test_data_extraction.py
class TestBimodalDataExtraction(unittest.TestCase):
    def test_extract_states(self):
        """Test extraction of world states from bimodal structure."""
        
    def test_extract_time_shift_relations(self):
        """Test extraction of time shift relations."""
        
    def test_extract_propositions(self):
        """Test extraction of proposition values."""

# Similar test files for each theory...
```

#### Implementation Tasks

1. **Add Methods to BimodalStructure**
```python
# In src/model_checker/theory_lib/bimodal/semantic.py, add to BimodalStructure class:
    """Extract data from bimodal model structures."""
    
    def extract_states(self, model_structure) -> Dict[str, List[str]]:
        """Extract world states from bimodal structure."""
        states = {"worlds": [], "possible": [], "impossible": []}
        
        if hasattr(model_structure, 'world_histories'):
            for world_id in model_structure.world_histories:
                states["worlds"].append(f"s{world_id}")
                
        return states
    
    def extract_evaluation_world(self, model_structure) -> Optional[str]:
        """Extract main world from bimodal structure."""
        if hasattr(model_structure, 'main_world') and model_structure.main_world is not None:
            return f"s{model_structure.main_world}"
        return None
    
    def extract_relations(self, model_structure) -> Dict[str, Any]:
        """Extract time shift relations."""
        relations = {}
        
        if hasattr(model_structure, 'time_shift_relations'):
            relations['time_shift'] = {}
            for source, shifts in model_structure.time_shift_relations.items():
                source_name = f"s{source}"
                relations['time_shift'][source_name] = {}
                for shift, target in shifts.items():
                    relations['time_shift'][source_name][str(shift)] = f"s{target}"
                    
        return relations
    
    def extract_propositions(self, model_structure) -> Dict[str, Dict[str, bool]]:
        """Extract proposition values at worlds."""
        propositions = {}
        
        if hasattr(model_structure, 'syntax') and hasattr(model_structure.syntax, 'propositions'):
            # Get world list
            worlds = []
            if hasattr(model_structure, 'world_histories'):
                worlds = list(model_structure.world_histories.keys())
            
            # Extract truth values
            for prop_name, prop_obj in model_structure.syntax.propositions.items():
                if hasattr(prop_obj, 'letter'):
                    letter = prop_obj.letter
                    propositions[letter] = {}
                    
                    for world in worlds:
                        world_name = f"s{world}"
                        if hasattr(prop_obj, 'evaluate_at'):
                            try:
                                propositions[letter][world_name] = prop_obj.evaluate_at(world)
                            except:
                                # If evaluation fails, skip this world
                                pass
                                
        return propositions
    
    def extract_formatted_output(self, model_structure) -> str:
        """Extract the print output from the model."""
        # This will be captured during the print_to() call
        return ""
```

2. **Logos Data Extractor**
```python
# src/model_checker/theory_lib/logos/data_extractor.py
from model_checker.output.base_extractor import ModelDataExtractor
from typing import Dict, Any, List, Optional

class LogosDataExtractor(ModelDataExtractor):
    """Extract data from logos model structures."""
    
    def extract_states(self, model_structure) -> Dict[str, List[str]]:
        """Extract states with possible/impossible classification."""
        states = {"worlds": [], "possible": [], "impossible": []}
        
        if hasattr(model_structure, 'N_states'):
            for state in model_structure.N_states:
                state_name = f"s{state}"
                
                # Check state type
                if hasattr(model_structure, 'is_null_state') and model_structure.is_null_state(state):
                    states["impossible"].append(state_name)
                elif hasattr(model_structure, 'is_world_state') and model_structure.is_world_state(state):
                    states["worlds"].append(state_name)
                else:
                    states["possible"].append(state_name)
                    
        return states
    
    # ... implement other methods similarly
```

3. **Register Extractors in __init__.py**
```python
# In each theory's __init__.py, add:
from .data_extractor import BimodalDataExtractor  # or appropriate class
DATA_EXTRACTOR = BimodalDataExtractor
```

#### Success Criteria
- [ ] Each theory has a data extractor implementation
- [ ] Extractors handle missing attributes gracefully
- [ ] Theory-specific tests pass

### Phase 3: Enhanced ModelDataCollector (Day 3)

#### Objective
Update ModelDataCollector to use theory-specific extractors dynamically.

#### Tests to Write First
```python
# src/model_checker/output/tests/test_enhanced_collector.py
class TestEnhancedCollector(unittest.TestCase):
    def test_loads_theory_extractor(self):
        """Test dynamic loading of theory extractors."""
        
    def test_fallback_for_unknown_theory(self):
        """Test graceful fallback when no extractor found."""
        
    def test_includes_captured_output(self):
        """Test that captured print output is included."""
```

#### Implementation Tasks

1. **Update ModelDataCollector**
```python
# src/model_checker/output/collectors.py
import importlib
from typing import Dict, Any, Optional
from .base_extractor import ModelDataExtractor

class ModelDataCollector:
    """Collects and structures model data for export."""
    
    def __init__(self):
        self._extractor_cache = {}
    
    def _get_theory_extractor(self, theory_name: str) -> Optional[ModelDataExtractor]:
        """Dynamically load theory-specific data extractor.
        
        Args:
            theory_name: Name of the theory (e.g., 'bimodal', 'logos')
            
        Returns:
            Extractor instance or None if not found
        """
        if theory_name in self._extractor_cache:
            return self._extractor_cache[theory_name]
        
        try:
            # Convert theory name to module path
            theory_lower = theory_name.lower()
            module_path = f"model_checker.theory_lib.{theory_lower}"
            
            # Import the theory module
            theory_module = importlib.import_module(module_path)
            
            # Get the extractor class
            if hasattr(theory_module, 'DATA_EXTRACTOR'):
                extractor_class = theory_module.DATA_EXTRACTOR
                extractor = extractor_class()
                self._extractor_cache[theory_name] = extractor
                return extractor
                
        except (ImportError, AttributeError):
            # Theory doesn't have an extractor
            pass
            
        return None
    
    def collect_model_data(self, model_structure, example_name: str, 
                          theory_name: str, captured_output: str = "") -> Dict[str, Any]:
        """Extract model data using theory-specific extractor.
        
        Args:
            model_structure: The model structure object
            example_name: Name of the example
            theory_name: Name of the theory
            captured_output: Captured print output (optional)
            
        Returns:
            Dictionary containing all model data
        """
        # Get basic info
        has_model = getattr(model_structure, 'z3_model_status', False)
        
        if not has_model:
            return self._empty_model_data(example_name, theory_name)
        
        # Try to get theory-specific extractor
        extractor = self._get_theory_extractor(theory_name)
        
        if extractor:
            # Use theory-specific extraction
            return {
                "example": example_name,
                "theory": theory_name,
                "has_model": True,
                "evaluation_world": extractor.extract_evaluation_world(model_structure),
                "states": extractor.extract_states(model_structure),
                "relations": extractor.extract_relations(model_structure),
                "propositions": extractor.extract_propositions(model_structure),
                "formatted_output": captured_output or extractor.extract_formatted_output(model_structure)
            }
        else:
            # Fallback to basic extraction
            return self._basic_extraction(model_structure, example_name, theory_name, captured_output)
    
    def _empty_model_data(self, example_name: str, theory_name: str) -> Dict[str, Any]:
        """Return empty data structure for no model case."""
        return {
            "example": example_name,
            "theory": theory_name,
            "has_model": False,
            "evaluation_world": None,
            "states": {"possible": [], "impossible": [], "worlds": []},
            "relations": {},
            "propositions": {},
            "formatted_output": ""
        }
    
    def _basic_extraction(self, model_structure, example_name: str, 
                         theory_name: str, captured_output: str) -> Dict[str, Any]:
        """Basic fallback extraction for theories without extractors."""
        # Try to extract what we can generically
        evaluation_world = None
        if hasattr(model_structure, 'z3_main_world') and model_structure.z3_main_world:
            if hasattr(model_structure.z3_main_world, 'as_long'):
                evaluation_world = f"s{model_structure.z3_main_world.as_long()}"
        
        return {
            "example": example_name,
            "theory": theory_name,
            "has_model": True,
            "evaluation_world": evaluation_world,
            "states": {"possible": [], "impossible": [], "worlds": []},
            "relations": {},
            "propositions": {},
            "formatted_output": captured_output
        }
```

2. **Update _capture_and_save_output to pass captured output**
```python
# In src/model_checker/builder/module.py
def _capture_and_save_output(self, example, example_name, theory_name, model_num=None):
    # ... existing capture code ...
    
    # Collect model data with captured output
    collector = ModelDataCollector()
    model_data = collector.collect_model_data(
        example.model_structure,
        example_name,
        theory_name,
        captured_output=converted_output  # Pass the captured output
    )
```

#### Success Criteria
- [ ] Collector dynamically loads theory extractors
- [ ] Fallback works for theories without extractors
- [ ] Captured output included in model data

### Phase 4: Enhanced Markdown Formatting (Day 3 continued)

#### Objective
Update MarkdownFormatter to include the captured model output.

#### Tests to Write First
```python
# src/model_checker/output/tests/test_enhanced_markdown.py
class TestEnhancedMarkdown(unittest.TestCase):
    def test_includes_formatted_output(self):
        """Test that formatted output is included in markdown."""
        
    def test_output_section_formatting(self):
        """Test proper formatting of output section."""
```

#### Implementation Tasks

1. **Update MarkdownFormatter**
```python
# In src/model_checker/output/formatters.py
def format_example(self, example_data: Dict[str, Any], 
                  model_output: str = None) -> str:
    """Format complete example with markdown."""
    sections = []
    
    # ... existing header and data sections ...
    
    # Add formatted output section if available
    output_to_use = example_data.get("formatted_output") or model_output
    if output_to_use:
        sections.append(self._format_output(output_to_use))
        
    return "\n".join(sections)

def _format_output(self, model_output: str) -> str:
    """Format the model output section.
    
    Args:
        model_output: Raw or formatted model output
        
    Returns:
        Formatted markdown section
    """
    if not model_output or not model_output.strip():
        return ""
    
    return f"""
### Model Output

```
{model_output}
```
"""
```

#### Success Criteria
- [ ] Markdown files include model output
- [ ] Output properly formatted in code blocks
- [ ] Empty output handled gracefully

### Phase 5: Integration Testing (Day 4)

#### Objective
Comprehensive testing of the complete system.

#### Tests to Write
```python
# tests/test_batch_output_integration.py
class TestBatchOutputIntegration(unittest.TestCase):
    def test_bimodal_batch_output(self):
        """Test complete batch output for bimodal theory."""
        
    def test_logos_batch_output(self):
        """Test complete batch output for logos theory."""
        
    def test_directory_prompt_batch_mode(self):
        """Test directory navigation prompt in batch mode."""
        
    def test_json_data_completeness(self):
        """Test JSON files contain expected data."""
        
    def test_markdown_formatting_quality(self):
        """Test markdown files are properly formatted."""
```

#### Success Criteria
- [ ] All theories produce complete output
- [ ] Directory prompt appears in batch mode
- [ ] JSON contains extracted model data
- [ ] Markdown includes formatted output
- [ ] No regression in existing functionality

## Testing Strategy

Following TDD principles from the style guide:

1. **Write tests first** for each component
2. **Test in isolation** before integration
3. **Use descriptive test names** that explain what is tested
4. **Include docstrings** explaining the test purpose
5. **Test edge cases** like missing attributes, empty data

## Risk Mitigation

1. **Theory compatibility**: Test with all existing theories
2. **Performance impact**: Benchmark before/after implementation
3. **Backward compatibility**: Ensure existing features still work
4. **Error handling**: Graceful degradation for missing extractors

## Success Metrics

1. Batch mode users get directory change instructions
2. JSON files contain meaningful model data for all theories
3. Markdown files include the formatted model output
4. New theories can add extractors without modifying core code
5. All existing tests continue to pass

## Documentation Updates

1. Update each theory's README with data extractor documentation
2. Update output/README.md with new architecture
3. Add examples of creating new theory extractors
4. Update TOOLS.md with enhanced batch mode features

## TODOs

- [x] The json files produced by the '-s' batch save look good but the markdown document looks crazy. Please fix this.
- [x] I also want to improve the first prompt styling. I want it to ask "Save all examples (a) or run in sequence (s)?" Currently I get: 
    ```consol
    Select save mode:
      1. batch - Save all at end
      2. interactive - Prompt after each model
    Choice (1-2): 
    ```
- [x] If I run the model-checker on an example without save_output=True, I get nice looking colors. However, if I run with save_output=True or the '-s' flag, then it prints to the terminal without colors. I would like to revise this behavior so that it asks before running, "Do you also want to print to the terminal? (y/N)", where if I say yes, I want the printed output to be colored as before if possible. Please think carefully about what is causing this problem before attempting a solution
- [x] For iterating when testing in sequence, I want it to ask "Do you want to find another model? Enter a number to iterate or hit return to continue."
- [x]
