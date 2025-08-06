# Feature Research: Batch Mode Output System Enhancement

## Current State Analysis

### Existing Functionality
- **OutputManager**: Handles file creation and directory management
- **ModelDataCollector**: Attempts to extract model data for JSON/Markdown export
- **MarkdownFormatter**: Formats collected data into markdown files
- **InteractiveSaveManager**: Handles user prompts for save decisions

### Integration Points
1. **BuildModule.run_examples()**: Main execution loop that calls output saving
2. **BuildExample._capture_and_save_output()**: Captures print output and collects model data
3. **Theory-specific model structures**: BimodalStructure, LogosStructure, etc.

### Dependencies
- Model structures inherit from ModelDefaults
- Each theory has custom print_to() and print_all() methods
- Output system depends on model structure attributes

### Current Limitations
1. **Directory Navigation**: Batch mode doesn't prompt for directory change
2. **Data Collection Mismatch**: ModelDataCollector expects non-existent methods
3. **Incomplete Output**: Captured model output not included in saved files
4. **Theory-Specific Data**: Each theory stores data differently

## Alternative Approaches

### Approach A: Minimal Fix
**Description**: Quick fixes to address immediate issues without major refactoring

**Implementation**:
- Add directory prompt for batch mode
- Create adapter methods in ModelDataCollector for existing attributes
- Pass captured output to markdown formatter

**Pros**:
- Low risk, minimal code changes
- Quick implementation (1-2 days)
- Preserves existing architecture

**Cons**:
- Doesn't address underlying design issues
- Theory-specific adapters needed
- Technical debt accumulation

### Approach B: Universal Model Interface
**Description**: Define a standard interface that all model structures must implement

**Implementation**:
- Create ModelDataInterface with required methods
- Update all theory model structures to implement interface
- Rewrite ModelDataCollector to use interface

**Pros**:
- Clean, extensible architecture
- Consistent data extraction across theories
- Future-proof for new theories

**Cons**:
- Requires updating all theory implementations
- Breaking changes to existing code
- Extensive testing required (1-2 weeks)

### Approach C: Dynamic Data Extraction (Recommended)
**Description**: Enhance ModelDataCollector to dynamically extract data from existing attributes

**Implementation**:
- Update ModelDataCollector to inspect model structure attributes
- Create theory-aware extraction methods
- Maintain backward compatibility
- Include captured output in markdown files

**Pros**:
- No breaking changes to theories
- Works with existing model structures
- Incremental improvement path
- Moderate implementation time (3-4 days)

**Cons**:
- More complex collector logic
- Need to handle theory variations

## Risk Assessment

### Approach A Risks
- **High Technical Debt**: Quick fixes will need rework later
- **Limited Functionality**: Won't fully solve output quality issues

### Approach B Risks
- **High Breaking Change Risk**: All theories need updates
- **Testing Burden**: Every theory needs comprehensive retesting
- **Timeline Risk**: Could take significantly longer than estimated

### Approach C Risks
- **Moderate Complexity**: Dynamic extraction logic more complex
- **Theory Coverage**: Need to ensure all theories properly handled

## Detailed Analysis of Approach C

### Data Available in Model Structures

#### BimodalStructure
- `world_histories`: Dict mapping world_id to time->state
- `time_shift_relations`: Dict of world relationships
- `world_arrays`: World state arrays
- `syntax.propositions`: Proposition objects with truth values

#### LogosStructure
- Similar to Bimodal plus:
- State type information (possible/impossible)
- Fusion/fission relations
- Null state handling

#### ExclusionStructure
- Witness-based semantics
- State compatibility relations
- Exclusion constraints

### Implementation Strategy for Approach C

1. **Enhanced ModelDataCollector**:
   - Add `_detect_theory_type()` method
   - Create theory-specific extraction methods
   - Fall back to generic extraction for unknown theories

2. **Capture Integration**:
   - Ensure captured output passed to formatter
   - Add option to include/exclude raw output

3. **Batch Mode Enhancement**:
   - Always prompt for directory navigation
   - Unify batch/interactive end behavior

## Recommendation

I recommend **Approach C: Dynamic Data Extraction** because it:
1. Addresses all identified issues
2. Maintains backward compatibility
3. Provides incremental improvement path
4. Balances implementation effort with results
5. Sets foundation for future enhancements

The implementation can be done in phases:
- Phase 1: Fix directory prompt issue (quick win)
- Phase 2: Enhance data collection for existing theories
- Phase 3: Integrate captured output into files
- Phase 4: Optimize and refine output formatting