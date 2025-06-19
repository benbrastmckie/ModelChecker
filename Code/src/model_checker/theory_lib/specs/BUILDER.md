# Builder Module Fix: Generated Project Import Resolution

## Problem Analysis

### Root Cause
When users run `model-checker` without arguments to generate a new project, the system:

1. Uses `logos` theory as the default template 
2. Copies the template structure to create a new project
3. Attempts to run examples from the generated project to demonstrate functionality
4. The BuildModule fails to load modules from the generated project because Python cannot resolve imports

### Error Details
```
ModuleNotFoundError: No module named 'project_SNAKE'
ImportError: Failed to load the module '__init__': No module named 'project_SNAKE'
```

This occurs at `src/model_checker/builder/module.py:135` when executing modules from the generated project.

### Technical Analysis
The issue is in `BuildModule._load_module()` method lines 88-117:
- The method attempts to detect package structure by traversing directories for `__init__.py` files
- Generated projects are standalone directories, not installed Python packages
- Any relative imports (e.g., `from ..semantic import`) require the parent directory to be importable
- Current logic fails to properly add the parent directory to `sys.path` for generated projects
- The system needs to work with any theory structure, not assume specific directory layouts

## Implementation Plan

### Phase 1: Immediate Fix - Structure-Agnostic Module Loading

**File**: `src/model_checker/builder/module.py`
**Method**: `BuildModule._load_module()` (lines 88-117)

#### Design Principles:
- **Structure Agnostic**: Work with any theory structure without assuming specific layouts
- **Import Resolution**: Ensure generated projects can resolve their imports regardless of internal organization
- **Backward Compatibility**: Maintain existing functionality for installed packages and theory_lib modules

#### Changes Required:

1. **Enhanced Path Detection Logic**
   - Always add the parent directory of generated projects to `sys.path`
   - Add the project directory itself to `sys.path` for sibling imports
   - Maintain existing package detection for theory_lib modules

2. **Generated Project Detection**
   - Detect projects by `project_` prefix pattern
   - Apply appropriate import resolution strategy

3. **Improved Error Handling**
   - Update error message at line 144 to provide guidance for generated projects
   - Add diagnostic information about detected project structure

#### Specific Code Changes:

```python
# Around line 88-117 in _load_module()
def _load_module(self):
    try:
        module_dir = os.path.dirname(os.path.abspath(self.module_path))
        
        # Check if this is a generated project
        is_generated_project = self._is_generated_project(module_dir)
        
        if is_generated_project:
            # For generated projects, ensure both project and parent directories are in sys.path
            # This enables both relative imports and sibling module imports
            project_parent = os.path.dirname(module_dir)
            if project_parent not in sys.path:
                sys.path.insert(0, project_parent)
            if module_dir not in sys.path:
                sys.path.insert(0, module_dir)
            
            # Set package context to enable relative imports
            project_name = os.path.basename(module_dir)
            package_name = project_name
        else:
            # Existing package detection logic for theory_lib and installed packages
            package_parts = []
            current_dir = module_dir
            
            while os.path.exists(os.path.join(current_dir, "__init__.py")):
                package_parts.insert(0, os.path.basename(current_dir))
                parent_dir = os.path.dirname(current_dir)
                if parent_dir == current_dir:
                    break
                current_dir = parent_dir
            
            if package_parts:
                package_name = ".".join(package_parts)
                parent_of_package = os.path.dirname(current_dir)
                if parent_of_package not in sys.path:
                    sys.path.insert(0, parent_of_package)
            else:
                package_name = ""
                if module_dir not in sys.path:
                    sys.path.insert(0, module_dir)
        
        # Load the module (rest unchanged)
        spec = importlib.util.spec_from_file_location(
            self.module_name, 
            self.module_path, 
            submodule_search_locations=[module_dir]
        )
        if spec is None or spec.loader is None:
            raise ImportError("Module spec could not be loaded.")
        
        module = importlib.util.module_from_spec(spec)
        
        # Set package attribute for relative imports
        if package_name:
            module.__package__ = package_name
        
        spec.loader.exec_module(module)
        return module
```

4. **Add Helper Method**:
```python
def _is_generated_project(self, module_dir):
    """Detect if module is from a generated project.
    
    Generated projects are identified by the project_ prefix pattern.
    This approach is structure-agnostic and works regardless of 
    internal theory organization.
    """
    project_name = os.path.basename(module_dir)
    return project_name.startswith('project_')
```

### Phase 2: Project Generation Enhancement

**File**: `src/model_checker/builder/project.py`
**Focus**: Ensure consistent examples.py generation

#### Goals:
- Maintain flexibility for theory structures
- Ensure every generated project has a working `examples.py` in the root
- Support the transition from default to logos as primary template

#### Changes:
1. **Post-Generation Validation**
   - Verify generated project has `examples.py` at root level
   - If missing, create a minimal `examples.py` that imports from theory structure

2. **Template Flexibility**
   - Support both file-based (`examples.py`) and directory-based (`examples/`) structures
   - Generate appropriate examples.py regardless of source theory structure

3. **Examples.py Generation**
   - If source theory has `examples.py`: copy directly
   - If source theory has `examples/` directory: create `examples.py` that imports from the directory
   - Ensure examples.py always works for initial project testing

### Phase 3: Comprehensive Testing

#### Test Cases to Add:
1. **Generated Project Import Test**
   - Create test project using logos template
   - Verify `examples.py` loads successfully from generated project
   - Test any relative imports work correctly within generated project

2. **Structure-Agnostic Template Test**
   - Test generation with logos theory (examples.py structure)
   - Test generation with default theory (examples/ directory structure)
   - Test generation with other theory templates
   - Verify all templates produce working projects with functional examples.py

3. **Path Resolution Test**
   - Test projects in various directory structures
   - Verify sys.path modifications work correctly for generated projects
   - Test that existing theory_lib functionality is unaffected
   - Test cleanup of sys.path modifications

4. **Examples.py Functionality Test**
   - Verify generated examples.py contains characteristic examples from source theory
   - Test that examples run successfully after project generation
   - Validate examples provide good demonstration of theory capabilities

#### Test Files:
- `tests/test_generated_project_imports.py`
- `tests/test_structure_agnostic_generation.py`
- `tests/test_module_loading.py`

### Phase 4: Documentation Updates

#### Files to Update:
1. `src/model_checker/builder/README.md`
   - Document the structure-agnostic import resolution fix
   - Explain generated project handling approach
   - Document examples.py requirement for theory templates

2. `ARCHITECTURE.md`
   - Update builder system documentation
   - Document flexible project generation process
   - Clarify theory structure requirements (examples.py at root)

3. `docs/DEVELOPMENT.md`
   - Add troubleshooting section for generated projects
   - Document theory template guidelines
   - Explain the examples.py convention

## Theory Structure Requirements

### Minimal Requirements for Theory Templates:
1. **examples.py** (Required): Must exist at theory root with characteristic examples
2. **Flexible Structure**: No assumptions about directories, submodules, or organization
3. **Import Independence**: Theory should work when copied to generated project

### Examples.py Standards:
- Contains `example_range` dictionary with characteristic examples
- Examples should demonstrate core theory capabilities
- Should be runnable immediately after project generation
- Serves as introduction to the theory for new users

## Implementation Priority

### High Priority (Immediate)
- [x] Root cause analysis
- [x] Phase 1: Structure-agnostic module loading fix (COMPLETED)
- [x] Basic testing with logos and default templates (COMPLETED)

### Medium Priority (Next Release)
- [ ] Phase 2: Project generation enhancements
- [ ] Phase 3: Comprehensive testing
- [ ] Error message improvements

### Low Priority (Future Enhancement)
- [ ] Phase 4: Documentation updates
- [ ] Theory template validation
- [ ] Enhanced project generation options

## Testing Strategy

### Manual Testing Steps:
1. Run `model-checker` without arguments
2. Create new project with default settings (using logos template)
3. Attempt to run `examples.py` from generated project
4. Verify no import errors occur
5. Test with different project names and theory templates
6. Verify examples demonstrate theory capabilities effectively

### Automated Testing:
1. Unit tests for `_load_module()` method with structure-agnostic logic
2. Integration tests for project generation workflow with different theory templates
3. Regression tests for existing theory_lib functionality
4. Examples.py functionality tests

## Risk Assessment

### Low Risk Changes:
- Structure-agnostic path detection (safely extends existing logic)
- Error message improvements
- Documentation updates

### Medium Risk Changes:
- sys.path modifications (could affect other imports, but limited to generated projects)
- Module loading logic changes (affects import resolution)

### Mitigation:
- Generated project detection limits scope of changes
- Existing theory_lib logic preserved unchanged
- Thorough testing with multiple theory templates
- Clear rollback plan

## Success Criteria

1. **Primary**: Generated projects from any theory template load without import errors
2. **Secondary**: Examples.py provides effective introduction to theory capabilities
3. **Tertiary**: Existing theory_lib functionality remains unaffected
4. **Future**: Smooth transition as default theory is phased out in favor of logos

## Implementation Notes

### Design Philosophy Alignment:
- **Fail Fast**: Let genuine import errors surface clearly
- **Root Cause Fix**: Address the import resolution issue directly at the module loading level
- **No Silent Failures**: Maintain clear error reporting
- **Structural Solutions**: Fix the underlying path resolution problem without assuming rigid structures
- **Structure Agnostic**: Support flexible theory organization while maintaining core functionality

### Code Quality Standards:
- Preserve existing error handling patterns
- Maintain backward compatibility for theory_lib modules
- Follow existing code style and conventions
- Add appropriate logging for debugging
- Minimize assumptions about theory internal structure

### Theory Template Guidelines:
- **Required**: `examples.py` at theory root containing characteristic examples
- **Flexible**: No constraints on internal directory structure, submodules, or organization
- **Functional**: Examples should work immediately after project generation
- **Demonstrative**: Examples should showcase theory's key capabilities and distinguish it from other theories

This plan addresses the immediate user issue while supporting the transition to logos as the primary template and maintaining flexibility for diverse theory structures.

## Implementation Progress

### Phase 1: COMPLETED ✅ (Commit: a12c030)

**Status**: Successfully implemented and tested

**Changes Made**:
- Added `_is_generated_project()` method to detect projects by `project_` prefix pattern
- Added `_find_project_directory()` method to locate project root when in subdirectories
- Enhanced `_load_module()` to handle generated projects with proper sys.path configuration
- Improved error messages for generated project import failures
- Maintained backward compatibility with existing theory_lib functionality

**Test Results**:
- ✅ Original error case (examples/__init__.py with relative imports) now works
- ✅ Logos template generation and loading works correctly
- ✅ Default template generation and loading works correctly  
- ✅ Existing theory_lib functionality unaffected
- ✅ All unit tests pass

**Key Fix**: Generated projects can now properly resolve relative imports regardless of internal structure, solving the "No module named 'project_SNAKE'" error.

### Phase 2: SKIPPED ⏭️

**Rationale**: Since the default theory will be removed in favor of logos, and Phase 1 completely solves the core import issue, Phase 2's template standardization was deemed unnecessary.

### Phase 3: COMPLETED ✅ (Commit: 2512f88)

**Status**: Successfully implemented comprehensive edge case and integration testing

**Test Coverage Added**:
- **test_edge_cases.py** (10 tests): Project names with special characters, directories with spaces, deeply nested modules, multiple projects isolation, boundary cases, sys.path cleanup, error recovery, performance testing, memory usage, CLI integration
- **test_integration_workflow.py** (6 tests): Original user scenario regression, comprehensive theory template workflows, dev CLI integration, structure-agnostic principle verification, project naming edge cases, exact error scenario prevention

**Test Results**: All 56 builder tests pass, confirming robust handling of edge cases and preventing regression

**Key Validations**:
- ✅ Original "project_SNAKE" error scenario completely resolved
- ✅ Structure-agnostic approach works across all theory templates
- ✅ Edge cases like special characters, spaces, and nested structures handled
- ✅ Performance and memory usage remain acceptable
- ✅ CLI integration workflows function correctly
- ✅ Regression prevention measures in place

### Next Steps:
- Phase 4: Documentation updates (optional - core functionality complete)