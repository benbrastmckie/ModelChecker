# BuildProject Refactoring Plan

## Current Issues

1. **File Creation Inconsistency**: 
   - README.md is created when running directly from repository but not when installed via pip
   - Some files are listed in the output but not actually created
   - Some files are created but not listed in the output (semantics.py vs semantic.py naming)

2. **Template Handling Problems**:
   - The file copying, renaming, and verification steps are not properly coordinated
   - Source files might be missing in some templates but the code doesn't handle this gracefully

## Root Cause Analysis

The primary issues appear to be:

1. **File naming discrepancies**: The code expects `semantics.py` in some places and `semantic.py` in others
  - NOTE: For now I would like to maintain `semantic.py`.
2. **Incomplete file verification**: Files are copied but not always checked to confirm they exist
3. **Installation differences**: When pip-installed, the template files may not be properly included or accessed
4. **Inadequate fallbacks**: Missing required templates don't have proper fallback mechanisms

## Detailed Refactoring Plan

### 1. Template File Management Overhaul

#### Create a Robust Template System

```python
# New approach for template management
DEFAULT_TEMPLATES = {
    "examples.py": {
        "required": True,
        "fallback": "default_examples.py_template",
        "description": "Example model checking cases"
    },
    "operators.py": {
        "required": True,
        "fallback": "default_operators.py_template", 
        "description": "Logical operator definitions"
    },
    "semantic.py": {  # Note: consistently named as semantic.py (not semantics.py)
        "required": True,
        "fallback": "default_semantic.py_template",
        "description": "Semantic theory implementation"
    },
    "README.md": {
        "required": True,
        "fallback": "project_readme_template",
        "description": "Project documentation"
    }
}
```

### 2. Standardize File Names

- Ensure consistent naming between source and destination
- Fix the confusion between `semantic.py` and `semantics.py`
- Update DEFAULT_FILES dictionary to match actual filenames in theory_lib subdirectories

### 3. File Generation Process Redesign

#### New Project Generation Workflow:

1. **Initialize Configuration**
   - Validate source theory directory exists 
   - Create destination directory
   - Prepare template and fallback references

2. **First Pass: Directory Structure**
   - Create base project directory
   - Create test subdirectory if needed

3. **Second Pass: Core Files**
   - Process each template file:
     1. Check if exists in source theory
     2. If exists: copy to destination
     3. If missing: use fallback template
     4. If both missing: raise appropriate error
   - Never silently fail to create a required file
   - Log all file operations for debugging

4. **Third Pass: File Customization**
   - Update file content with project-specific information
   - Replace placeholders with actual values
   - Handle special cases like __init__.py version updates

5. **Final Pass: Verification**
   - Verify all required files exist in destination
   - Generate comprehensive status report
   - Create detailed list of exactly what was created

### 4. Improve pip Install Behavior

- Store fallback templates within the package to ensure they're available when installed via pip
- Add a check to detect if running from a pip installation and adjust paths accordingly
- Use pkg_resources or importlib.resources to access included template files

### 5. Implementation Details

#### New Methods and Their Responsibilities:

```python
def _prepare_project_structure(self):
    """Create base directory structure for the project."""
    # Create main project directory
    # Create any needed subdirectories (test, etc.)
    # Return success status

def _process_template_files(self):
    """Process all template files in a reliable sequence."""
    created_files = {}
    for template_name, config in self.DEFAULT_TEMPLATES.items():
        success, details = self._process_single_template(template_name, config)
        created_files[template_name] = {
            "success": success,
            "path": details.get("path"),
            "source": details.get("source"),
            "description": config["description"]
        }
    return created_files

def _process_single_template(self, template_name, config):
    """Handle creation of a single template file with fallbacks."""
    # Try source theory file
    # If missing and required, try fallback template
    # If both missing and required, raise error
    # Return success status and details

def _customize_file_content(self, file_path, template_name):
    """Update file content with project-specific values."""
    # Read file content
    # Replace placeholders with actual values
    # Handle special cases
    # Write updated content
    # Return success status

def _verify_project_completion(self, created_files):
    """Verify all required files were properly created."""
    # Check each required file exists on disk
    # Validate file content is not empty
    # Return complete verification report
```

### 6. Error Handling Improvements

1. **Detailed Error Messages**:
   - Each error should indicate exactly what went wrong
   - Include suggestions for fixing the problem

2. **Graceful Fallbacks**:
   - When a non-critical file is missing, use a fallback
   - When a critical file is missing, provide clear error

3. **Logging System**:
   - Add comprehensive logging
   - Track each file operation for debugging

### 8. Backward Compatibility

1. **Maintain API Compatibility**:
   - Keep public method signatures unchanged
   - Ensure old code using BuildProject still works

2. **Enhance Rather than Replace**:
   - Refactor internal implementation
   - Keep external behavior consistent unless explicitly noted

### 9. Implementation Order

1. **Phase 1: File Naming Standardization**
   - Audit all theory_lib directories to identify correct file names
   - Update DEFAULT_FILES to use consistent names
   - Fix semantics.py vs semantic.py confusion

2. **Phase 2: Template System Redesign**
   - Implement DEFAULT_TEMPLATES with detailed configuration
   - Add fallback template handling
   - Create built-in fallback templates

3. **Phase 3: Core Process Refactoring**
   - Implement _prepare_project_structure
   - Implement _process_template_files and _process_single_template
   - Implement _customize_file_content

4. **Phase 4: Pip Installation Support**
   - Add detection for pip installation environment
   - Implement resource access for fallback templates
   - Test installation and template handling

5. **Phase 5: Verification and Reporting**
   - Implement _verify_project_completion
   - Enhance output reporting

6. **Phase 6: Error Handling**
   - Add comprehensive error handling
   - Implement logging system

## Quick Fixes Before Full Refactoring

If a complete refactoring is not immediately feasible, here are some targeted fixes that could address the most pressing issues:

1. **Fix File Naming Inconsistency**: 
   - Update DEFAULT_FILES to ensure consistent naming (semantic.py vs semantics.py)
   - Check each theory directory to standardize file naming

2. **Improve README.md Creation**:
   - Add explicit code to ensure README.md is created regardless of installation method
   - Add a simple fallback README template when the source file is missing

3. **Enhance Verification**:
   - Add a verification step that checks all required files exist before reporting success
   - Only list files in the success message that actually exist on disk

4. **Fix pip Installation Issues**:
   - Bundle default templates with the package
   - Use importlib.resources to access these templates when installed via pip

These targeted fixes would address the immediate issues while the more comprehensive refactoring plan is implemented.
