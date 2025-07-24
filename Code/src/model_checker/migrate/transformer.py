"""
AST-based code transformation for ModelChecker API migration.

This module provides tools for automatically transforming Python source code
from the old ModelChecker API to the new modernized API.
"""

import ast
import sys
import re
from typing import Dict, List, Tuple, Optional, Set
from pathlib import Path


class APITransformer(ast.NodeTransformer):
    """AST transformer for migrating ModelChecker code to new API."""
    
    # Mapping of old imports to new imports
    IMPORT_MAPPINGS = {
        'BuildExample': ('model_checker.builders', 'ExampleBuilder'),
        'BuildModule': ('model_checker.builders', 'ProjectLoader'),
        'BuildProject': ('model_checker.builders', 'ProjectBuilder'),
        'check_formula': ('model_checker.jupyter', 'check_formula'),
        'find_countermodel': ('model_checker.jupyter', 'find_countermodel'),
        'explore_formula': ('model_checker.jupyter', 'explore_formula'),
        'ModelExplorer': ('model_checker.jupyter', 'InteractiveExplorer'),
        'FormulaChecker': ('model_checker.jupyter', 'FormulaChecker'),
        'get_theory': ('model_checker.core', 'Theory'),
        'get_example': ('model_checker.utils', 'get_example'),
        'run_test': ('model_checker.utils', 'run_test'),
        'ForAll': ('model_checker.utils', 'ForAll'),
        'Exists': ('model_checker.utils', 'Exists'),
        'bitvec_to_substates': ('model_checker.utils', 'bitvec_to_substates'),
        'ModelConstraints': ('model_checker.core', 'ModelConstraints'),
        'Syntax': ('model_checker.core', 'Syntax'),
    }
    
    # Settings that need to be renamed
    SETTING_MAPPINGS = {
        'N': 'num_propositions',
        'expectation': 'expect_valid',
        'non_empty': 'non_empty_valuations',
        'print_constraints': 'debug_constraints'
    }
    
    def __init__(self):
        self.imports_to_add: Set[Tuple[str, str]] = set()
        self.imports_to_remove: Set[str] = set()
        self.warnings: List[str] = []
        
    def visit_ImportFrom(self, node):
        """Transform import statements."""
        if node.module == 'model_checker':
            new_imports = []
            
            for alias in node.names:
                name = alias.name
                if name in self.IMPORT_MAPPINGS:
                    new_module, new_name = self.IMPORT_MAPPINGS[name]
                    self.imports_to_add.add((new_module, new_name))
                    self.imports_to_remove.add(name)
                else:
                    # Keep unknown imports as-is with warning
                    self.warnings.append(f"Unknown import '{name}' - please migrate manually")
                    new_imports.append(alias)
            
            if new_imports:
                # Keep the original import with remaining items
                return ast.ImportFrom(
                    module=node.module,
                    names=new_imports,
                    level=node.level
                )
            else:
                # Remove the entire import if all items were mapped
                return None
                
        return self.generic_visit(node)
    
    def visit_Import(self, node):
        """Handle regular import statements."""
        new_names = []
        for alias in node.names:
            if alias.name == 'model_checker':
                # Keep model_checker imports as-is
                new_names.append(alias)
            else:
                new_names.append(alias)
        
        if new_names:
            node.names = new_names
            return node
        return None
    
    def visit_Call(self, node):
        """Transform function and constructor calls."""
        # Transform BuildExample calls
        if self._is_call_to(node, 'BuildExample'):
            return self._transform_build_example(node)
        
        # Transform get_theory calls
        elif self._is_call_to(node, 'get_theory'):
            return self._transform_get_theory(node)
        
        # Transform ModelExplorer calls
        elif self._is_call_to(node, 'ModelExplorer'):
            return self._transform_model_explorer(node)
        
        # Transform settings dictionaries in method calls
        elif hasattr(node.func, 'attr') and node.func.attr in ['check_result', 'check_formula']:
            return self._transform_method_call(node)
        
        return self.generic_visit(node)
    
    def visit_Dict(self, node):
        """Transform settings dictionaries."""
        # Check if this looks like a settings dictionary
        if self._is_settings_dict(node):
            return self._transform_settings_dict(node)
        return self.generic_visit(node)
    
    def _is_call_to(self, node, name):
        """Check if a call node is calling a specific function name."""
        if isinstance(node.func, ast.Name):
            return node.func.id == name
        elif isinstance(node.func, ast.Attribute):
            return node.func.attr == name
        return False
    
    def _is_settings_dict(self, node):
        """Heuristically determine if a dict is a ModelChecker settings dict."""
        if not node.keys:
            return False
        
        # Check for common settings keys
        settings_keys = {'N', 'max_time', 'contingent', 'expectation', 'non_empty', 'print_constraints'}
        dict_keys = set()
        
        for key in node.keys:
            if isinstance(key, ast.Constant) and isinstance(key.value, str):
                dict_keys.add(key.value)
            elif isinstance(key, ast.Str):  # Python < 3.8 compatibility
                dict_keys.add(key.s)
        
        # If more than half the keys are settings keys, assume it's a settings dict
        return len(dict_keys.intersection(settings_keys)) > len(dict_keys) / 2
    
    def _transform_build_example(self, node):
        """Transform BuildExample(name, theory, example) calls."""
        if len(node.args) >= 3:
            name_arg, theory_arg, example_arg = node.args[:3]
            
            # The old pattern: BuildExample(name, theory, [premises, conclusions, settings])
            # New pattern: ExampleBuilder(name, theory).check(premises, conclusions, config)
            
            # Create ExampleBuilder(name, theory)
            builder_call = ast.Call(
                func=ast.Name(id='ExampleBuilder', ctx=ast.Load()),
                args=[name_arg, theory_arg],
                keywords=[]
            )
            
            # Extract premises, conclusions, settings from example list
            if isinstance(example_arg, ast.List) and len(example_arg.elts) >= 3:
                premises, conclusions, settings = example_arg.elts[:3]
                
                # Transform settings dict to ModelConfig
                config_call = ast.Call(
                    func=ast.Name(id='ModelConfig', ctx=ast.Load()),
                    args=[],
                    keywords=self._extract_config_keywords(settings)
                )
                
                # Create builder.check(premises, conclusions, config) call
                check_call = ast.Call(
                    func=ast.Attribute(
                        value=builder_call,
                        attr='check',
                        ctx=ast.Load()
                    ),
                    args=[],
                    keywords=[
                        ast.keyword(arg='premises', value=premises),
                        ast.keyword(arg='conclusions', value=conclusions),
                        ast.keyword(arg='config', value=config_call)
                    ]
                )
                
                self.imports_to_add.add(('model_checker.builders', 'ExampleBuilder'))
                self.imports_to_add.add(('model_checker.core', 'ModelConfig'))
                
                return check_call
            else:
                self.warnings.append("BuildExample with non-list example argument - please migrate manually")
        
        return self.generic_visit(node)
    
    def _transform_get_theory(self, node):
        """Transform get_theory(name) to Theory.load(name)."""
        if node.args:
            theory_name = node.args[0]
            
            # Create Theory.load(name) call
            load_call = ast.Call(
                func=ast.Attribute(
                    value=ast.Name(id='Theory', ctx=ast.Load()),
                    attr='load',
                    ctx=ast.Load()
                ),
                args=[theory_name],
                keywords=[]
            )
            
            self.imports_to_add.add(('model_checker.core', 'Theory'))
            return load_call
        
        return self.generic_visit(node)
    
    def _transform_model_explorer(self, node):
        """Transform ModelExplorer() to InteractiveExplorer()."""
        # Simply rename the class
        new_call = ast.Call(
            func=ast.Name(id='InteractiveExplorer', ctx=ast.Load()),
            args=node.args,
            keywords=node.keywords
        )
        
        self.imports_to_add.add(('model_checker.jupyter', 'InteractiveExplorer'))
        return new_call
    
    def _transform_method_call(self, node):
        """Transform method calls that might contain settings."""
        # Look for settings in keyword arguments
        new_keywords = []
        for keyword in node.keywords:
            if keyword.arg == 'settings' and isinstance(keyword.value, ast.Dict):
                # Transform settings dict to config
                config_call = ast.Call(
                    func=ast.Name(id='ModelConfig', ctx=ast.Load()),
                    args=[],
                    keywords=self._extract_config_keywords(keyword.value)
                )
                new_keywords.append(ast.keyword(arg='config', value=config_call))
                self.imports_to_add.add(('model_checker.core', 'ModelConfig'))
            else:
                new_keywords.append(keyword)
        
        node.keywords = new_keywords
        return self.generic_visit(node)
    
    def _transform_settings_dict(self, node):
        """Transform a settings dictionary to ModelConfig constructor."""
        config_keywords = self._extract_config_keywords(node)
        
        config_call = ast.Call(
            func=ast.Name(id='ModelConfig', ctx=ast.Load()),
            args=[],
            keywords=config_keywords
        )
        
        self.imports_to_add.add(('model_checker.core', 'ModelConfig'))
        return config_call
    
    def _extract_config_keywords(self, dict_node):
        """Extract keyword arguments for ModelConfig from a settings dict."""
        keywords = []
        
        for i, key in enumerate(dict_node.keys):
            if i < len(dict_node.values):
                value = dict_node.values[i]
                
                # Get the key name
                key_name = None
                if isinstance(key, ast.Constant) and isinstance(key.value, str):
                    key_name = key.value
                elif isinstance(key, ast.Str):  # Python < 3.8 compatibility
                    key_name = key.s
                
                if key_name:
                    # Map old setting names to new ones
                    new_key_name = self.SETTING_MAPPINGS.get(key_name, key_name)
                    keywords.append(ast.keyword(arg=new_key_name, value=value))
        
        return keywords


def transform_code(source_code: str) -> Tuple[str, List[str]]:
    """
    Transform source code from old API to new API.
    
    Args:
        source_code: Python source code string
        
    Returns:
        Tuple of (transformed_code, warnings)
    """
    try:
        # Parse the source code
        tree = ast.parse(source_code)
        
        # Transform the AST
        transformer = APITransformer()
        new_tree = transformer.visit(tree)
        
        # Add new imports at the top
        if transformer.imports_to_add:
            import_nodes = []
            for module, name in transformer.imports_to_add:
                import_node = ast.ImportFrom(
                    module=module,
                    names=[ast.alias(name=name, asname=None)],
                    level=0
                )
                import_nodes.append(import_node)
            
            # Insert new imports at the beginning
            new_tree.body = import_nodes + new_tree.body
        
        # Convert back to source code
        try:
            import astor
            transformed_code = astor.to_source(new_tree)
        except ImportError:
            # Fallback if astor is not available
            import ast
            transformed_code = ast.unparse(new_tree)
        
        return transformed_code, transformer.warnings
        
    except SyntaxError as e:
        return source_code, [f"Syntax error in source code: {e}"]
    except Exception as e:
        return source_code, [f"Error transforming code: {e}"]


def transform_file(file_path: Path, backup: bool = True) -> Tuple[bool, List[str]]:
    """
    Transform a Python file from old API to new API.
    
    Args:
        file_path: Path to the Python file
        backup: Whether to create a backup file
        
    Returns:
        Tuple of (success, warnings)
    """
    try:
        # Read the original file
        with open(file_path, 'r', encoding='utf-8') as f:
            original_code = f.read()
        
        # Transform the code
        transformed_code, warnings = transform_code(original_code)
        
        # Check if any changes were made
        if transformed_code == original_code:
            return True, ["No changes needed"]
        
        # Create backup if requested
        if backup:
            backup_path = file_path.with_suffix(file_path.suffix + '.backup')
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(original_code)
            warnings.append(f"Backup created: {backup_path}")
        
        # Write the transformed code
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(transformed_code)
        
        return True, warnings
        
    except Exception as e:
        return False, [f"Error transforming file {file_path}: {e}"]


def batch_transform_files(file_paths: List[Path], backup: bool = True) -> Dict[Path, Tuple[bool, List[str]]]:
    """
    Transform multiple Python files.
    
    Args:
        file_paths: List of file paths to transform
        backup: Whether to create backup files
        
    Returns:
        Dictionary mapping file paths to (success, warnings) tuples
    """
    results = {}
    
    for file_path in file_paths:
        if file_path.suffix == '.py':
            success, warnings = transform_file(file_path, backup)
            results[file_path] = (success, warnings)
        else:
            results[file_path] = (False, ["Not a Python file"])
    
    return results


# Example usage and testing functions
def _example_transformations():
    """Examples of code transformations for testing."""
    
    examples = [
        # BuildExample transformation
        '''
from model_checker import BuildExample, get_theory

theory = get_theory("logos")
example = [[], ["p → q"], {"N": 3, "max_time": 5}]
model = BuildExample("test", theory, example)
result = model.check_result()
        ''',
        
        # Settings dictionary transformation
        '''
settings = {
    "N": 3,
    "max_time": 5,
    "contingent": True,
    "expectation": True,
    "non_empty": False
}
        ''',
        
        # Jupyter imports
        '''
from model_checker import check_formula, ModelExplorer

result = check_formula("p → q", premises=["p"])
explorer = ModelExplorer("logos")
        '''
    ]
    
    for i, example in enumerate(examples, 1):
        print(f"\n=== Example {i} ===")
        print("Original:")
        print(example)
        
        transformed, warnings = transform_code(example)
        print("\nTransformed:")
        print(transformed)
        
        if warnings:
            print("\nWarnings:")
            for warning in warnings:
                print(f"  - {warning}")


if __name__ == "__main__":
    _example_transformations()