"""
UI component builders for Jupyter widgets.

This module provides helper classes for building complex UI components,
extracting UI construction logic from the main interactive classes.
"""

from typing import Dict, List, Any, Optional, Callable

try:
    import ipywidgets as widgets
    HAVE_IPYWIDGETS = True
except ImportError:
    HAVE_IPYWIDGETS = False
    widgets = None


class ModelExplorerUIBuilder:
    """Builder for ModelExplorer UI components."""
    
    def __init__(self, parent):
        """
        Initialize UI builder.
        
        Args:
            parent: The ModelExplorer instance
        """
        self.parent = parent
    
    def build_main_ui(self) -> 'widgets.Widget':
        """
        Build the main UI layout.
        
        Returns:
            Main UI widget container
        """
        if not HAVE_IPYWIDGETS:
            raise ImportError("ipywidgets is required for UI building")
        
        # Build individual components
        formula_input = self._build_formula_input()
        premises_input = self._build_premises_input()
        theory_selector = self._build_theory_selector()
        settings_accordion = self._build_settings_accordion()
        check_button = self._build_check_button()
        next_model_button = self._build_next_model_button()
        viz_selector = self._build_viz_selector()
        output_area = widgets.Output()
        
        # Store references in parent
        self.parent.formula_input = formula_input
        self.parent.premises_input = premises_input
        self.parent.theory_selector = theory_selector
        self.parent.settings_accordion = settings_accordion
        self.parent.check_button = check_button
        self.parent.next_model_button = next_model_button
        self.parent.viz_selector = viz_selector
        self.parent.output_area = output_area
        
        # Assemble UI components
        control_panel = widgets.VBox([
            formula_input,
            premises_input,
            theory_selector,
            settings_accordion,
            widgets.HBox([check_button, next_model_button]),
            viz_selector
        ])
        
        return widgets.HBox([control_panel, output_area])
    
    def _build_formula_input(self) -> 'widgets.Text':
        """Build formula input widget."""
        return widgets.Text(
            value='p → q',
            description='Formula:',
            style={'description_width': 'initial'}
        )
    
    def _build_premises_input(self) -> 'widgets.Textarea':
        """Build premises input widget."""
        return widgets.Textarea(
            value='',
            description='Premises:',
            placeholder='Enter premises (one per line)',
            style={'description_width': 'initial'}
        )
    
    def _build_theory_selector(self) -> 'widgets.Dropdown':
        """Build theory selector widget."""
        selector = widgets.Dropdown(
            options=self.parent.available_theories,
            value=self.parent.theory_name,
            description='Theory:',
            style={'description_width': 'initial'}
        )
        selector.observe(self.parent._on_theory_change, names='value')
        return selector
    
    def _build_check_button(self) -> 'widgets.Button':
        """Build check formula button."""
        button = widgets.Button(
            description='Check Formula',
            button_style='primary'
        )
        button.on_click(self.parent._on_check_click)
        return button
    
    def _build_next_model_button(self) -> 'widgets.Button':
        """Build next model button."""
        button = widgets.Button(
            description='Find Next Model',
            button_style='info',
            disabled=True
        )
        button.on_click(self.parent._on_next_model_click)
        return button
    
    def _build_viz_selector(self) -> 'widgets.RadioButtons':
        """Build visualization selector."""
        selector = widgets.RadioButtons(
            options=['Text Output', 'Graph Visualization'],
            value='Text Output',
            description='View:',
            style={'description_width': 'initial'}
        )
        selector.observe(self.parent._on_viz_change, names='value')
        return selector
    
    def _build_settings_accordion(self) -> 'widgets.Accordion':
        """
        Build settings accordion with all configuration options.
        
        Returns:
            Settings accordion widget
        """
        # Number of atomic propositions
        n_slider = widgets.IntSlider(
            value=self.parent.settings['N'],
            min=1,
            max=10,
            step=1,
            description='Num Props (N):',
            style={'description_width': 'initial'}
        )
        n_slider.observe(
            lambda change: self.parent._update_setting('N', change['new']), 
            names='value'
        )
        
        # Max time
        max_time_slider = widgets.FloatSlider(
            value=self.parent.settings['max_time'],
            min=1,
            max=30,
            step=1,
            description='Max Time (s):',
            style={'description_width': 'initial'}
        )
        max_time_slider.observe(
            lambda change: self.parent._update_setting('max_time', change['new']),
            names='value'
        )
        
        # Contingent checkbox
        contingent_checkbox = widgets.Checkbox(
            value=self.parent.settings['contingent'],
            description='Contingent Valuations',
            style={'description_width': 'initial'}
        )
        contingent_checkbox.observe(
            lambda change: self.parent._update_setting('contingent', change['new']), 
            names='value'
        )
        
        # Non-empty checkbox
        non_empty_checkbox = widgets.Checkbox(
            value=self.parent.settings['non_empty'],
            description='Non-Empty Valuations',
            style={'description_width': 'initial'}
        )
        non_empty_checkbox.observe(
            lambda change: self.parent._update_setting('non_empty', change['new']), 
            names='value'
        )
        
        # Expectation selector (validity expectation)
        expectation_selector = widgets.Dropdown(
            options=[('Expect Valid', True), ('Expect Invalid', False)],
            value=self.parent.settings.get('expectation', True),
            description='Expectation:',
            style={'description_width': 'initial'}
        )
        expectation_selector.observe(
            lambda change: self.parent._update_setting('expectation', change['new']),
            names='value'
        )
        
        # Print constraints checkbox
        print_constraints_checkbox = widgets.Checkbox(
            value=self.parent.settings['print_constraints'],
            description='Print Constraints',
            style={'description_width': 'initial'}
        )
        print_constraints_checkbox.observe(
            lambda change: self.parent._update_setting('print_constraints', change['new']), 
            names='value'
        )
        
        # Store references
        self.parent.n_slider = n_slider
        self.parent.max_time_slider = max_time_slider
        self.parent.contingent_checkbox = contingent_checkbox
        self.parent.non_empty_checkbox = non_empty_checkbox
        self.parent.expectation_selector = expectation_selector
        self.parent.print_constraints_checkbox = print_constraints_checkbox
        
        # Create accordion
        settings_box = widgets.VBox([
            n_slider,
            max_time_slider,
            contingent_checkbox,
            non_empty_checkbox,
            expectation_selector,
            print_constraints_checkbox
        ])
        
        accordion = widgets.Accordion(
            children=[settings_box],
            selected_index=None
        )
        accordion.set_title(0, 'Settings')
        
        return accordion


class FormulaCheckerUIBuilder:
    """Builder for FormulaChecker UI components."""
    
    def __init__(self, parent):
        """
        Initialize UI builder.
        
        Args:
            parent: The FormulaChecker instance
        """
        self.parent = parent
    
    def build_main_ui(self) -> 'widgets.Widget':
        """
        Build the main UI layout.
        
        Returns:
            Main UI widget container
        """
        if not HAVE_IPYWIDGETS:
            raise ImportError("ipywidgets is required for UI building")
        
        # Build individual components
        formula_input = self._build_formula_input()
        premises_input = self._build_premises_input()
        theory_selector = self._build_theory_dropdown()
        check_button = self._build_check_button()
        output_area = widgets.Output()
        
        # Store references in parent
        self.parent.formula_input = formula_input
        self.parent.premises_input = premises_input
        self.parent.theory_selector = theory_selector
        self.parent.check_button = check_button
        self.parent.output_area = output_area
        
        # Create layout
        return widgets.VBox([
            formula_input,
            premises_input,
            theory_selector,
            check_button,
            output_area
        ])
    
    def _build_formula_input(self) -> 'widgets.Text':
        """Build formula input widget."""
        return widgets.Text(
            value='p → q',
            description='Formula:',
            style={'description_width': 'initial'}
        )
    
    def _build_premises_input(self) -> 'widgets.Textarea':
        """Build premises input widget."""
        return widgets.Textarea(
            value='',
            description='Premises:',
            placeholder='Enter premises (one per line)',
            style={'description_width': 'initial'}
        )
    
    def _build_theory_dropdown(self) -> 'widgets.Dropdown':
        """Build theory selection dropdown."""
        dropdown = widgets.Dropdown(
            options=self.parent.available_theories,
            value=self.parent.theory_name,
            description='Theory:',
            style={'description_width': 'initial'}
        )
        # Only observe if the parent has this method
        if hasattr(self.parent, '_on_theory_change'):
            dropdown.observe(self.parent._on_theory_change, names='value')
        return dropdown
    
    def _build_check_button(self) -> 'widgets.Button':
        """Build check button."""
        button = widgets.Button(
            description='Check Formula',
            button_style='primary'
        )
        button.on_click(self.parent._on_check_click)
        return button
