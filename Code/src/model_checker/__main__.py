'''
file specifies premises, conclusions, and settings.
running the file finds a model and prints the result.
to test from the Code/ directory, run: python -m src.model_checker 
'''

import sys
import subprocess
import argparse

# Standard imports
from model_checker import __version__
from model_checker.builder import (
    BuildProject,
    BuildModule,
)


class ParseFileFlags:
    """Parses command line arguments and manages configuration flags for the model checker application.
    
    This class provides a centralized way to handle command-line interface (CLI) arguments,
    process various configuration flags, and manage the overall execution settings of the
    model checker tool."""

    def __init__(self):
        """Initialize the argument parser with default configuration settings.
        
        Sets up the parser instance variable but does not process any arguments.
        The actual parsing happens later in the parse() method."""
        self.parser = self._create_parser()
        self.flags = None
        self.package_name = None

    def _create_parser(self):
        """Create and configure the argument parser with all supported command line options.
        
        Returns:
            argparse.ArgumentParser: A configured parser that handles all command line arguments
            including file paths, semantic theory options, output controls, and utility flags.
        """
        # Create the parser
        parser = argparse.ArgumentParser(
            prog='model-checker',
            usage='%(prog)s [options] input',
            description="""
            Running '%(prog)s' without options or an input will prompt the user
            to generate a project. To run a test on an existing file, include
            the path to that file as the input.""",
            epilog="""
            More information can be found at:
            https://github.com/benbrastmckie/ModelChecker/""",
        )
        # Add arguments
        parser.add_argument(
            "file_path",
            nargs='?',
            default=None,
            type=str,
            help="Specifies the path to a Python file.",
        )
        parser.add_argument(
            '--contingent',
            '-c',
            action='store_true',
            help='Overrides to make all propositions contingent.'
        )
        parser.add_argument(
            '--disjoint',
            '-d',
            action='store_true',
            help='Overrides to make all propositions have disjoint subject-matters.'
        )
        parser.add_argument(
            '--non_empty',
            '-e',
            action='store_true',
            help='Overrides to make all propositions non_empty.'
        )
        parser.add_argument(
            '--load_theory',
            '-l',
            type=str,
            metavar='NAME',
            help='Load a specific theory by name.'
        )
        parser.add_argument(
            '--maximize',
            '-m',
            action='store_true',
            help='Overrides to compare semantic theories.'
        )
        parser.add_argument(
            '--non_null',
            '-n',
            action='store_true',
            help='Overrides to make all propositions non_null.'
        )
        parser.add_argument(
            '--print_constraints',
            '-p',
            action='store_true',
            help='Overrides to print the Z3 constraints or else the unsat_core constraints if there is no model.'
        )
        parser.add_argument(
            '--save_output',
            '-s',
            action='store_true',
            help='Overrides to prompt user to save output.'
        )
        parser.add_argument(
            '--print_impossible',
            '-i',
            action='store_true',
            help='Overrides to print impossible states.'
        )
        parser.add_argument(
            '--version',
            '-v',
            action='version',
            version=f"%(prog)s:  {__version__}",
            help='Prints the version number.'
        )
        parser.add_argument(
            '--upgrade',
            '-u',
            action='store_true',
            help='Upgrade the package.'
        )
        parser.add_argument(
            '--print_z3',
            '-z',
            action='store_true',
            help='Overrides to print Z3 model or unsat_core.'
        )
        parser.add_argument(
            '--align_vertically',
            '-a',
            action='store_true',
            help='Overrides to display world histories vertically with time flowing from top to bottom.'
        )
        return parser

    def parse(self):
        """Parse command line arguments and store results in instance variables.
        
        This method processes the command line arguments using argparse and stores
        the parsed flags and package name in the instance variables self.flags
        and self.package_name respectively.
        
        Returns:
            tuple: A tuple containing (parsed_args, package_name) where:
                - parsed_args: The parsed command line arguments
                - package_name: The name of the package (model-checker)
        """
        # Create a mapping from short flag names to long names
        self._short_to_long = {
            'c': 'contingent',
            'd': 'disjoint',
            'e': 'non_empty',
            'l': 'load_theory',
            'm': 'maximize',
            'n': 'non_null',
            'p': 'print_constraints',
            's': 'save_output',
            'i': 'print_impossible',
            'v': 'version',
            'u': 'upgrade',
            'z': 'print_z3',
            'a': 'align_vertically'
        }
        
        # Store the original command line arguments
        import sys
        self._parsed_args = sys.argv[1:]
        
        # Parse the arguments
        self.flags = self.parser.parse_args()
        
        # Add the mapping and args to the flags object for use in settings manager
        self.flags._short_to_long = self._short_to_long
        self.flags._parsed_args = self._parsed_args
        
        self.package_name = self.parser.prog
        return self.flags, self.package_name

def main():
    """Main entry point for the model checker application.

    This function handles the primary execution flow of the model checker:
    
    1. If no arguments are provided, it launches the interactive project generator
    2. Otherwise, it processes command line arguments to:
        - Upgrade the package if requested
        - Load a specific semantic theory if specified
        - Run model comparisons if maximize flag is set
        - Execute model checking on provided examples
    
    The function supports various modes of operation:
    - Interactive project generation
    - Package upgrade via pip
    - Loading specific semantic theories
    - Running model comparisons
    - Executing model checks on example files

    No parameters or return values as this is the main program entry point.
    """
    # Check for Jupyter dependencies if they'll be needed
    jupyter_flags = ["-j", "--jupyter", "-n", "--notebook"]
    needs_jupyter = any(flag in sys.argv for flag in jupyter_flags)
    
    if needs_jupyter:
        # Check for required dependencies if Jupyter features are requested
        missing_deps = []
        for pkg in ["ipywidgets", "matplotlib", "networkx"]:
            try:
                __import__(pkg)
            except ImportError:
                missing_deps.append(pkg)
                
        if missing_deps:
            print(f"Error: The following required dependencies are missing: {', '.join(missing_deps)}")
            print("To use Jupyter notebook features, install them with:")
            print("  pip install model-checker[jupyter]")
            return
    
    if len(sys.argv) < 2:
        builder = BuildProject()
        builder.ask_generate()
        return
    parser = ParseFileFlags()
    module_flags, package_name = parser.parse()
    if module_flags.upgrade:
        print("Upgrading package")
        try:
            subprocess.run(['pip', 'install', '--upgrade', package_name], check=True)
        except subprocess.CalledProcessError as e:
            print(f"Failed to upgrade {package_name}: {e}")
        return
    if module_flags.load_theory:
        semantic_theory_name = module_flags.load_theory
        builder = BuildProject(semantic_theory_name)
        builder.ask_generate()
        return

    module = BuildModule(module_flags)

    # TODO: create print/save class
    if module.general_settings["maximize"]:
        module.run_comparison()
        return

    module.run_examples()

def run():
    """Entry point for the application."""
    main()

if __name__ == '__main__':
    run()
