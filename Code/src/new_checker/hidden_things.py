from z3 import (
    sat,
    Solver,
)
import time
from syntax import prefix
from src.model_checker.model_definitions import find_subsentences
from src.model_checker.semantics import all_sentence_letters

# B: this looks really clean!
class ModelSetup:

    # B: there are a lot or arguments for the class. could it make sense to define an Input class
    # and pass that class to ModelSetup alongside semantics and operators_list?
    def __init__(
            self,
            infix_premises,
            infix_conclusions,
            semantics,
            max_time,
            contingent,
            disjoint,
            operators_list
        ):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.operators = operators_list
        self.max_time = max_time
        self.contingent = contingent
        self.disjoint = disjoint

        self.prefix_premises = [prefix(prem, self) for prem in infix_premises]
        self.prefix_conclusions = [prefix(con, self) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.all_subsentences = find_subsentences(prefix_sentences)
        self.all_sentence_letters = all_sentence_letters(prefix_sentences)
        
        self.frame_constraints = semantics.frame_constraints
        self.model_constraints = [semantics.find_model_constraints(sl) for sl in self.all_sentence_letters]
        self.premise_constraints = [semantics.premise_behavior(prem, semantics.w) for prem in self.prefix_premises]
        self.conclusion_constraints = [semantics.conclusion_behavior(conc, semantics.w) for conc in self.prefix_conclusions]
        self.all_constraints = (self.frame_constraints + self.model_constraints + 
                                self.premise_constraints + self.conclusion_constraints)

    # B: should this go into ModelStructure? I was thinking ModelSetup would include everything
    # short of running the solver and that the ModelStructure would start off by running the solver
    def solve(self):
        solver = Solver()
        solver.add(self.all_constraints)
        solver.set("timeout", int(self.max_time * 1000)) # in milliseconds
        try:
            model_start = time.time()  # start benchmark timer
            result = solver.check()
            model_end = time.time()
            model_runtime = round(model_end - model_start, 4)
            if result == sat:
                return False, True, solver.model(), model_runtime
            if solver.reason_unknown() == "timeout":
                return True, False, None, model_runtime
            return False, False, solver.unsat_core(), model_runtime
        except RuntimeError as e:
            # Handle unexpected exceptions
            print(f"An error occurred while running `solve_constraints()`: {e}")
            return True, False, None, None

    def __str__(self):
        '''useful for using model-checker in a python file'''
        return f'ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions}'

class ModelStructure:
    pass
