'''
Attempt 2 at doing class semantics. The first issue that came up was the fact that if we put
operator objects in prefix sentences, we need to have the semantics already defined. But if we
have the semantics already defined, we need to already have the constraints generated by the
operators' "true_at" and "false_at" functions. That was fixed by having a global operator_dict, 
that has operator names as keys and dictionaries with relevant info as values. The second problem
that came up was the same reason that semantics is currently one big function: the possible, 
verify, falsify, and assign functions (and N) would have to be passed in as arguments to everything.
At first I reluctantly started editing functions to do that but realized that makes everything
very unfriendly to the user and is quite tedious to implement. The solution I thought of for now
is (not fully implemented, but this is the idea): a user will make a sublcass of the Frame class,
which has all the definitions that do not change from theory to theory. Then they will add to that
class whatever things they want to add re how to define truth and what not by making a subclass
with the same __init__ method and whatever other additional methods they want. Then to add operators,
which is really all that's left at this point, they will add things to the operator_dict of that
Frame object. In this way, the definitions of possible, verify, falsify, and assign (pvfa from now
on) are in the same environment as where they are defining the true_at (and false_at, if bilateral)
method(s) so you don't have to enter pvfa into the method manually, you can access them by inside
the method writing frame.possible (and just pass a frame into the method, which is already done
in the form of self). 

Thought of from the perspective of a user doing all this in a script, the Frame object strategy
allows for broader definitions that operators may depend on to be put in first, then add operators.

Everything after would follow exactly as is in the class semantics doc, with frame information
being accessible to the ModelSetup object by making the Frame object an attribute of the
ModelSetup object or something of that sort. 
'''
# TODO: what methods must every frame have (and thus can go in Frame class), and likewise, what
# methods must every operator have? 

import time
from z3 import (
    sat,
    Lambda, # used in FiniteForAll and FiniteExists definitions
    Implies,
    Or,
    Not,
    Solver,
    And,
    BitVec,
    BitVecVal,
    substitute, # used in FiniteForAll definition
    Function,
    BitVecSort,
    BoolSort,

)
from z3 import Exists as Z3Exists
from z3 import ForAll as Z3ForAll
from syntax import AtomSort, prefix
from semantics import all_sentence_letters
Exists = Z3Exists
ForAll = Z3ForAll

########################################################################################
################################ BEGIN HELPER FUNCTIONS ################################
########################################################################################

def find_prop_constraints(frame, sentence_letters):
    '''
    disjoint bool is not implemented
    '''
    return [frame.proposition_definition(atom) for atom in sentence_letters]


########################################################################################
################################# END HELPER FUNCTIONS #################################
########################################################################################

class Frame:

    # B: I moved the commented lines below into the instance since the may vary by user
    def __init__(self, N):
        self.N = N
        # self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        # self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.operator_dict = {}
        # self.w = BitVec("w", N) # what will be the main world

    def find_premise_constraints(self, prefix_premises, main_world):
        """find constraints corresponding to the input sentences
        takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
        returns a list of Z3 constraints
        used in find_all_constraints"""
        return [self.premise_constraint_behavior(premise, main_world) for premise in prefix_premises]
        # return [self.prefix_constraint_behavior(premise, main_world) for premise in prefix_premises]
        # B: should this be premise_constraint_behavior? where is this defined?
        # B: where do the sentence letters occur? why are they needed here?

    def find_conclusion_constraints(self, prefix_conclusions, main_world):
        """find constraints corresponding to the input sentences
        takes in sentences in prefix form and the input sentence letters (a list of AtomSorts)
        returns a list of Z3 constraints
        used in find_all_constraints"""
        # return [self.true_at(conclusion, main_world) for conclusion in prefix_conclusions]
        return [self.conclusion_constraint_behavior(conclusion, main_world) for conclusion in prefix_conclusions]
        # B: where do the sentence letters occur? why are they needed here?

    def add_operator(self, operator_name, **kw):
        self.operator_dict[operator_name] = kw


class ModelSetup():
    def __init__(self, frame, infix_premises, infix_conclusions):
        self.frame = frame
        self.max_time = 2 # B: this is a placeholder for later
        self.prefix_premises = [prefix(prem) for prem in infix_premises]
        self.prefix_conclusions = [prefix(con) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        self.sentence_letters = all_sentence_letters(prefix_sentences)
        self.frame_constraints = frame.frame_constraints()
        self.atom_proposition_constraints = find_prop_constraints(frame, self.sentence_letters)
        self.premise_constraints = frame.find_premise_constraints(self.prefix_premises, frame.w)
        self.conclusion_constraints = frame.find_conclusion_constraints(self.prefix_conclusions, frame.w)
        self.constraints = (
            self.frame_constraints +
            self.atom_proposition_constraints +
            self.premise_constraints +
            self.conclusion_constraints
        )
        timeout, z3_model_status, z3_model, model_runtime = self.solve(
                self.constraints,
                self.max_time # B: ModelSetup has no 'max_time' member; I added a place holder
            )
        self.timeout = timeout
        self.model_status = z3_model_status
        self.z3_model = z3_model
        self.model_runtime = model_runtime

    # NOTE: seems to mostly be working but occasionally seems to run longer than the printed time
    def solve(self, all_constraints, max_time): # all_constraints is a list of constraints
        """Finds a model for the input constraints within the max_time if there is such a model
        returns a tuple with a boolean representing if (1) the timeout occurred, if (2) the
        constraints were solved or not and, if (3) the model or unsatisfiable core depending"""
        solver = Solver()
        solver.add(all_constraints)
        # Set the timeout (in milliseconds)
        milliseconds = int(max_time * 1000)
        solver.set("timeout", milliseconds)
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

    # ... and so on for ModelSetup object
