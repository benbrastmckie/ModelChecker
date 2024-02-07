from z3 import Bool, Solver, sat


def find_model(boolean_sentence):
    # Create a solver instance
    solver = Solver()

    # Define boolean variables using Z3 Bool
    variables = {}
    for variable in set(boolean_sentence.replace("(", "").replace(")", "").split()):
        variables[variable] = Bool(variable)

    # Parse the boolean sentence and add it to the solver
    parsed_sentence = eval(boolean_sentence, variables)
    solver.add(parsed_sentence)

    # Check for satisfiability
    if solver.check() == sat:
        # Get the model
        model = solver.model()

        # Extract variable assignments from the model
        variable_assignments = {
            var: model.evaluate(variables[var], model_completion=True)
            for var in variables
        }

        return variable_assignments
    else:
        return None


if __name__ == "__main__":
    # Example boolean sentence: (A or B) and (not A or C)
    boolean_sentence = "(A or B) and (not A or C)"

    # Find a model for the boolean sentence
    model = find_model(boolean_sentence)

    if model:
        print("Model found:")
        for variable, value in model.items():
            print(f"{variable}: {value}")
    else:
        print("No model found for the given boolean sentence.")
