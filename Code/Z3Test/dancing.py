from z3 import *


def find_happy_dancing_model():
    # Define a set of people
    people = ["Alice", "Bob", "Charlie"]

    # Define boolean variables for happiness and dancing for each person
    happy = {person: Bool(f"{person}_happy") for person in people}
    dancing = {person: Bool(f"{person}_dancing") for person in people}

    # Create Z3 solver instance
    solver = Solver()

    # Add constraints
    for person in people:
        # If a person is happy, they must be dancing
        solver.add(Implies(happy[person], dancing[person]))
        # If a person is dancing, they may not be happy
        solver.add(Not(Implies(dancing[person], Not(happy[person]))))

    # Add constraint that at least one person is happy
    solver.add(Or([happy[person] for person in people]))

    # Check if there is a model
    if solver.check() == sat:
        model = solver.model()
        # Print the model
        print(
            "Model where someone is happy, and everyone who is happy is dancing but not everyone who is dancing is happy:"
        )
        for person in people:
            print(
                f"{person}: happy={model[happy[person]]}, dancing={model[dancing[person]]}"
            )
    else:
        print("No model found.")


# Find a model
find_happy_dancing_model()
