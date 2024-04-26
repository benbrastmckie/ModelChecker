from z3 import *

# thought this might be interesting to compare, though it only takes modal sentences like '□A'

# Define atomic propositions and modal operators
propositions = {}
modal_operators = {"□": "necessarily", "◇": "possibly"}

# Function to parse modal sentences
def parse_modal_sentence(sentence):
    parsed_sentence = []
    for token in sentence.split():
        if token in modal_operators:
            parsed_sentence.append(modal_operators[token])
        elif token.isalpha():
            if token not in propositions:
                propositions[token] = Bool(token)
            parsed_sentence.append(propositions[token])
    return parsed_sentence

# Function to check if the modal sentence holds in the given Kripke model
def check_modal_sentence(model, sentence):
    parsed_sentence = parse_modal_sentence(sentence)
    if "necessarily" in parsed_sentence:
        # Check if the sentence is necessarily true in all reachable worlds
        for world1 in model["worlds"]:
            for world2 in model["accessibility"][world1]:
                solver = Solver()
                for prop in parsed_sentence[1:]:
                    solver.add(Implies(model["valuation"][world1][prop], model["valuation"][world2][prop]))
                if solver.check() == unsat:
                    return False
    elif "possibly" in parsed_sentence:
        # Check if the sentence is possibly true in some reachable world
        for world1 in model["worlds"]:
            for world2 in model["accessibility"][world1]:
                solver = Solver()
                for prop in parsed_sentence[1:]:
                    solver.add(Or(model["valuation"][world2][prop], Not(model["valuation"][world1][prop])))
                if solver.check() == sat:
                    return True
        return False
    else:
        # Check if the sentence is true in the current world
        solver = Solver()
        for prop in parsed_sentence:
            solver.add(prop)
        return solver.check() == sat

# Function to find Kripke models satisfying the given modal sentence
def find_kripke_models(sentence, num_worlds):
    kripke_models = []
    for i in range(num_worlds):
        # Define worlds and accessibility relation
        worlds = range(i + 1)
        accessibility = {world: [] for world in worlds}
        for world in worlds:
            for j in range(i + 1):
                if j <= world:
                    accessibility[world].append(j)
        # Define valuation function
        valuation = {world: {prop: BoolVal(False) for prop in propositions.values()} for world in worlds}
        # Check if the sentence holds in the Kripke model
        if check_modal_sentence({"worlds": worlds, "accessibility": accessibility, "valuation": valuation}, sentence):
            kripke_models.append({"worlds": worlds, "accessibility": accessibility, "valuation": valuation})
    return kripke_models

# Main program
if __name__ == "__main__":
    # Get modal sentence input from user
    modal_sentence = input("Enter modal sentence: ")
    # Get the number of worlds for the Kripke models
    num_worlds = int(input("Enter the number of worlds: "))
    # Find Kripke models satisfying the modal sentence
    models = find_kripke_models(modal_sentence, num_worlds)
    # Print the satisfying Kripke models
    if models:
        print("Satisfying Kripke models:")
        for i, model in enumerate(models, start=1):
            print(f"Model {i}: {model}")
    else:
        print("No satisfying Kripke models found.")

