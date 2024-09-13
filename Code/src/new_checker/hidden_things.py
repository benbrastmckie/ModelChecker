from src.model_checker.syntax import prefix

class ModelSetup:
    def __init__(self, infix_premises, infix_conclusions, semantics, max_time, contingent, disjoint):
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.semantics = semantics
        self.max_time = max_time
        self.contingent = contingent
        self.disjoint = disjoint

        self.prefix_premises = [prefix(prem) for prem in infix_premises]
        self.prefix_conclusions = [prefix(con) for con in infix_conclusions]
        prefix_sentences = self.prefix_premises + self.prefix_conclusions
        # need to:
            # find all subsentences
            # find all constraints
            # and that's basically it! 

    def build_test_file(self, output):
        """generates a test file from input to be saved"""
        inputs_data = {
            "N": self.N,
            "premises": self.infix_premises,
            "conclusions": self.infix_conclusions,
            "runtime": self.model_runtime,
            "max_time": self.max_time,
        }
        inputs_content = inputs_template.substitute(inputs_data)
        print(inputs_content, file=output)

    def print_enumerate(self, output):
        """prints the premises and conclusions with numbers"""
        infix_premises = self.infix_premises
        infix_conclusions = self.infix_conclusions
        start_con_num = len(infix_premises) + 1
        if self.infix_premises:
            if len(self.infix_premises) < 2:
                print("Premise:", file=output)
            else:
                print("Premises:", file=output)
            for index, sent in enumerate(self.infix_premises, start=1):
                print(f"{index}. {sent}", file=output)
        if infix_conclusions:
            if len(infix_conclusions) < 2:
                print("\nConclusion:", file=output)
            else:
                print("\nConclusions:", file=output)
            for index, sent in enumerate(infix_conclusions, start=start_con_num):
                print(f"{index}. {sent}", file=output)

    def __str__(self):
        '''useful for using model-checker in a python file'''
        return f'ModelSetup for premises {self.infix_premises} and conclusions {self.infix_conclusions}'

    def __bool__(self):
        '''returns the value of self.model_status (ie, whether the z3 model was solved)
        reasoning: say ms is a ModelSetup object. Now we can check its model_status by doing:
        if ms: # as opposed to if ms.model_status
            (do_something)
        '''
        return self.model_status

class ModelStructure:
    pass