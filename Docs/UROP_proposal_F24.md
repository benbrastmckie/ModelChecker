Name: Miguel Buitrago
Faculty Supervisor: Ben Brast-McKie
Direct Supervisor: Brad Skow
Term: Fall 2024
9/5/24
 
### Using model-checker to Evaluate Hyperintensional Semantics
 
 
## Project Overview
Provide an explanation/background of your UROP project that includes the project aim, context & scope, and with whom you are conducting research.
This project is a continuation of the UROP I did with Dr. Brast-McKie last semester. The aim of the project is to continue developing model-checker, a package that checks theorems for a hyperintensional semantics of counterfactuals. 
	Counterfactuals have long proven difficult to adequately model with intensional semantics. Intensional theories often end up not formally accounting for all desired rules of inference, for example classifying a rule like Strengthening the Antecedent (A ☐-> C derives (A and B) ☐-> C, where ☐-> represents the counterfactual operator) as a valid rule when it is usually considered invalid, or classifying a rule like Simplification of Disjunctive Antecedent ((A v B) ☐-> C derives (A ☐-> C) and (B ☐-> C)) as invalid when it is usually considered valid. 
However, recently, hyperintensional truthmaker semantics (Kit Fine 2017, “Truthmaker Semantics”), where the truth of a statement is not evaluated at a world but rather by the states that compose that world, have provided logicians with more tools to make a formal theory to capture all desired rules of inference. 
Dr. Brast-McKie has developed a semantics for counterfactuals that adequately models some of the long-standing difficulties previous intensional theories have had with counterfactuals (classifying both aforementioned inference rules as desired) (Brast-McKie forthcoming). However, hyperintensional models like Brast-McKie’s prove difficult to provide models for by hand, reason for which a program that can automatically look for models would make theories like this useful and tractable in the field of formal semantics. Last semester, I did a UROP to create a package called model-checker that checks whether provided rules of inference are valid under Dr. Brast-McKie’s semantics of counterfactuals.  
The project this semester is to expand the package to be applicable to semantics besides Dr. Brast-McKie’s. Currently, the package can only find models for theorems using Dr. Brast-McKie’s semantics of counterfactuals, but it would be more useful to be able to compare different hyperintensional semantics, which tend to be difficult to create models for by hand, quickly. To this end, the project is to rewrite the package as it currently is so that a user could define a semantics, inputting operators (e.g. Brast-McKie’s counterfactual or Champollion (20203)’s unilateral negation), definitions (e.g. what is considered a proposition in the model), and other relations among hyperintensional states (fusion, parthood, etc). 

## Communication with Mentor(s)
I plan to communicate with my mentor via email and weekly check-ins. 

## Briefly explain the following:

# Research Role & Tentative Work Plan
We will meet weekly to check in on progress, with Dr. Brast-McKie leading the design of the package and me leading the implementation on the GitHub, though we will collaborate on our roles as necessary and expected in a coding project like this. The first step will be to refactor the package so that a user could define the semantics as input and not have to use Dr. Brast-McKie’s as default. After that, we will use other hyperintensional semantics (namely Fine’s imposition semantics and Champollion’s unilateral negation) as test cases to see what differences in valid theorems and countermodels arise between these and Dr. Brast-McK’e's semantics. I will be leading the effort on Champollion’s semantics and Dr. Brast-McKie on Fine’s. Finally we will focus on improving documentation and outlining the findings for a publication. Anticipated deliverables will be the package and, if time allows, a write-up of the Champollion test case to be used in the publication detailing the package. 
 
# Personal Statement/Goals
Broadly, this project sits at the intersection of philosophy, computer science, and linguistics, all of which are fields that greatly interest me (I am after all majoring in Linguistics and Philosophy with a minor in CS). More specifically, the project is in semantics and counterfactuals, for which I have particularly developed an interest through the linguistics and philosophy courses I’ve taken. Finally, it is a novel methodological approach in the field, so the prospect of being able to see a field I’m interested move forward is exciting. 
Last semester I learned more than I thought I could about recent developments in logic and their applications to philosophy and linguistics through this project, so by continuing the project I hope to learn more, especially since I approach the end of my time as an undergrad and am considering applying to graduate programs in these fields. I hope to learn more about the fields of logic and formal semantics to see if they are something I’d like to purse in graduate school.  
Programming skills can always be improved, and I feel that last semester this project helped me immensely to improve them. One of the unexpected challenges from last semester was reading through APIs (particularly Z3’s is not as explanatory or pedagogical as some of the packages that are used in programming classes I’ve taken, like numpy or pytorch in 6.390); I would like to continue improving on working with unfamiliar APIs, as there are still many aspects of Z3 that I am not familiar with.  
