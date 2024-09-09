Name: Miguel Buitrago\
Faculty Supervisor: Ben Brast-McKie\
Direct Supervisor: Brad Skow\
Term: Fall 2024\
9/5/24
 
# Formal Verification for the Working Semanticist <!-- good title? -->
 
## Project Overview

> Provide an explanation/background of your UROP project that includes the project aim, context & scope, and with whom you are conducting research.

This project is a continuation of the UROP I did with Dr. Brast-McKie last semester.
The aim of the project is to continue developing the `model-checker`, a package that checks the validity of theorems given a hyperintensional semantics for a language which includes a counterfactual conditional operator. 

Counterfactuals have long proven difficult to adequately model within intensional semantic frameworks.
Intensional theories are forced to accept trade-offs between the desired rules of inference, for example classifying a rule like **Strengthening the Antecedent** (i.e., $A > C \vdash (A \wedge B) > C$, where `>` represents the counterfactual conditional operator) as a valid rule when it is natural to take this rule to be invalid, or else classifying a rule like **Simplification of Disjunctive Antecedent** (i.e., $(A \vee B) > C \vdash (A > C) \wedge (B > C)$) as invalid when it is natural to assume otherwise. 

In order to overcome these issues, Kit Fine's hyperintensional truthmaker semantic (Kit Fine's "Counterfactuals without Possible Worlds" (2012), "A Theory of Truthmaker Content I" (2017), and "Truthmaker Semantics" (2017)) evaluates sentences at _states_ rather than the _possible worlds_ employed in intensional theories.
Whereas possible worlds are primitive points in a model, states are ordered by _parthood_ and so may be composed mereologically to form a complete lattice, providing for much richer theories of content than possible worlds. 

Dr. Brast-McKie has developed a semantics for counterfactuals that adequately models some of the long-standing difficulties previous intensional theories have had with counterfactuals (classifying both aforementioned inference rules as desired) (Brast-McKie forthcoming).
However, given the added complexity of hyperintensional models, it remains difficult to find models by hand, thereby motivating the development of a program that can automate this process.
Beyond this specific application, this project aims to lay down methodology for making semantic theories of increasing complexity more tractable to its users.

Last semester, I did a UROP to create the `model-checker` package that checks whether a given inference is valid under Dr. Brast-McKie’s hyperintensional semantics of counterfactual conditionals.  
The project this semester aims to expand the package to be applicable to semantics besides Dr. Brast-McKie’s.
In particular, it would be extremely useful to be able to compare different hyperintensional semantic systems.
To this end, the project seeks to rewrite the package as it currently stands so that a user could develop novel semantic theories by defining operators (e.g., Champollion (2023)’s unilateral theory of negation), definitions (e.g., what is considered a proposition in the model), and other relations among states. 

## Communication with Mentor(s)

I plan to communicate with my mentor via email, GitHub issues, and weekly meetings. 

## Briefly explain the following:

### Research Role & Tentative Work Plan

We will meet weekly to evaluate progress.
Dr. Brast-McKie will lead the design of the package and I will lead the implementation on the GitHub, though we will collaborate as is necessary and expected in a coding project like this.
The first step will be to refactor the package so that a user could define a novel semantics, bypassing Dr. Brast-McKie’s which will be maintained as a default.
We will then use draw on other hyperintensional semantic theories (namely Fine’s imposition semantics and Champollion’s unilateral semantics for negation) as case studies to see what differences in valid theorems and countermodels arise between these and Dr. Brast-McKie's semantics.
I will be leading the effort on Champollion’s semantics and Dr. Brast-McKie on Fine’s.
Finally we will focus on improving documentation and outlining the findings for a publication.
Anticipated deliverables will be the package and, time permitting, a write-up of the Champollion case study to be used in the publication detailing the package. 
 
### Personal Statement/Goals

I am majoring in Linguistics and Philosophy with a minor in CS.
This project sits at the intersection of philosophy, computer science, and linguistics, all of which are fields that greatly interest me.
More specifically, the project focuses on the semantics of counterfactuals for which I have developed particular interest through the linguistics and philosophy courses I’ve taken.

This project also aims to develop new methodology for semantics research.
I am excited about the prospect of contributing to the evolution of a field that I’m interested in. 
Last semester I learned more than I thought I could about recent developments in logic and their applications to philosophy and linguistics.
By continuing with this project, I hope to learn more, especially since I am approaching the end of my time as an undergraduate and am considering applying to graduate programs in these fields.
I hope to learn more about the fields of logic and formal semantics to see if they are something I’d like to purse in graduate school.  

Working on this project last semester helped me improve my programming skills immensely, and I'm excited to continue to expand my knowledge during this next term.
One of the unexpected challenges from last semester was reading through APIs (particularly Z3’s is not as explanatory or pedagogical as some of the packages that are used in the programming classes I’ve taken, like numpy or pytorch in 6.390).
I would like to continue improving on working with unfamiliar APIs, as there are still many aspects of Z3 that I am not familiar with.  
In addition to this general skill set, Z3 itself has more proven its worth as a powerful tool well deserving of study.
