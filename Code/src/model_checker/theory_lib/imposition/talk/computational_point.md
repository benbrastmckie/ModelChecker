# Computation

<!-- First, a primer on runtime/space complexity. Computer scientists have developed notions to measure the efficiency of algorithms based on how long they take to run, as a function of their input parameters, called runtime complexity. We will focus on _worst case_ runtime complexity. 
    - example: does someone have a birthday today? I go around asking everyone. O(n), n the number of people in this room.
    - example: do two people share the same birthday in this room? O(n^2), n the number of people in the room.

Similarly, data structures have space complexities that  -->

Z3 functions are saved as array objects. We know this because when we print out a Z3 function, like say `verify` from the default theory, we see an array-like object. This means Z3 saves every value (that it is forced to for a given model) for every input combination, meaning that the space complexity of functions is proportional to the input space. For example, consider a function with inputs in the space of bitvectors with $N=5$. There are $2^5$ bitvectors in this space, so the space complexity of a function with inputs in this space has space complexity of $O(2^5)$. 

This becomes key when thinking of what primitive functions are in the semantics. For example, the default semantics has three primitive functions: `verify`, `falsify`, and `possible`. These are in $O(A*2^N)$, $O(A*2^N)$, and $O(2^N)$, respectively, where $A$ is the number of atomic sentences in the example. (In practice, the three functions are in $O(2^N)$, since $2^N$ is virtually always larger than $A$ for $N>2$.) Indeed, if we print e.g. "possible" for an example ($\neg A, A \boxright C \vDash (A \wedge B) \boxright C$), we see the "possible" as an array:

IMAGE HERE

<!-- As a contrast, consider Fine's imposition semantics, which has the same primitives as the default theory along with a three-place `imposition` function. This has a space complexity of $O(2^{3N})$, which means it will take more space (and thus time) in the worst case to save.  -->

<!-- To give a concrete example with numbers, consider a three-place function with inputs in the space of bitvectors, and assume bitvectors of size $N=7$, which is a rather reasonable number to go up to to look for (interesting) countermodels. The space complexity of this function is $O(2^{3*7})$ -->

<!-- Since there are many other differences that may affect performance with respect to speed between Fine's imposition semantics and the default semantics, we did a comparison of speed between the current version of the default theory and a version with all definitions as Z3 primitives. Each of these new primitives then had a constraint that corresponds to its python function definition. (This method has the advantage that at the moment of evaluation, every function's extension can be found merely by doing `z3_model.evaluate(_____)`, though we will see it comes at a considerable cost). Notably, there were three-place primitive functions, like for example `is_alternative`. We then ran the counterfactual test suite for the default theory on both versions with $N=7$, which has a total runtime of 172 seconds (Z3 run time of 3.3 seconds). The latter version, with all functions as primitives, never terminates, thus showing that the additional space complexity is significant. And even if the limiting fact was the number of primitive functions, these would scale linearly with their complexities, meaning that the problem is only worse for the exponential growth of 2^N.  -->

<!-- NOTE—now you have a new comparison, logos counterfactual with logos counterfactual. The comparison file is `semantic_alt_alt.py`, which is to be compared with `semantic.py` in `logos`.  -->

<!-- This brings up a new methodological consideration for theory building: the arity of our primitive functions now matters from a computational point of view, with less arity being computationally cheaper.  -->

<!-- % \item With inputs in $A \times B$, $A$ being the space of atomic sentences and $B$ the space of bitvectors, `verify' has a worst-case complexity of $O(\abs{A} \abs{B}) = O(\abs{A} 2^N)$, $N$ the size of the bitvectors.
    % NOTE: by 'atomic' sentences you mean using the Z3 primitives, right? Like 'imposition(a, b, c)'
	% \item With inputs in $B^3$, `imposition' has a complexity of $O(2^{3N})$. 
    % NOTE: confusing to use 'B' again. Do you mean to specify the cost of the arity of a predicate? Maybe use 'F^3' and the word 'predicate'.
	% \item This means much slower runtimes for the imposition semantics: imposition semantics takes about 10 times as long as logos to run for $N=4$. 
	% \item Since the complexity of `imposition' is exponential with $N$, this is only more marked for larger values of $N$, which can be useful for finding easily interpretable models. 
    % NOTE: maybe reword this one. Is there a simpler way to say this?
	% \item This provides a computational reason to favor theories that keep the arity of semantic primitives low.
	% \item This reasoning is not too different from familiar questions of theoretical simplicity: this is just a notion of simplicity with regards to the computer -->


Now we have practical presure 