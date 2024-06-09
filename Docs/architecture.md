# Code architecture

As an overview, the program does three things: 
1. It takes sentences inputted by the user, translates them into constraints on Z3 BitVectors.
2. Finds a model that solves the constraints.
3. Draws on the model to interpret the original sentences provided by the user.


## Step 1: User input to Z3

A set of premises, set conclusions, and BitVector length N are passed to `make_model_for` which calls `prefix` from the `syntax` module.
This converts the premises and conclusions from strings in infix notation to lists in prefix notation conforming to the following rules:
- An atomic input sentence `'A'` is converted to `[A]` in prefix notation, where `A` is declared as a Z3 sort called `AtomSort`.
- The designated top element `'top'` is an `AtomSort` but treated separately by the semantics.
- An atomic input sentence `'unary_operator A'` is `['unary_operator', prefix(A)]`, where `prefix(A)` represents the prefix form of `A`. If `A` is atomic, `'unary_operator A'` is `['unary_operator', [A]]`, where `A` in the embedded list is an AtomSort.
- An atomic sentence `'A binary_operator B'` is `['binary_operator', prefix(A), prefix(B)]`. If `A` and `B` are both atomic, `'A \binary_operator B'` is `['binary_operator', [A], [B]]`, where the `A` and `B` in the embedded lists are AtomSorts.
This ensures that every prefix sentence is an instance of the python list class, and if the length of that list is larger than one, then the first element is the main operator of the sentence (as a string). This allows recursive functions to call the appropriate semantic clauses and to access the contents of the sentences.[^note_on_backslashes]

[^note_on_backslashes]: Trivially, the function `add_backslashes_to_infix` adds two backslashes to every operator and the special `top` sentence so that when print they will be LaTeX commands. Two backslashes are necessary because `'\'` is a special character in python so one instance next to e.g. `'neg'` will not print `'\neg'` but rather `'eg'` on the next line. This also ensures that, in the options where a user can search for a prefix sentence in a solved model, they can find it regardless of whether they originally inputted it with backslashes or not (and regardless of whether they do so in the search).

Once converted, the prefix premises and conclusions are stored in a ModelSetup object.
It is inside ModelSetup that the `define_N_semantics` from the `semantics` module is defined, where this includes the following primitives: 
  - `verify` and `falsify` are relations between states and atomic sentences.
  - `possible` a property of states.
  - `assign` is a function from state-sentence pairs to states and is used to Skolemize the exhaustivity constraint brought out below.
  - `w` is the designated world at which sentences are evaluated.
The prefix premises and conclusions are then converted into Z3 constraints by requiring each premise to be `true_at` the world `w` and each conclusion to be `false_at` the world `w`.
The `true_at` and `false_at` functions include the semantic clauses for the operators in the language and is discussed in greater detail in [Semantics]()



## Step 2: Solving the Z3 Constraints (i.e., Getting a Model) and Organizing Results

These constraints are added to a Z3 solver along with a number of frame constraints and constraints on the verifiers and falsifiers for each sentence letter that occurs in the premises and conclusions.
If a model is found, the elements of that model are stored in a ModelSetup object which is used to print and save the result.
If no model is found, the unsatisfiable core constraints are stored instead.




You may think this step is the most complex in the code, but since we just use the power of Z3 it is actually the most simple—why build tools to solve a huge problem when you can instead just translate your problem into one that someone else already has the tools to solve? As of now we have a ModelSetup object: a bucket with everything we've used so far and (most importantly) a whole bunch of Z3 constraints (constraints on functions that map integers to truth values—see the section "How does `semantics` work?" for background on that). Once the ModelSetup object has been made, you can now solve it with its `solve` method, which is called inside of `make_model_for`. At a high level, in the function a Z3 Solver object is made, the constraints are added to it, Z3 does all the number crunching, and Z3 then spits out a model (a ModelRef object). This is a model that specifies the domain and mappings of the functions `possible`, `verify`, etc. Since all the definitions, like whether a world is an alternative to another, is defined in terms of these functions, we can also extract the domains and values of those definitions (thinking of them as mathematical funtions).[^solve_constraints] [^addtl_info_returned] With this done, returning to our `make_model_for` story, we make a `ModelSetup` object, return it, and we exit the function (notice–that single function is the user's indirect interation with the majority of the code in the package). 

[^solve_constraints]: In reality this all happens inside a function called `solve_constraints`, defined in the `semantics` module, which is called inside of the `solve` method, but that is trivial. 
[^addtl_info_returned]: Some more information, like the time it took to solve the model and whether a model was in fact found, is also returned by `make_model_for`. 

The dirty work that remains is to extract that information about how states (so really integers in binary) relate to concepts like "possible", verification, alternate-ness, worldhood, etc. This is done with the `ModelStructure` and `StateSpace` objects in the `model_structure` module. The ModelStructure object is basically an updated bucket, for convenience, that stores everything that's relevant up to now. It's necessary because in case there is not a model, there is not a state space, so it's counterintuitive to make a StateSpace object. So in the case there is no model, `ModelStructure` is the final result. Otherwise, we proceed to make a `StateSpace` object, which takes the previous two buckets to set up a the space of states. Inside it you can find which states are possible, which are worlds, which is the main world of interpretation, the (mathematical) functions `possible`, `verify`, etc. Proposition objects are also made, which are essentially just a place to store the verifiers and falsifiers of every input sentence (and intermediate sentence). The verifiers and falsifiers for extensional sentences are rather straightforward (and follow the definitions in the manuscript); for non-extensional sentences, a true sentence has a verifier of the null state and no falsifiers, and the converse if false. These objects (themselves mini-buckets of information) are themselves stored in the bigger StateSpace bucket. At this point, all of the relevant information has been found from the Z3 constraints and organized—there is now a list of states (i.e. numbers) that are possible, that are worlds, etc. There are a couple interesting/noteworthy things in this process, which is where the final module `model_definitions` comes in. 
1. Since states are integers (BitVectors) and we know which are possible, which verify others, etc, but not which are alternatives, which are verifiers for _specific propositions_, many of the functions in `model_definitions` look awfully similar to functions in `semantics`, like `fusion` and `bit_fusion`, `is_world` and `bit_world`, etc. Since they do the same thing, why can't the same functions be used for both? The reason boils down to how Z3 represents BitVectors. When defining constraints, Z3 uses `BitVec`s—these bitvectors do _not_ have an assigned value yet. When they do, Z3 represents them as `BitVecVals`, which are bitvectors with an associated value. The functions that Z3 uses on these two are slightly different, so we need to have two sets of functions for them: one set when defining constraints, another when extracting information from them.
2. To define Proposition objects, the function `find_complex_proposition` uses the recursive functions in the manuscript defined with products and coproducts to get verifiers and falsifiers for any sentence that exists in the space created by the original inputs (i.e., any possible subsentence or sentence made by combining any of the inputs).
3. (Add more noteworthy stuff here later?)

However, remember how we solved the constraints: in Z3. So everything at this point remains in terms of BitVectors, which are literally just numbers. This is very hard nigh impossible to understand as raw output, so we must translate it back into something that philsophers (or really anyone/thing besides Z3) can understand. 


## Step 3: Translating from Z3 to Human-Readable Output
We have successfully either found or not found a model for our input sentences! Now we need to translate that into user-readable output. All of the methods for `ModelStructure` and `StateSpace` with "print" in the name do exactly that. They themselves rely on either other methods of these objects or helpers defined in the `model_definitions` module. This step is also where files are made with outputs (with the `print_all` method of `StateSpace`—it itself is an amalgamation of specialized print methods belonging to the StateSpace and ModelSetup of the model). All of this is rather mechanical; an interesting point though, to come full circle, is the function `infix` defined in the `syntax` module: it takes a sentence in prefix notation and returns its infix equivalent. This is used throughout the print methods for human-readable input. Other noteworthy functions in this domain include `pretty_set_print`, which prints python in a nice way. (Add more? I think his covers basically everything. I am also realizing that you've done a lot in this domain @Ben, so maybe you have some insights here.) 
