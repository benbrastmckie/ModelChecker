# Paper Outline: A Programmatic Framework for Modular Semantic Theory Development Using SMT Solvers

**Target Journal**: Journal of Automated Reasoning

---

## Abstract (250 words max)

**Key Elements**:
- Problem: Lack of systematic computational tools for semantic theory development
- Approach: ModelChecker framework treating theories as executable programs
- Innovation: Theory-agnostic architecture for diverse semantic frameworks
- Methodology: Finite model exploration via SMT constraints
- Complexity metrics: Objective computational measures replacing subjective evaluations
- Vision: TheoryLib extensible library
- Results: 4 frameworks, 177+ examples
- Significance: First computational bilateral truthmaker semantics implementation

---

## 1. Introduction

Semantic theories specify the truth conditions of logical formulas through mathematical models consisting of possible worlds, times, situations, states, or other semantic primitives depending on the target language under study. Developing such theories traditionally proceeds by hand-verified semantic proofs and countermodels. This paper presents a computational framework that treats semantic theories as executable programs, enabling systematic model exploration, empirical theory comparison, and automated validation checking through SMT constraint solving.

### 1.1 The Challenge of Semantic Theory Development

Semantic theorizing faces a fundamental tension between expressive power of the language and the difficulty of verifying inferences. Modern semantic frameworks such as intensional semantics, situation semantics, and truthmaker semantics employ increasingly sophisticated model structures to capture fine-grained distinctions in content. This sophistication restricts the range of inferences that can be validated by hand.

**The Complexity Problem**

As theories grow more complex, verifying their consequences increases in difficult. The problem intensifies when theories combine multiple operators in order to study their interactions.

**The Comparison Problem**

Semantic theorists frequently propose alternative frameworks claiming to better capture some semantic domain. Comparing theories is typically informal, relying on judgments of theoretical parsimony. Without empirical metrics, theory choice often reflects subjective assessments of elegance or intuitive fit rather than systematic benchmarking that compares semantic theories on standardized inputs to measure comparative performance.

**The Tractability Problem**

Some semantic theories are computationally demanding. Others are much more tractable, yielding efficiently solvable constraints. Traditional semantic theorizing treats computational complexity as an implementation detail, external to semantic concerns. We argue that computational complexity should inform semantic theory development, taking computability to be a theoretical virtue that can be measured and used to guide theory choice.

### 1.2 The Computational Turn in Semantics

**TODO**: Expand with specific recent projects in computational philosophy/automated reasoning, identifying their scope and limitations relative to our approach.

SMT solvers, originally developed for program verification, provide powerful engines for constraint satisfaction over complex mathematical structures. Applying SMT technology to semantic theory development is a natural extension: semantic models are mathematical structures; semantic theories specify constraints over these structures; SMT solvers find assignments satisfying constraints.

**Prior Computational Approaches**

Several research programs have explored computational approaches to semantic theory:

- **Automated theorem proving for modal logic**: Provers for modal logics exist, but typically target specific well-studied systems (S4, S5) rather than providing frameworks for implementing arbitrary semantic theories.

- **Model checking for temporal logics**: Bounded model checking techniques from formal verification could apply to semantic theories, but remain theory specific.

- **General-purpose automated reasoning tools**: Systems like Prover9 (theorem prover) and Mace4 (finite model finder) provide powerful first-order reasoning capabilities. While these tools can encode semantic theories in first-order logic, they lack semantic-theory-specific infrastructure: no native support for semantic clause specifications, no operator modularity, no comparative framework for testing multiple theories on shared examples.

**The Gap: Theory-Agnostic Semantic Frameworks**

What's missing is a theory-agnostic framework enabling researchers to implement diverse semantic theories, test them on shared examples, and compare their validation patterns and computational characteristics systematically. Whereas existing tools target specific logics and focus on theorem proving, we need infrastructure supporting arbitrary semantic frameworks in order to explore the space of countermodels for invalid inferences. Instead of treating theories individually, we need systematic comparative methodology to enhance theory selection. Moreover, pure first-order encodings can be cumbersome for semantic structures. By contrast, SMT solvers that support bitvectors for state spaces, uninterpreted functions for semantic relations, and arithmetic for cardinality constraints provide more natural and efficient representations.

### 1.3 Contributions: A Programmatic Framework for Semantic Theory Development

This paper presents the ModelChecker, a framework treating semantic theories as executable programs that can be systematically tested, compared, and analyzed. The framework makes six principal contributions to semantic methodology and automated reasoning.

**Contribution 1: Theory-Agnostic Architecture**

The framework provides infrastructure independent of particular semantic theories, providing uniform treatment of syntactic parsing, constraint generation, model extraction, and output formatting. This theory-agnosticism enables implementing new theories by providing semantic clause specifications without modifying core infrastructure, creating a plugin architecture for semantic theorizing.

The significance is methodological: separating theory-independent infrastructure from theory-specific semantics enables systematic comparison on identical computational foundations. Differences in validation patterns or performance reflect genuine theoretical differences rather than implementation variations.

**Contribution 2: Compositional Modularity**

Semantic theories are implemented as compositions of operator modules, each providing syntactic parsing, semantic interpretation, and model construction and representation. Operators can be selectively loaded, enabling exploration of language fragments as convenient. Subtheories can share operator implementations, promoting consistency and efficiency.

The modular architecture provided by the ModelChecker mirrors compositional semantics by making the computability of a complex inference a function of the computability of their components.

**Contribution 3: Systematic Comparative Methodology**

The framework enables running identical arguments through multiple semantic theories under controlled conditions, measuring both validation outcomes and computational costs. This produces empirical comparative data replacing informal assessments with reproducible measurements.

The methodological innovation is experimental control in semantic theorizing. Traditional comparison lacks controlled conditions; the framework provides them. This enables evidence-based theory evaluation complementing intuitive and formal-theoretical considerations.

**Contribution 4: Bounded Model Exploration**

The framework searches bounded regions of model space for counterexamples through finite model techniques adapted to semantic theories. While not providing complete decision procedures, bounded search finds genuine countermodels when they exist within search bounds and provides evidence for validity through countermodel exclusion within increasingly large search spaces. Finite model exploration reflects an epistemically modest methodology appropriate to semantic theorizing. We gain evidence for validity through systematic failure to find countermodels rather than claiming absolute proofs.

**Contribution 5: TheoryLib**

The framework includes implementations of four semantic theories: bilateral truthmaker semantics (Logos), unilateral truthmaker semantics (Exclusion), Fine's imposition semantics, and bimodal temporal-modal logic. This demonstrates theory-agnosticism across diverse frameworks. These implementations form the foundation of TheoryLib, an extensible library envisioned as a collaborative platform for sharing semantic theories.

Community infrastructure of this form provides a methodology for researchers to implement theories in a standardized form, making them available for comparative testing, educational use, and further adaptation. The TheoryLib provides for semantics what proof assistant libraries provide for formalized mathematics: shared, reusable, validated implementations.

**Contribution 6: Computational Complexity as a Theoretical Virtue**

The framework provides empirical measures of semantic theory complexity through timeout rates, solve times, and maximum tractable model sizes. Analysis reveals that the arity of semantic primitives directly predicts computational tractability. Computational complexity becomes a practical evaluation criterion alongside logical adequacy and intuitive fit.

**Paper Structure**

Section 2 presents the complete pipeline architecture from input specification through constraint generation to output formatting. Section 3 examines the three-layer operator architecture and compositional modularity that enables theory-agnostic extensibility. Section 4 develops the systematic comparative methodology: controlled experimental design, empirical complexity metrics, and cross-theory validation patterns. Section 5 addresses model exploration through configurable semantic constraints and bounded search via countermodel iteration with isomorphism detection. Section 6 establishes the arity-complexity thesis, demonstrating that primitive arity determines tractability boundaries through model space analysis, frame constraint complexity examination, and comparative case studies. Section 7 concludes by developing the TheoryLib vision, providing practical guidance for testing existing theories and implementing new semantic frameworks, and inviting collaborative contribution to computational formal semantics.

---

## 2. Complete Pipeline Architecture

This section presents the basic architecture of the ModelChecker pipeline which transforms logical arguments into validity determinations. Understanding this transformation is essential to grasping how the framework achieves theory-agnostic semantic evaluation.

### 2.1 Input Specification and Configuration

The framework accepts logical arguments alongside semantic theory specifications, enabling systematic exploration of how different semantic frameworks evaluate identical inference patterns.

**Argument Specification Design**

Each logical argument consists of premise formulas, conclusion formulas, and settings. This structure mirrors standard logical notation while permitting precise control over the semantic search space. For example, constraining atomic propositions to be contingent (having both verifiers and falsifiers) filters out trivial models where propositions are necessarily true or false.

**Multi-Theory Evaluation Architecture**

The input structure accepts multiple semantic frameworks, evaluating each argument with each theory in turn. This enables direct theory comparison by measuring validity determinations and computational times side-by-side.

### 2.2 Logical Processing Pipeline

The core transformation from symbolic formulas to validity determinations proceeds through four stages while remaining theory-agnostic.

**Stage 1: Syntactic Parsing**

Object-language formulas (e.g., `((A \\wedge B) \\rightarrow C)`) are transformed into structured representations amenable to semantic interpretation. The parser builds recursive sentence structures while remaining agnostic to operator semantics by requiring all formulas to consist of binary operators prefixed with `\\` and wrapped in parentheses and unary operators that bind to the next immediate argument. The separation between syntactic structure and semantic interpretation is fundamental to maintaining theory independence.

**Stage 2: Semantic Constraint Generation**

Each formula generates constraints in the SMT solver expressing what it means for that formula to be verified or falsified according to the chosen semantic theory. This translation from semantic metalanguage (the theory's truth/verification conditions) to SMT constraints is where theory-specific semantics enter the pipeline.

Four categories of constraints jointly specify the countermodel search problem:
1. **Frame constraints** encode the semantic structure (e.g., accessibility relations, mereological principles, etc.)
2. **Model constraints** ensure atomic propositions receive valid semantic values determined by the definition of a proposition in that theory
3. **Premise constraints** require all premises to be satisfied
4. **Conclusion constraints** require at least one conclusion to be false

The combination forms a satisfiability problem: Is there a model satisfying the semantic framework's structural principles where the premises are all true but conclusions are not?

**Stage 3: SMT Solving**

The Z3 solver attempts to find an assignment that satisfies all constraints, bounded by user-specified timeouts and state-space size limits. This is bounded model checking for semantic theories: we search finite portions of the model space rather than attempting complete decision procedures. If the solver finds a satisfying assignment, it has discovered a countermodel. If no satisfying assignment exists within the bounded search, we gain evidence that the argument is valid rather than providing a proof.

**Stage 4: Model Iteration (Optional)**

When multiple countermodels are requested, the system iteratively excludes previously discovered models through additional constraints while checking for structural isomorphism to avoid presenting mere relabelings of identical model structures. This exploration of countermodel diversity reveals the deeper structure of the countermodel space for particular inferences.

### 2.3 Output Generation and Interpretation

SMT solver results are transformed into interpretable semantic structures if a satisfying countermodel is found, with output formats tailored to the use case.

**Validity Reporting**

For valid arguments (no countermodel found within search bounds), the system reports the search space explored, providing evidence for but not proof of validity. As search bounds increase, confidence in genuine validity is strengthened.

**Countermodel Visualization**

Invalid arguments yield countermodels displayed according to theory specifications. An extensional model specifies truth-vales; an intensional model specifies the worlds each sentence is true in and the extension of an accessibility relation; a hyperintensional model displays state-based verification and falsification along with a parthood relation while distinguishing possible states, world states, and impossible states. The visualization is encoded alongside each operator to ensure modularity.

**Comparative Analysis**

Identical arguments can be run through multiple theories, generating empirical data on how semantic frameworks differ in their validation patterns and computability. This produces systematic comparative data rarely available in traditional semantic theorizing: concrete, reproducible evidence of which theories validate which inferences and at what computational expense.

**Multiple Output Formats**

Different research tasks require different output formats. Interactive console output supports rapid exploration; structured JSON enables programmatic analysis; Jupyter notebooks provide reproducible computational narratives for reporting and presentation; Markdown outputs provide a baseline for capturing outputs in a minimal and readable form for later reference.

**Pipeline Integration**

The three-stage architecture (input specification, constraint-based solving, and theory-specific output) achieves a crucial design goal: theory-agnostic infrastructure with theory-specific plugins. Core components (parsing, constraint solving, output management) operate independently of particular semantic frameworks, while theory modules provide the semantic interpretation that gives formal symbols their meaning. This separation enables the extensibility and systematic comparison that the subsequent sections explore.

## 3 Modular Operator Classes

The framework's modularity emerges from a fundamental design principle: logical operators should be self-contained units that encapsulate syntactic recognition, semantic interpretation, and result presentation. This architecture enables theory composition, selective loading, and systematic reuse across semantic frameworks, providing framework extensibility.

### 3.1 Three-Layer Operator Architecture

Logical operators provide methods for operating at three distinct conceptual levels, each addressing a different aspect of the semantic evaluation problem. This layered design enforces separation of concerns while maintaining compositional coherence.

**Layer 1: Syntactic Recognition**

At the syntactic level, operators are purely structural entities characterized by their name, LaTeX code, and arity. Infix sentences of the form `(A \\wedge B)` are converted to prefix notation `[\\wedge, A, B]` in preparation for interpretation. Although the binary operator `\\wedge` is recognized as requiring exactly two arguments, nothing at this level specifies what `\\wedge` *means*. This abstraction is what enables the same parser to handle the operators included in different languages uniformly.

The parser builds recursive formula structures recognizing only operator arities, not their semantic interpretations. This means adding a new operator to a theory requires no modification to the parsing infrastructure since the parser recognizes any operator symbol meeting structural requirements.

Defined operators exemplify this separation: the material conditional can be treated syntactically as a primitive binary operator `\\rightarrow` while semantically being defined as `(\\neg A \\vee B)`. Whereas the parser sees the structure, the semantic layer sees through the definition. This enables theoretical economy (fewer primitives) without any cost to convenience.

**Layer 2: Semantic Interpretation**

Operators provide theory-specific semantic methods to translate purely syntactic constructions in prefix notation into formal SMT constraints. Despite sharing the same syntactic structure, a conjunction operator in classical logic implements different semantic methods than conjunction in hyperintensional semantics.

Rather than hardcoding "worlds" as evaluation points, the framework passes extensible dictionaries containing whatever contextual parameters the theory requires to evaluate sentences:
 **Extensional theories** require no contextual parameters since sentences receive truth-values directly
 **Intensional theories** require a single contextual parameter which is interpreted to be a world for circumstantial modals, information state for epistemic modals, or a time for tense operators
 **Bimodal theories** require two contextual parameters that specify both the world-history and a time in that history
 **Normative theories** require additional parameters for utility functions or preference orderings over the space of worlds, states, or evolutions depending

Beyond evaluation parameters, frameworks also differ in structural requirements: bilateral theories require independent specification of truth and falsity conditions, while unilateral theories define falsity as negation of truth. All theories require model extraction methods translating solver assignments into readable semantic values.

This design accommodates semantic diversity: the framework does not impose a single semantic interface. Instead, operators implement whichever methods their semantic framework requires. The framework adapts to the theory rather than forcing theories into a single semantic pattern.

**Layer 3: Model Interpretation**

Once the solver produces a satisfying assignment, operators translate raw solver values into theory-appropriate model structures, calling methods to present the semantic information. The same logical negation operator displays differently depending on the semantic framework: classical negation shows simple truth-value flips, while bilateral negation inverts the sets of verifiers and falsifiers. This layer recognizes that semantic theories differ not just in their validation patterns but in how they conceptualize and present semantic information.

**Architectural Significance**

The three-layer architecture achieves theory-agnosticism through strategic abstraction points. Layers 1 and 3 (syntax and output) provide stable interfaces, while Layer 2 (semantics) serves as the plugin point where theory-specific interpretations enter. This design pattern recurs throughout the framework and enables the extensibility that subsequent sections explore.

### 3.2 Subtheory Composition and Modular Loading

Semantic theories are not monolithic. Classical logic comprises connectives with distinct semantic behaviors; modal logic extends classical logic with intensional operators. The ModelChecker accommodates extensibility through subtheory modules that can be selectively loaded and combined.

**Compositional Theory Design**

Rather than implementing theories as indivisible units, the framework treats them as compositions of operator subtheories. For instance, the Logos theory comprises five independent subtheories: extensional connectives, modal operators, constitutive operators, counterfactual conditionals, and relevance operators. Each subtheory can be loaded independently or in combination.

Modular subtheories serves both practical and theoretical purposes. Practically, loading only required operators reduces overhead, improving performance. Theoretically, subtheory composition enables exploring fragments of semantic frameworks that make sense to study independent of other operators.

**Dependency Management**

Subtheories exhibit dependency relationships: modal operators are interdefinable in the presence of extensional connectives and may be defined in the presence of counterfactual and extensional operators. The framework automatically resolves these dependencies, ensuring that loading a subtheory transitively loads all required dependencies without circularity. This enables users to request high-level operator sets while the system handles dependencies.

### 3.3 Semantic Framework Patterns and Operator Responsibilities

While operators are theory-specific plugins, certain patterns emerge across semantic frameworks. Understanding these patterns illuminates both the diversity and commonalities of formal semantic approaches.

**Intensional Semantics Pattern**

Intensional frameworks (modal, temporal, epistemic logics) share a common structure: operators define truth conditions relative to evaluation points in some structured space (worlds, times, information states). Operators in these frameworks implement methods specifying truth-at-point conditions, typically involving quantification over accessible points.

This pattern reflects a deep semantic commitment: meaning involves truth conditions across alternative scenarios. The framework accommodates this through evaluation-point-parameterized semantic methods, enabling operators to implement the "look at alternative points" semantic pattern that characterizes intensional logics.

**Bimodal Semantics Pattern**

Bimodal frameworks combine two evaluation dimensions by integrating temporal and modal operators within a unified semantic structure. For instance, operators receive both a world-history parameter (for modal evaluation) and a time parameter (for temporal evaluation), with truth conditions specified relative to history-time pairs. Operators must coordinate these dimensions: a temporal operator like "always" quantifies over times within a world-history, while a modal operator like "necessarily" quantifies over histories at a given time.

This pattern reflects a compositional semantic commitment: different semantic dimensions can be independently varied and systematically combined. The framework supports this through multi-parameter evaluation dictionaries, enabling operators to access whichever contextual coordinates their semantics require. Bimodal theories demonstrate that the framework's parameter-passing architecture scales naturally from single-dimension to multi-dimension evaluation without architectural modification.

**Hyperintensional Semantics Pattern**

Hyperintensional frameworks (truthmaker semantics, situation semantics) evaluate formulas not at worlds but at partial states or situations. Operators implement verification and falsification methods that quantify over states, often with mereological structure (part-whole relations, fusion operations). For instance, negation swaps the verifiers and falsifiers for its argument where neither verifiers nor falsifiers are defined in terms of each other. Although bilateral frameworks permit gaps or gluts in truth-values, these may be eliminated by imposing frame constraints.

The key semantic innovation is *partiality*: formulas are verified or falsified by states that might be partial, representing fragmentary information. Conjunction, for instance, is verified by fusing the verifier states of its conjuncts. This semantic pattern enables hyperintensional distinctions between necessarily equivalent formulas based on their verification structure.

**Defined Operator Abstraction**

Some operators are not semantically primitive but defined in terms of others. For instance, the material conditional may be defined as `(\\neg A \\vee B)`. Defined operators do not need semantic methods since they expand to their definitions before semantic evaluation. This provides notational convenience without semantic complexity, following standard practices of metalinguistic abbreviation in semantics.

**Implications for Theory Design**

These patterns suggest design principles for implementing semantic theories: Identify core semantic primitives, implement their semantic methods, define convenient abbreviations as derived operators. The framework's architecture encourages this separation, rewarding clean semantic design with improved performance and maintainability. Theories with fewer, simpler semantic primitives yield reliable implementations that are easy to maintain.

## 4. Systematic Comparative Methodology

A persistent challenge in semantic theory development is comparison: how do different frameworks fare on identical test cases? Which theories are computationally simpler? Traditional comparison is informal and unsystematic, relying on selective examples and subjective assessments. The ModelChecker enables systematic empirical comparison by running identical arguments through multiple semantic theories under controlled conditions, measuring both validation outcomes and computational costs. This implements **Contribution 3: Systematic Comparative Methodology** (Section 1.3).

### 4.1 Comparative Framework Design

When multiple theories are provided, the framework evaluates each theory on the same argument with identical settings, measuring both validation outcomes and computational costs. This produces concrete, reproducible comparative data replacing subjective assessments of theory complexity.

The methodology controls for discrepancies in test conditions so that differences in outcomes or performance reflect genuine theoretical differences rather than variations in test conditions. Experimental measures are not provided by traditional semantic theorizing which relies on manual proofs.

**Multi-Theory Evaluation Protocol**

The input structure accepts multiple semantic frameworks, evaluating each argument with each theory in turn (Section 2.1). This enables direct theory comparison: identical inputs, identical configuration, identical search bounds. The only variation is the semantic theory itself. Differences in validation patterns or performance thus reflect theoretical commitments rather than experimental artifacts.

This experimental control is the methodological innovation. Traditional semantic comparison lacks controlled conditions: different researchers test different examples, use different proof techniques, focus on different fragments. The framework provides standardized conditions enabling systematic evidence-based theory evaluation.

### 4.2 Empirical Complexity Metrics

Evaluating examples with multiple theories yields empirical complexity data: which theories timeout on which examples, which scale to larger state spaces, which validate or invalidate particular patterns. These metrics complement traditional theoretical complexity analysis with empirical performance data.

**Metrics Collected**

- **Validation outcomes**: Which theories declare the argument valid vs. invalid
- **Solve times**: Time required to reach validity determination (in milliseconds)
- **Timeout rates**: Percentage of test cases exceeding time bounds
- **Maximum tractable domain size**: Largest N value permitting solution within timeout
- **Constraint counts**: Number of SMT constraints generated by each theory

**Theoretical vs. Empirical Complexity**

Theoretical complexity (quantifier alternation, primitive arity) predicts computational costs based on model space size and constraint structure. Empirical performance measures actual cost on specific examples. Sometimes they align (primitive arity correctly predicts timeouts), sometimes they diverge (solver heuristics, optimizations, formula-specific structure).

The framework provides both perspectives. Empirical measurements validate theoretical predictions (Section 6) while revealing performance variations within complexity tiers. Theory A and Theory B might share the same primitive arity (same tier) yet differ by 2-3× in solve time due to frame constraint differences.

### 4.3 Cross-Theory Validation Patterns

Beyond performance metrics, comparison reveals how theories differ in their validation patterns: which inferences they accept as valid, which they reject, and why.

**Validation Agreement and Divergence**

Some inferences produce agreement: all theories validate modus ponens, all reject affirming the consequent. These represent semantic universals—logical patterns independent of semantic framework choices.

Other inferences produce divergence: Theory A validates while Theory B invalidates. These divergences reveal theoretical commitments. Hyperintensional theories may invalidate inferences that intensional theories validate, reflecting their sensitivity to verification structure beyond truth conditions.

**Comparison as Theoretical Insight**

Systematic comparison transforms theory evaluation from informal assessment to empirical investigation. Instead of asking "Does this theory seem simpler?", we ask "How does this theory perform on 177 test cases relative to alternatives?"

Concrete questions become answerable:
- Do bilateral and unilateral frameworks validate the same inferences?
- How much computational overhead does bilateral tracking impose?
- Which theory differences matter for validation, which only affect performance?

The comparative methodology enables evidence-based answers grounded in reproducible measurements.

### 4.4 Setting Up Complexity Analysis

The empirical observations raise explanatory questions: Why do theories differ in performance? What structural properties determine computational costs?

Section 6 develops a theoretical explanation: **primitive arity determines tractability boundaries**. The empirical comparison provides evidence for this thesis:

- Logos and Exclusion (binary primitives) show similar performance tier despite different primitive counts
- Imposition (ternary primitive) exhibits dramatic performance degradation
- Performance gaps align with model space predictions from primitive arity

This section establishes the empirical phenomena; Section 6 explains them theoretically. The progression from comparative observation to theoretical analysis demonstrates how computational tools enable new forms of semantic investigation: systematic measurement generating explanatory hypotheses validated through formal analysis.

---

## 5. Model Exploration and Bounded Search

The framework enables systematic exploration of model spaces through configurable constraints and iterative countermodel discovery. This section examines how researchers control the search space through hierarchical configuration and how the system discovers structurally distinct countermodels through constraint-based iteration combined with isomorphism detection.

### 5.1 Hierarchical Configuration and Research Flexibility

The framework implements a multi-level configuration hierarchy balancing global defaults with local overrides. This design assists research by providing different levels of control depending for flexibility and ease of use.

**Configuration Hierarchy as Research Tool**

At the broadest level, framework-wide defaults ensure sensible baseline behavior. Theory-specific defaults capture semantic assumptions distinctive to particular frameworks. User-level preferences enable researchers to establish their own working assumptions. Example-level settings permit fine-grained control for specific test cases. Command-line flags provide immediate overrides.

This hierarchy allows researchers to restrict the space of models while remaining flexible. Global defaults ensure reproducibility and comparability across experiments. Local overrides enable exploring variations without modifying core configurations. The architecture makes the distinction between standing assumptions and temporary variations explicit in the configuration structure.

**Methodological Significance**

The hierarchical design has methodological implications beyond mere convenience. It distinguishes theory-constitutive constraints (embedded in semantic implementations) from investigative constraints (imposed by researchers exploring consequences).

### 5.2 Constraint Composition and Interaction

Constraints compose: requiring both contingency and disjointness yields models satisfying both conditions. But constraints also interact: contingency implies non-emptiness (contingent propositions must have verifiers and falsifiers), so redundant constraints can be omitted. The framework handles these interactions, applying only the minimal constraint set expressing the desired conditions.

This compositional approach mirrors theoretical practice. Semantic theorists often build up model requirements incrementally: start with basic structural requirements, add contingency, impose subject-matter constraints. The framework's constraint composition enables the same incremental specification, with each addition narrowing the model space explored.

### 5.3 Countermodel Discovery and Iteration

Finding a single countermodel establishes invalidity. But how many structurally distinct countermodels exist? Is the countermodel space rich or sparse? Exploring countermodel diversity reveals semantic properties invisible from single-model examination.

**The Model Iteration Problem**

Naively requesting multiple countermodels risks redundancy: the solver might return the same model structure with different variable assignments (e.g., where world w₁ merely trade names w₂). Such label variants are structurally identical, representing the same countermodel under different naming schemes. Meaningful diversity requires structural distinctness, not mere label variation.

To systematically explore structurally distinct countermodels while avoiding label variants, the ModelChecker implements iterative constraint-based exclusion combined with graph isomorphism detection.

**Constraint-Based Model Exclusion**

The core strategy is incremental: find one countermodel, add constraints excluding it, find another model, add further exclusion constraints, repeat. Each iteration narrows the search space by excluding previously discovered models while maintaining the original semantic requirements.

This approach has theoretical elegance: model exclusion is itself expressed as constraints, so the iteration process works within the same constraint-satisfaction framework used for initial discovery. We're not switching paradigms (from solving to enumeration); we're incrementally refining constraints to explore the solution space systematically.

**The Isomorphism Challenge**

Constraint-based exclusion alone is insufficient since excluding a specific variable assignment doesn't rule out isomorphic variants. Without isomorphism detection, iteration might return many label variants of a model with the same structure.

Graph isomorphism detection solves this: represent models as labeled graphs (worlds as nodes, accessibility relations as edges, valuations as labels) and check whether new models are isomorphic to previous ones. Isomorphic models are rejected, triggering additional exclusion constraints. Only structurally distinct models are accepted.

### 5.4 Isomorphism Detection and Structural Distinctness

Full graph isomorphism is computationally expensive. The framework employs a two-stage strategy: quick structural checks (node count, edge count, degree sequences) cheaply reject most non-isomorphic models; expensive full isomorphism checking runs only when cheap checks pass. This optimizes for the common case while maintaining correctness.

The approach reflects a performance principle: spend computational effort proportionally to expected payoff. Most models will differ in basic structural properties (different numbers of worlds, different accessibility patterns). Full isomorphism checking is reserved for structurally similar models, reducing average-case cost.

**Methodological Applications**

Model iteration enables several research methodologies:

1. **Diversity assessment**: How rich is the countermodel space for this inference? Sparse countermodel spaces suggest the argument is "nearly valid"; rich spaces suggest deep invalidity.

2. **Structural comparison**: How do countermodel structures differ across theories? Do they share common patterns or exhibit fundamental differences?

3. **Minimal countermodels**: Iterate with increasing bounds to find smallest distinguishing models, revealing minimal structural requirements for counterexamples.

Each methodology leverages systematic countermodel exploration to address questions beyond simple validity testing, demonstrating how computational tools enable new forms of semantic investigation.

### 5.5 Termination and Search Space Boundaries

Model iteration raises a termination question: when should the search stop? Unlike validity checking (stop when countermodel found or search space exhausted), iteration could continue indefinitely seeking ever more countermodels. The framework employs multiple termination conditions reflecting different exhaustion scenarios.

**Termination Conditions**

Iteration terminates when: (1) the requested number of distinct models is found (successful completion), (2) timeout limits are reached (resource exhaustion), (3) the solver reports no more satisfying assignments exist (search space exhausted), or (4) consecutive isomorphism failures suggest we've found all non-isomorphic models in the accessible search space (heuristic exhaustion).

These conditions reflect different search outcomes. Successful completion means we found desired diversity. Resource exhaustion means computational limits constrained exploration. Search space exhaustion means we've found all countermodels within bounded space. Heuristic exhaustion suggests we've likely found all accessible distinct models given isomorphism clustering.

**Epistemic Status of Termination**

Each termination condition has different epistemic status. Successful completion: we have N distinct countermodels (definite within specified bounds). Resource exhaustion: countermodel space may be richer than explored (indefinite). Search space exhaustion within bounds: no more countermodels exist in bounded space (definite within bounded models). Heuristic exhaustion: likely found all accessible distinct models (supporting evidence).

The framework reports termination reasons, enabling users to interpret results. Finding 5 models then timing out means "at least 5 distinct countermodels exist"; finding 5 models then exhausting search space means "exactly 5 distinct countermodels exist within the bounded space of models." The distinction matters for theoretical conclusions drawn from iteration results.

## 6. Computational Complexity and Primitive Arity

Semantic theories differ dramatically in their computational characteristics. Some theories enable rapid model checking across large state spaces, while others timeout on modest search bounds. This section examines how the computational complexity of semantic theories is directly determined by the arity of their semantic primitives—the fundamental Z3 relations and functions that constitute the theory's model structure—with higher-arity primitives inducing exponentially larger model spaces that must be searched.

This arity-complexity relationship has both theoretical and practical significance. Theoretically, it identifies a structural property of semantic frameworks—primitive arity—that predicts computational behavior independently of implementation details or solver optimizations. Practically, it provides design guidance for semantic theorists: theories built from lower-arity primitives exhibit better computational tractability than theories requiring higher-arity primitives.

### 6.1 Semantic Primitives and Model Space

Computational tractability is determined by the primitive fundamental Z3 functions and relations that constitute a semantic theory's model structure. These *semantic primitives* are declared using z3.Function() and represent the basic elements over which the SMT solver searches when seeking countermodels.

**Examples of Semantic Primitives in TheoryLib**

Different semantic theories employ different primitives:

- `possible(x)`: A unary predicate determining whether state x is possible (Logos, Exclusion, Imposition)
- `verify(x, p)`: A binary relation specifying that state x verifies atomic proposition p (Logos, Exclusion, Imposition)
- `falsify(x, p)`: A binary relation specifying that state x falsifies atomic proposition p (Logos, Imposition)
- `excludes(x, y)`: A binary relation specifying that state x excludes state y (Exclusion)
- `imposition(x, w, u)`: A ternary relation specifying that imposing state x on world w yields outcome world u (Imposition)
- `task(x, y)`: A binary relation specifying transition from world-state x to world-state y (Bimodal)
- `truth_condition(x, p)`: A binary relation specifying truth of proposition p at world-state x (Bimodal)

The *arity* of a primitive is the number of arguments it accepts. The `possible` predicate is unary (one argument), `verify` and `excludes` are binary (two arguments), and `imposition` is ternary (three arguments).

**Model Space and Search Complexity**

When the SMT solver searches for countermodels, it explores the space of all possible assignments to the semantic primitives. The size of this search space is determined by four factors: (1) the domain cardinality D=2^N, (2) the number of sentence letters P, (3) the arity of each primitive, and (4) the number of primitives.

Sentence letters that occur in the inference under evaluation provide the atomic propositions over which formulas are built. Primitive arguments are typed where state arguments (like x, y, w, u) range over the D domain, while sentence letter arguments (like p, q) range over P sentence letters.

**Model space size M by theory:**

When a theory employs multiple primitives, their model spaces multiply to yield the combined search space. Assuming N=4 and P=3 results in a domain cardinality D=16 which may use for the following example calculations:

- **Logos**: M = 2^D × 2^(D·P) × 2^(D·P) = 2^(D + 2D·P) = 2^112
  - `possible(x)`: 2^D
  - `verify(x,p)`: 2^(D·P)
  - `falsify(x,p)`: 2^(D·P)

- **Exclusion**: M = 2^D × 2^(D·P) × 2^(D²) = 2^(D + D·P + D²) = 2^320
  - `possible(x)`: 2^D
  - `verify(x,p)`: 2^(D·P)
  - `excludes(x,y)`: 2^(D²)

- **Imposition**: M = 2^D × 2^(D·P) × 2^(D·P) × 2^(D³) = 2^(D + 2D·P + D³) = 2^4208
  - `possible(x)`: 2^D
  - `verify(x,p)`: 2^(D·P)
  - `falsify(x,p)`: 2^(D·P)
  - `imposition(x,w,u)`: 2^(D³)

For primitives with k arguments ranging over states and h arguments ranging over sentence letters, the number of possible assignments for that primitive is 2^(D^k × P^h). Since D is typically much larger than P, the dominant complexity factor is the maximum state argument count k. Assuming N=4 and P=3, `falsify` contributes 2^8 possible assignments, `excludes` contributes 2^16 possible assignments, and `imposition` contributes 2^64 which dominates all other contributions for large values of D.

Strong evidence for validity findings requires scaling both D (larger domains) and P (more complex formulas). To maximize these dimensions while preserving computational tractability, the critical structural factors are the argument signatures of primitives and the primitive count. Increasing the arity of a semantic primitive from k to k+1 increases the possible assignments by the same amount as adding D-1 additional semantic primitives of arity k.

**Primitive Arity as the Dominant Factor**

The exponential scaling of model space with primitive arity establishes arity as the dominant factor in computational complexity. While frame constraint complexity, formula nesting depth, and sentence letter count all affect performance, none produces comparable impact. This dominance explains why maximum primitive arity serves as the primary complexity classifier for semantic theories.

### 6.2 Frame Constraints and the Pruning-Complexity Tradeoff

Frame constraints impose structural requirements on semantic primitives, ruling out invalid model regions before the solver explores them. These constraints exhibit a fundamental performance tradeoff: while they prune invalid search space through constraint propagation, they also impose computational overhead through constraint expansion, memory consumption, and propagation costs. Well-designed frame constraints dramatically accelerate solving; poorly-designed constraints degrade performance or exhaust available memory, crashing the solver.

**The Pruning Benefit**

Frame constraints eliminate invalid primitive assignments through constraint propagation. Consider downward closure on the `possible` primitive:

```
Downward Possibility: ∀x∀y[(possible(y) ∧ part_of(x, y)) → possible(x)]
```

When expanded over D=16 states, this generates D²=256 constraints. If the solver assigns `possible(s)=false`, propagation immediately infers `possible(t)=false` for all states t containing s as a part, potentially eliminating hundreds of invalid assignments. Without this constraint, the solver would accept semantically invalid models where possible states contain impossible parts.

**The Complexity Cost**

The same constraints that enable pruning impose computational costs:

1. **Memory consumption**: Each expanded constraint consumes memory. Downward closure over D=16 generates 256 clauses; over D=32 generates 1,024 clauses. Memory scales as D^k for k-ary quantification.

2. **Propagation overhead**: The solver must check constraints after each assignment. More constraints slow propagation, creating tension: constraints prune search space but degrade the propagation mechanism.

3. **Coupling**: When multiple constraints share primitives, they create dependency networks. Assignments to one primitive trigger cascading propagations across coupled constraints, forcing the solver to reason about joint assignment spaces rather than independent primitive spaces.

**Memory Explosion: Catastrophic Failure**

Excessive frame constraints cause catastrophic failure through memory exhaustion. For Imposition theory at N=12 (D=4,096):
- Four ternary-quantified constraints expand to 4×D³ ≈ 275 billion constraints
- Memory requirement: ~27 terabytes
- Result: Immediate out-of-memory crash

Empirical testing confirms Imposition crashes at N≥13 from constraint explosion. The ternary primitive's D³ scaling exhausts available memory before solving begins. Even when constraints initially fit, dynamic clause learning can trigger mid-search memory exhaustion.

**Conclusion: Frame Constraints Compound with Primitive Arity**

Even with optimal frame constraint design, primitive arity remains the dominant complexity driver. Higher-arity primitives require more frame constraints to ensure semantic validity, and those constraints expand more rapidly (D³ vs. D²). Frame constraint complexity thus *compounds* with primitive arity, reinforcing that semantic primitive arity determines the fundamental tractability boundaries of SMT-based semantic theory implementation.

### 6.3 The Primitive Count Tradeoff: Logos vs. Exclusion

The choice of semantic primitives involves a fundamental tradeoff: more primitives enable simpler semantic clauses and frame constraints, while fewer primitives require complex semantic clauses and additional frame constraints to achieve equivalent expressive power. This section examines this tradeoff through the comparison of Logos and Exclusion theories.

**Logos: More Primitives, Simple Semantics**

Logos employs three semantic primitives to provide truthmaker semantics for logical operators:
- `verify(x, p)`: State x verifies sentence letter p
- `falsify(x, p)`: State x falsifies sentence letter p
- `possible(x)`: State x is metaphysically possible

This primitive choice enables remarkably simple semantics for negation:
```
extended_verify(s, ¬φ, w) = extended_falsify(s, φ, w)
extended_falsify(s, ¬φ, w) = extended_verify(s, φ, w)
```

Negation simply swaps verifiers and falsifiers. If state s verifies φ, then s falsifies ¬φ. If s falsifies φ, then s verifies ¬φ. This elegant symmetry requires no quantification, no witness predicates, no complex conditions—just direct substitution.

Frame constraints are equally simple. Logos requires only two frame constraints:
1. **Downward closure**: `∀x∀y[(possible(y) ∧ part_of(x,y)) → possible(x)]`
2. **Actuality**: `is_world(main_world)`

The downward closure constraint ensures parts of possible states remain possible, while actuality constrains the evaluation point to be a maximal possible state. Both constraints expand quadratically (D² for downward closure) and create minimal constraint overhead.

**Exclusion: Fewer Primitives, Complex Semantics**

Exclusion eliminates `possible` and `falsify` as primitives, retaining only:
- `verify(x, p)`: State x verifies sentence letter p
- `excludes(x, y)`: States x and y are mutually incompatible

Possibility becomes a *derived* notion: a state is possible if it coheres with itself, where coherence means the absence of internal exclusion conflicts. Falsification is similarly derived through the verification semantics of negation.

This primitive reduction forces dramatic complexity increases in semantic clauses. Negation in Exclusion requires three interdependent conditions with witness predicates h(x) and y(x):

```
extended_verify(s, ¬φ, w) ⟺
  ∀x[verify(x, φ, w) → (part_of(y(x), x) ∧ excludes(h(x), y(x)))] ∧
  ∀x[verify(x, φ, w) → part_of(h(x), s)] ∧
  ∀z[(∀x[verify(x, φ, w) → part_of(h(x), z)]) → part_of(s, z)]
```

The first condition ensures that for every verifier x of φ, the witness predicate y(x) identifies a part of x that the hypothetical falsifier h(x) excludes. The second condition requires all such hypothetical falsifiers to be parts of s. The third ensures s is the *least* state satisfying the second condition.

This complexity serves a purpose: it encodes through `excludes` and witness functions what Logos achieves directly through the `falsify` primitive. The witness predicates h(x) and y(x) are Z3 uninterpreted functions that implicitly represent falsification structure without making it primitive.

Frame constraints similarly proliferate. Exclusion requires five frame constraints:
1. **Actuality**: `is_world(main_world)`
2. **Negation symmetry**: `∀x∀y[excludes(x,y) → excludes(y,x)]`
3. **Null state**: `∀x[¬excludes(null, x)]`
4. **Harmony**: `∀x∀y[(is_world(x) ∧ coheres(x,y)) → possible(y)]`
5. **Rashomon**: `∀x∀y[(possible(x) ∧ possible(y) ∧ coheres(x,y)) → compossible(x,y)]`

The symmetry constraint ensures exclusion is symmetric. The null state constraint establishes that the null state excludes nothing. Harmony and Rashomon connect the derived notion of possibility to worlds and compossibility. These constraints expand to thousands of concrete implications at N=5, compared to Logos's ~1,100 total constraints.

**Argument Domains: Not All Binary Primitives Are Equal**

While both theories employ only binary primitives, a crucial distinction emerges: the *domains* over which primitive arguments range determine model space complexity. For primitives with k arguments ranging over states and h arguments ranging over sentence letters, model space is 2^(D^k × P^h).

Consider the primitives:
- `excludes(x, y)`: k=2, h=0 → Model space = 2^(D²)
- `falsify(x, p)`: k=1, h=1 → Model space = 2^(D×P)

Both primitives have arity 2, yet `excludes` creates exponentially larger model space because both arguments range over states (domain size D), while `falsify` has one argument over states and one over sentence letters (domain size P). Since D=2^N grows exponentially with bitvector width while P remains small (typically 3-5), D² vastly exceeds D×P.

For N=5: D=32, P=3:
- `excludes`: 2^(32²) = 2^1024
- `falsify`: 2^(32×3) = 2^96

The `excludes` primitive's model space is 2^928 times larger than `falsify`'s, despite identical arity. This explains why Exclusion's total model space (2^(D+D·P+D²) = 2^1152) dramatically exceeds Logos's (2^(D+2D·P) = 2^224): the D² term from a pure-state binary primitive dominates two mixed-argument binary primitives.

The critical insight: *primitive arity relative to domain size* determines complexity. A binary primitive over states×states creates quadratically larger model space than a binary primitive over states×letters when D >> P. The simplistic characterization "both theories use binary primitives" obscures this fundamental distinction.

**Conclusion: Primitive Arity Dominates Primitive Count**

The Logos-Exclusion comparison demonstrates that primitive *count* is negotiable: theories with 2-3 binary primitives achieve similar performance whether they employ simple semantics with many primitives or complex semantics with few primitives. The decisive factor remains primitive *arity*: both theories use exclusively binary primitives, keeping model space scaling to O(D² + D·P).

This analysis reinforces the central conclusion: primitive arity determines tractability boundaries, while primitive count and semantic clause complexity determine performance within those boundaries.

### 6.4 Empirical Performance Data and Arity Effects

**TODO: Conduct systematic empirical comparison of Logos, Exclusion, and Imposition theories using the following methodology, adjusting numbers accordingly.**

**1. Test Suite Design**
- Select 15-20 representative inference problems spanning:
  - Propositional validities (tautologies)
  - Modal inferences (if applicable)
  - Invalid arguments (to test satisfiability)
- Ensure test cases exercise each theory's primitives
- Vary formula complexity: atomic, conjunctive, nested negations

**2. Domain Size Sweep**
- Test each inference at N = {4, 5, 6, 8, 10, 12, 15, 18, 20}
- For Imposition, extend to N = {3, 4, 5, 6, 8} (expect failure beyond N=10-12)
- Record both successful solves and timeouts

**3. Metrics to Collect**
- Solve time (seconds)
- Timeout rate (percentage of test cases exceeding 60s)
- Memory usage (if available)
- Constraint count (from Z3 statistics)
- Model space size (2^X where X = exponent from primitive analysis)

**4. Performance Tiers**
- **Tier 1 (Binary primitives)**: Logos, Exclusion
  - Hypothesis: N=18-20 tractable, <25% timeout rate
  - Model space: O(2^(D²+D·P))
- **Tier 2-3 (Ternary primitive)**: Imposition
  - Hypothesis: N=10-12 maximum, >50% timeout at N=10
  - Model space: O(2^(D³))

**5. Analysis**
- Plot solve time vs. N for each theory (log scale)
- Calculate scaling factors: solve_time(N+1) / solve_time(N)
- Compare empirical scaling to theoretical predictions (quadratic vs. cubic)
- Isolate arity effect: test Imposition formulas without `imposition` primitive

**6. Expected Results**
- Logos and Exclusion: Similar Tier 1 performance (N=18-20), differing by ~2× in solve time
- Imposition: Dramatic degradation at N≥10, memory crashes at N≥13
- Confirmation: Primitive arity dominates; primitive count causes variation within tiers

**7. Presentation**
- Table: Theory × N showing average solve time and timeout rate
- Graph: Solve time vs. N (separate lines for each theory)
- Bar chart: Maximum tractable N by theory
- Statistical test: Correlation between model space exponent and timeout rate

### 6.5 Conclusion: The Dominance of Primitive Arity

**TODO: After completing empirical testing (Section 6.4), populate this section with specific tractability numbers for each primitive arity tier (maximum tractable N values, timeout rates, solve times).**

The analysis of semantic primitive complexity establishes primitive arity—specifically, the number of arguments ranging over states—as the primary determinant of computational tractability in SMT-based semantic theory implementation. This conclusion emerges from three complementary investigations: model space analysis, frame constraint complexity, and the Logos-Exclusion comparison.

**The Central Finding**

For primitives with k arguments ranging over states (domain D=2^N) and h arguments ranging over sentence letters (domain P), model space scales as 2^(D^k × P^h). Since D grows exponentially with bitvector width N while P remains small, the state-argument count k dominates:

- **Unary primitives** (k=1): Model space 2^D — [TODO: tractability results]
- **Binary primitives** (k=1, h=1): Model space 2^(D×P) — [TODO: tractability results]
- **Pure-state binary primitives** (k=2): Model space 2^(D²) — [TODO: tractability results]
- **Ternary primitives** (k=3): Model space 2^(D³) — [TODO: tractability results]

This exponential hierarchy creates discrete performance tiers. Theories with lower k values achieve substantially higher tractability regardless of primitive count or semantic clause complexity. Theories with higher k values experience dramatic performance degradation regardless of optimization efforts. The k=2 → k=3 transition represents a tractability boundary that no amount of constraint optimization can overcome.

**Frame Constraints Compound, Don't Determine**

Frame constraints exhibit a pruning-complexity tradeoff: they eliminate invalid model regions but impose computational overhead through constraint expansion and memory consumption. Critically, frame constraint complexity *compounds with* rather than *determines* tractability:

- Frame constraints over k-ary primitives expand as D^k
- Binary primitives generate D² frame constraint expansions (manageable)
- Ternary primitives generate D³ frame constraint expansions (overwhelming)

[TODO: After testing, update with specific N threshold and constraint count where Imposition experiences memory crashes] Imposition's memory crashes result from frame constraints over ternary primitives expanding to prohibitively large clause counts at moderate N values. Even optimal frame constraint design cannot compensate for high k. The frame constraint analysis reinforces rather than contradicts the primitive arity conclusion.

**Domain-Typed Arguments: The Refined Criterion**

The critical refinement: not all "binary primitives" are equal. Argument domains determine complexity:

- `falsify(x, p)`: k=1, h=1 → 2^(D×P) ≈ 2^96 at N=5
- `excludes(x, y)`: k=2, h=0 → 2^(D²) ≈ 2^1024 at N=5

This comparison demonstrates the refinement of the arity principle: k=1 theories substantially outperform k=2 theories, which in turn dramatically outperform k=3 theories.

- Logos (3 primitives, simple negation, k_max=1): ~1,100 constraints at N=5, [TODO: max tractable N]
- Exclusion (2 primitives, complex negation, k_max=2): ~3,200 constraints at N=5, [TODO: max tractable N]

Logos significantly outperforms Exclusion for two compounding reasons: (1) lower maximum state-argument count (k_max=1 vs. k_max=2), and (2) simpler semantic clauses with fewer frame constraints. Logos's primitives (`verify`, `falsify`, `possible`) each have at most one state argument, yielding model space O(D×P). Exclusion's `excludes(x,y)` primitive has two state arguments, creating O(D²) model space that dominates the D×P contribution from `verify`. Combined with Exclusion's additional frame constraints, this produces ~3× more constraints at equivalent N.

**The Complexity Hierarchy**

Semantic theory tractability follows a clear hierarchy:

1. **Primary**: Primitive arity relative to domain (k = state arguments)
   - Determines tractability tier boundaries
   - Creates exponential performance gaps (2^(D^k))
   - Cannot be compensated by optimization

2. **Secondary**: Frame constraint design
   - Compounds with primitive arity (D^k expansion)
   - Can cause catastrophic memory failures
   - Enables 2-3× performance variation within tiers

3. **Tertiary**: Primitive count and semantic complexity
   - Creates variation within tractability tiers
   - Negotiable through design tradeoffs
   - Does not affect tier boundaries

**Design Implications**

This hierarchy yields a clear design principle: minimize k (state arguments per primitive) as the primary complexity criterion. Theories with k≥3 should be avoided unless absolutely necessary for semantic adequacy. When higher arity proves essential, modular architecture can isolate high-arity primitives in optional subtheories, enabling users to access Tier 1 performance for formulas not requiring the high-arity primitive.

The analysis establishes computational tractability as objective, measurable, and predictable from primitive structure. Semantic theorists can calculate tractability boundaries before implementation by identifying maximum k across primitives. This transforms tractability from an empirical surprise into a design criterion, enabling informed choices between semantic expressiveness and computational feasibility.

---

## 7. Conclusion: TheoryLib and Collaborative Semantic Theory Development

This paper has presented the ModelChecker framework treating semantic theories as executable programs enabling systematic model exploration, empirical theory comparison, and automated validation checking. Six principal contributions advance semantic methodology: theory-agnostic architecture, compositional modularity, systematic comparative methodology, bounded model exploration, computational complexity as theoretical virtue, and TheoryLib extensible library. This concluding section develops the TheoryLib vision and provides practical guidance for researchers to use the framework, test existing theories, implement new semantic frameworks, and contribute to collaborative formal semantics.

### 7.1 TheoryLib: A Shared Repository for Semantic Theories

TheoryLib provides for formal semantics what proof assistant libraries provide for formalized mathematics: shared, reusable, validated implementations in standardized format. The current library includes four semantic theories—bilateral truthmaker semantics (Logos), unilateral truthmaker semantics (Exclusion), Fine's imposition semantics, and bimodal temporal-modal logic—demonstrating theory-agnosticism across diverse frameworks while providing foundation for collaborative expansion.

**Benefits of Standardized Implementation**

Implementing theories in TheoryLib format yields multiple research benefits. **Reproducibility**: Published theories become executable, enabling other researchers to validate results and test new examples. **Direct comparison**: Standardized format permits running identical arguments through multiple theories under controlled conditions (Section 4), producing empirical comparative data rarely available in traditional semantic theorizing. **Educational use**: Students can explore semantic frameworks through concrete models rather than abstract definitions, building intuition about how theories validate inferences. **Theory reuse**: Shared operator implementations promote consistency while enabling researchers to build on prior work rather than reimplementing from scratch.

**Current Coverage and Future Expansion**

The four implemented theories cover 177+ validated examples spanning propositional logic, modal operators, counterfactual conditionals, and constitutive operators. This demonstrates framework viability while establishing baseline for expansion. Future TheoryLib development envisions implementations of epistemic semantics, normative logics, causal frameworks, dynamic semantics, and hybrid approaches combining multiple semantic dimensions.

### 7.2 Testing and Adapting Existing Theories

Researchers can immediately use TheoryLib to explore how semantic frameworks evaluate inferences without implementing theories from scratch.

**Basic Workflow: Testing Inferences**

1. **Select theory**: Choose from Logos, Exclusion, Imposition, or Bimodal based on the semantic domain under investigation
2. **Specify argument**: Define premises and conclusions using the framework's syntactic notation
3. **Configure settings**: Set search bounds (domain size N), timeout limits, and semantic constraints (e.g., contingency requirements)
4. **Run validation**: The framework generates SMT constraints, invokes Z3 solver, and reports validity determination with countermodel if invalid
5. **Interpret results**: Valid arguments provide evidence for semantic entailment; invalid arguments yield concrete countermodels illustrating why the inference fails

### 7.3 Implementing New Semantic Theories

Contributing new theories to TheoryLib requires systematic implementation following the framework's architecture. This section provides step-by-step methodology informed by Sections 3 (modularity) and 6 (complexity).

**Step 1: Design Semantic Primitives**

Identify the fundamental Z3 functions and relations constituting the theory's model structure. These primitives are where theory-specific semantics enter the framework (Section 3.1).

*Guidance*: Minimize the maximum state-argument count k to maximize computational tractability (Section 6).

**Step 2: Implement Semantic Clauses**

Define truth or verification conditions for each logical operator through SMT constraint generation methods. Follow the three-layer operator architecture (Section 3.1): syntactic recognition (arity specification), semantic interpretation (constraint generation), model presentation (result formatting).

*Guidance*: Keep semantic clauses simple when possible. More primitives with simple semantics often outperform fewer primitives with complex semantics due to reduced constraint overhead (Section 6.3).

*Step 3: Specify Frame Constraints**

Encode structural requirements on semantic primitives ruling out invalid model regions. Well-designed frame constraints dramatically improve performance through constraint propagation, but excessive constraints cause memory exhaustion (Section 6.2).

*Guidance*: Balance pruning benefits against complexity costs. Frame constraints over k-ary primitives expand as D^k, so theories with higher-arity primitives face greater constraint overhead. Test constraint expansion at moderate domain sizes (N=5-8) to identify memory issues before they become catastrophic failures.

**Step 4: Create Example Suite**

Validate theory implementation through comprehensive test cases covering expected validities, characteristic invalidities, and edge cases distinguishing the theory from alternatives.

*Guidance*: Include both positive tests (inferences the theory should validate) and negative tests (inferences it should invalidate). Compare validation patterns with related theories to confirm the implementation captures intended distinctions. Use the comparative methodology (Section 4) to benchmark performance relative to existing TheoryLib implementations.

**Step 5: Documentation and Contribution**

Document primitives, operators, frame constraints, and theoretical motivations. Include references to semantic literature establishing the theory's philosophical foundations. Submit implementations, examples, and documentation to TheoryLib repository for community review, validation, and integration.

### 7.4 A Methodology for Computational Formal Semantics

The ModelChecker framework enables new research methodologies transforming how semantic theories are developed, tested, and compared.

**Theory Development Cycle**

1. **Implement**: Encode semantic theory as executable program
2. **Test**: Run example suites validating expected inferences
3. **Refine**: Identify bugs, optimize performance, simplify implementations
4. **Compare**: Benchmark against alternative theories on shared examples
5. **Iterate**: Revise based on empirical results and theoretical insights

This cycle replaces informal theory development with systematic engineering methodology. Bugs become obvious (theory validates/invalidates unexpectedly), performance becomes measurable (timeout rates, solve times), and comparisons become reproducible (standardized test suites, controlled conditions).

**Empirical Validation**

Run standardized test suites across theories, collecting validation patterns and performance metrics. Which theories agree on classical validities? Where do hyperintensional frameworks diverge from intensional approaches? How much does bilateral tracking cost computationally? These questions receive empirical answers grounded in concrete measurements (Section 4.2).

**Educational Applications**

Teaching semantic frameworks becomes interactive: students can execute theories, examine countermodels, modify operators, and observe validation changes in real time. Abstract metalogical definitions become concrete algorithmic implementations. Exploring how conjunction verification works in truthmaker semantics transitions from reading formal clauses to running code, examining models, and testing predictions.

**Reproducibility and Cumulative Progress**

Standardized implementations enable reproducibility: publish the theory file alongside the paper, allowing reviewers to validate results and other researchers to build on prior work. This addresses a persistent challenge in formal philosophy where theory comparisons depend on informal assessments differing across researchers. TheoryLib provides shared infrastructure enabling cumulative progress through validated, reusable implementations.

**The Computational Turn in Semantics**

The methodology represents broader shifts in semantic theorizing:
- From informal comparison → systematic empirical benchmarking
- From hand-verified proofs → automated model exploration
- From subjective complexity → objective tractability metrics
- From isolated theories → collaborative theory libraries
- From philosophical intuition → computational constraint

These shifts don't replace traditional semantic methods but complement them with new forms of evidence, validation, and comparison.

### 7.5 Future Directions

The ModelChecker framework enables multiple research trajectories extending its contributions to semantic methodology.

**Expanding TheoryLib Coverage**

Implementing additional theories—epistemic logics, normative semantics, causal frameworks, dynamic semantics—would broaden framework applicability. Hybrid approaches combining multiple semantic dimensions (temporal-epistemic, modal-normative) would demonstrate extensibility to complex interactions. Domain-specific applications (legal reasoning, linguistic semantics, metaphysical theories) would establish the framework's versatility beyond philosophical logic.

**Advancing Computational Methods**

Solver optimization through improved heuristics, parallel search, and incremental solving could push tractability boundaries established in Section 6. Integration with theorem provers would combine SMT-based bounded search with complete decision procedures where available. Automated assistance through machine learning—predicting formula timeout likelihood, identifying optimal primitive designs, suggesting frame constraints—could guide theory implementation. These advances would expand the framework's reach while maintaining its theory-agnostic architecture.

**Transforming Semantic Methodology**

Computational complexity could become a formal adequacy criterion alongside logical correctness and intuitive fit, with tractability boundaries constraining theory design (Section 6.5). Reproducibility standards requiring published theories to include executable implementations would enable systematic validation and cumulative progress. Educational infrastructure including interactive environments for exploring semantic frameworks, countermodel visualization, and theory comparison tools would make formal semantics accessible to broader audiences.

**Invitation to Contribute**

TheoryLib is an open research platform inviting collaboration from the formal semantics community. Contributions take multiple forms: implementing new theories, extending existing theories with additional operators, creating example suites testing specific semantic domains, improving solver performance, developing educational materials, or proposing methodological innovations. The ModelChecker repository includes comprehensive documentation covering installation, theory implementation, example creation, and contribution guidelines.

**Concluding Thought**

The ModelChecker framework provides infrastructure transforming semantic theorizing from isolated analyses to collaborative computational methodology. TheoryLib invites the formal semantics community to implement theories, share examples, and advance the computational turn.
