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

*The Comparison Problem**

Semantic theorists frequently propose alternative frameworks claiming to better capture some semantic domain. Comparing theories is typically informal, relying on judgments of theoretical parsimony. Without empirical metrics, theory choice often reflects subjective assessments of elegance or intuitive fit rather than systematic benchmarking that compares semantic theories on standardized inputs to measure comparative performance.

**The Tractability Problem**

Some semantic theories are computationally demanding. Others are much more tractable, yielding efficiently solvable constraints. Traditional semantic theorizing treats computational complexity as an implementation detail, external to semantic concerns. We argue that computational complexity should inform semantic theory development, taking computability to be a theoretical virtue that can be measured and used to guide theory choice.

### 1.2 The Computational Turn in Semantics

SMT solvers, originally developed for program verification, provide powerful engines for constraint satisfaction over complex mathematical structures. Applying SMT technology to semantic theory development is a natural extension: semantic models are mathematical structures; semantic theories specify constraints over these structures; SMT solvers find assignments satisfying constraints.

**Prior Computational Approaches**

Several research programs have explored computational approaches to semantic theory:

- **Automated theorem proving for modal logic**: Provers for modal logics exist, but typically target specific well-studied systems (S4, S5) rather than providing frameworks for implementing arbitrary semantic theories.

- **Model checking for temporal logics**: Bounded model checking techniques from formal verification could apply to semantic theories, but remain theory specific.

- **General-purpose automated reasoning tools**: Systems like Prover9 (theorem prover) and Mace4 (finite model finder) provide powerful first-order reasoning capabilities. While these tools can encode semantic theories in first-order logic, they lack semantic-theory-specific infrastructure: no native support for semantic clause specifications, no operator modularity, no comparative framework for testing multiple theories on shared examples.

**The Gap: Theory-Agnostic Semantic Frameworks**

What's missing is a theory-agnostic framework enabling researchers to implement diverse semantic theories, test them on shared examples, and compare their validation patterns and computational characteristics systematically. Whereas existing tools target specific logics and focus on theorem proving, we need infrastructure supporting arbitrary semantic frameworks in order to explore the space of countermodels for invalid inferences. Instead of treating theories individually, we need systematic comparative methodology to enhance theory selection. Moreover, pure first-order encodings can be cumbersome for semantic structures. By contrast, SMT solvers that support bitvectors for state spaces, uninterpreted functions for semantic relations, and arithmetic for cardinality constraints provide more natural and efficient representations.

**TODO**: Expand with specific recent projects in computational philosophy/automated reasoning, identifying their scope and limitations relative to our approach.

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

Section 2 presents the ModelChecker architecture: input processing, logical pipeline, and output generation (2.1); operator modularity and three-layer architecture (2.2); configurable constraints and model discovery (2.3). Section 3 examines modularity and extensibility in detail. Section 4 develops the arity-complexity thesis with empirical validation. Section 5 discusses finite model methodology and epistemic limitations. Section 6 presents the TheoryLib vision and contribution model. Section 7 provides a detailed case study of Logos theory implementation. Section 8 reports empirical results and theory comparisons. Section 9 reviews related work. Section 10 concludes with future directions and broader impact.

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

## 4 Configurable Semantic Constraints and Model Discovery

Semantic theories make diverse assumptions about model structure: some require propositions to be contingent, others permit necessary truths; some demand disjoint subject-matters, others allow overlap. The framework addresses this diversity through configurable semantic constraints. This section examines how constraint configuration enables precise model control to assist exploration.

### 4.1 Hierarchical Configuration and Research Flexibility

The framework implements a multi-level configuration hierarchy balancing global defaults with local overrides. This design assists research by providing different levels of control depending for flexibility and ease of use.

**Configuration Hierarchy as Research Tool**

At the broadest level, framework-wide defaults ensure sensible baseline behavior. Theory-specific defaults capture semantic assumptions distinctive to particular frameworks. User-level preferences enable researchers to establish their own working assumptions. Example-level settings permit fine-grained control for specific test cases. Command-line flags provide immediate overrides.

This hierarchy allows researchers to restrict the space of models while remaining flexible. Global defaults ensure reproducibility and comparability across experiments. Local overrides enable exploring variations without modifying core configurations. The architecture makes the distinction between standing assumptions and temporary variations explicit in the configuration structure.

**Methodological Significance**

The hierarchical design has methodological implications beyond mere convenience. It distinguishes theory-constitutive constraints (embedded in semantic implementations) from investigative constraints (imposed by researchers exploring consequences).

### 4.2 Constraint Composition and Interaction

Constraints compose: requiring both contingency and disjointness yields models satisfying both conditions. But constraints also interact: contingency implies non-emptiness (contingent propositions must have verifiers and falsifiers), so redundant constraints can be omitted. The framework handles these interactions, applying only the minimal constraint set expressing the desired conditions.

This compositional approach mirrors theoretical practice. Semantic theorists often build up model requirements incrementally: start with basic structural requirements, add contingency, impose subject-matter constraints. The framework's constraint composition enables the same incremental specification, with each addition narrowing the model space explored.

### 4.3 Systematic Cross-Theory Comparison

A persistent challenge in semantic theory development is comparison in order to determine how different frameworks fare on identical test cases or which theory is simpler than the other. Traditional comparison is informal and unsystematic. The ModelChecker enables systematic empirical comparison by running identical examples through multiple theories while measuring computational costs.

**Comparative Methodology**

When multiple theories are provided, the framework evaluates each theory on the same argument with identical settings, measuring both validation outcomes and computational costs. This produces concrete, reproducible comparative data replacing subjective assessments of theory complexity.

The methodology controls for discrepancies in test conditions so that differences in outcomes or performance reflect genuine theoretical differences rather than variations in test conditions. Experimental measures are not provided by traditional semantic theorizing which rely on manual proofs.

**Empirical Complexity Metrics**

Evaluating examples with multiple theories yields empirical complexity data: which theories timeout on which examples, which scale to larger state spaces, which validate or invalidate particular patterns. These metrics complement traditional theoretical complexity analysis with empirical performance data.

Whereas theoretical complexity (quantifier alternation, primitive arity) predicts computational costs, empirical performance measures actual cost. Sometimes they align, sometimes they diverge (optimizations, solver heuristics). The framework provides both. [Section 5] develops a theoretical complexity analysis that builds on the empirical measurement methodology provided here.

### 4.4 Countermodel Discovery and Semantic Diversity

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

**Two-Stage Isomorphism Checking**

Full graph isomorphism is computationally expensive. The framework employs a two-stage strategy: quick structural checks (node count, edge count, degree sequences) cheaply reject most non-isomorphic models; expensive full isomorphism checking runs only when cheap checks pass. This optimizes for the common case while maintaining correctness.

The approach reflects a performance principle: spend computational effort proportionally to expected payoff. Most models will differ in basic structural properties (different numbers of worlds, different accessibility patterns). Full isomorphism checking is reserved for structurally similar models, reducing average-case cost.

**Methodological Applications**

Model iteration enables several research methodologies:

1. **Diversity assessment**: How rich is the countermodel space for this inference? Sparse countermodel spaces suggest the argument is "nearly valid"; rich spaces suggest deep invalidity.

2. **Structural comparison**: How do countermodel structures differ across theories? Do they share common patterns or exhibit fundamental differences?

3. **Minimal countermodels**: Iterate with increasing bounds to find smallest distinguishing models, revealing minimal structural requirements for counterexamples.

Each methodology leverages systematic countermodel exploration to address questions beyond simple validity testing, demonstrating how computational tools enable new forms of semantic investigation.

### 4.5 Termination and Search Space Boundaries

Model iteration raises a termination question: when should the search stop? Unlike validity checking (stop when countermodel found or search space exhausted), iteration could continue indefinitely seeking ever more countermodels. The framework employs multiple termination conditions reflecting different exhaustion scenarios.

**Termination Conditions**

Iteration terminates when: (1) the requested number of distinct models is found (successful completion), (2) timeout limits are reached (resource exhaustion), (3) the solver reports no more satisfying assignments exist (search space exhausted), or (4) consecutive isomorphism failures suggest we've found all non-isomorphic models in the accessible search space (heuristic exhaustion).

These conditions reflect different search outcomes. Successful completion means we found desired diversity. Resource exhaustion means computational limits constrained exploration. Search space exhaustion means we've found all countermodels within bounded space. Heuristic exhaustion suggests we've likely found all accessible distinct models given isomorphism clustering.

**Epistemic Status of Termination**

Each termination condition has different epistemic status. Successful completion: we have N distinct countermodels (definite within specified bounds). Resource exhaustion: countermodel space may be richer than explored (indefinite). Search space exhaustion within bounds: no more countermodels exist in bounded space (definite within bounded models). Heuristic exhaustion: likely found all accessible distinct models (supporting evidence).

The framework reports termination reasons, enabling users to interpret results. Finding 5 models then timing out means "at least 5 distinct countermodels exist"; finding 5 models then exhausting search space means "exactly 5 distinct countermodels exist within the bounded space of models." The distinction matters for theoretical conclusions drawn from iteration results.

## 5. Computational Complexity of Semantic Primitives and Arity

**Central Thesis**: Arity of semantic primitives directly determines computational tractability

### 5.1 Arity and Quantifier Complexity
- Unary functions: 1 quantifier (tractable)
- Binary functions/relations: 2 quantifiers (manageable)
- Ternary functions: 3 quantifiers (challenging)
- Quantifier alternation impact (hardest)

### 5.2 Theory Comparison by Primitive Arity
**Table**: Theories ranked by primitive complexity
- Classical: Unary/binary only - Fast
- Modal: Binary accessibility - Moderate
- Truthmaker: Binary verify/falsify - Moderate
- Imposition: Quaternary closeness - Slow

### 5.3 Constraint Structure and Primitive Interaction
Examples:
- Negation: Simple swap (no added quantifiers)
- Disjunction: Existential fusion (2 quantifiers)
- Necessity: Universal over worlds (1 quantifier + recursion)
- Counterfactual: Triple nesting + quaternary primitive (very expensive)

### 5.4 Empirical Performance by Arity
**Data**: Solve times and timeout rates by primitive arity

### 5.5 Optimization Strategies for High-Arity Primitives
- Currying: Reduce effective arity
- Lazy evaluation: Defer constraint generation
- Conditional loading: Only declare needed primitives

### 5.6 Theoretical Complexity Classification
**Complexity Hierarchy**:
- Class 1 (Fast): Arity ≤2, no alternation
- Class 2 (Moderate): Arity 3 or ∀∃ patterns
- Class 3 (Slow): Arity ≥4 or ∀∃∀ patterns

### 5.7 Design Principle: Minimize Arity
**Recommendation**: Prefer binary/unary primitives when designing theories

### 5.8 Case Study: Arity Impact on Logos Theory
- Binary truthmaking: Efficient core
- Counterfactuals: Performance bottleneck
- Optimization outcomes

### 5.9 Summary: Arity as Complexity Driver
Key findings:
- Arity predicts performance
- Quantifier structure matters
- Design implications for theorists

---

## 6. TheoryLib

### 6.1 Current Implementation (4 Theories)
1. **Logos**: Bilateral truthmaker semantics (19 operators)
2. **Exclusion**: Unilateral truthmaker semantics
3. **Imposition**: Fine's counterfactual theory
4. **Bimodal**: Temporal-modal logic

### 6.2 TheoryLib Architecture
- Standardized interfaces
- Shared infrastructure
- Theory registry
- Dependency management

### 6.3 Ambitions
- Community contributions
- Comparative benchmarking
- Citation and versioning
- Educational resources

---

## 7. Case Study: Logos Theory and Unified Hyperintensional Semantics

### 7.1 Truthmaker Semantics Foundations
 States as truthmakers
 Bilateral verification/falsification
 Hyperintensional distinctions

### 7.2 Operator Semantics: Five Subtheories

#### 1. Extensional Operators
- Negation, disjunction, conjunction
- Material conditional
- Truth/falsity constants

#### 2. Modal Operators
- Necessity and possibility
- Accessibility relations
- S4 modal logic

#### 3. Constitutive Operators
- Ground (d)
- Propositional identity (a)
- Essence operations

#### 4. Counterfactual Operators
- Would-counterfactual (□→)
- Might-counterfactual (◇→)
- Alternative world selection

#### 5. Relevance Operators
- Relevance implication (→c)
- Subject-matter overlap
- Meaningful connections

### 7.3 Empirical Validation and Test Suite

#### Example Categories (177 total)
- Extensional: 55 examples
- Modal: 35 examples
- Constitutive: 35 examples
- Counterfactual: 32 examples
- Relevance: 30 examples

#### Validation Process
- Each example tested
- Expected vs. actual results
- Bug detection

---

## 8. Discussion and Future Directions

### 8.1 Contributions Summary

#### Theoretical Contributions
1. First computational bilateral truthmaker semantics
2. Objective complexity metrics (arity-based)
3. Theory-agnostic methodology
4. Comparative analysis framework
5. Finite model exploration for hyperintensional logics

#### Practical Contributions
1. TheoryLib implementation
2. 4 theories, 177+ examples
3. Open source tooling
4. Modular architecture
5. Empirical validation methodology
6. Bug detection capabilities

### 8.2 Limitations and Challenges

#### Computational Limitations
1. **No Completeness**: Finite search limitations
   - Mitigation: Progressive search, confidence building

2. **Performance Constraints**: Large N timeouts
   - Mitigation: Optimization, incremental solving

#### Theoretical Limitations
1. **Undecidability**: Some logics have no decision procedure
   - Mitigation: Bounded fragments

2. **Expressiveness**: Some theories resist formalization
   - Mitigation: Approximations, careful design

#### Practical Limitations
1. **Learning Curve**: Z3 and theory implementation complexity
   - Mitigation: Documentation, examples

2. **Constraint Debugging**: Cryptic errors
   - Mitigation: Labeling, unsat cores
   - Future: Better debugging tools

### 8.3 Conclusion
 Recap main contributions
 Significance of computational approach
 TheoryLib vision
 Call for community engagement

