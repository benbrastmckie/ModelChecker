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

--- CONTINUE ---

## 2. ModelChecker Pipeline

### 2.1 Complete Pipeline Architecture

This section presents the conceptual architecture of the ModelChecker pipeline, which transforms logical arguments into validity determinations through three principal stages: input specification, logical processing, and result generation. Understanding this transformation is essential to grasping how the framework achieves theory-agnostic semantic evaluation.

#### 2.1.1 Input Specification and Configuration

The framework accepts logical arguments alongside semantic theory specifications, enabling systematic exploration of how different semantic frameworks evaluate identical inference patterns. This design decision—requiring both arguments and theories as input—reflects a core commitment: semantic theories should be executable programs that can be systematically compared on shared test cases.

**Argument Specification Design**

Each logical argument consists of premise formulas, conclusion formulas, and an optional configuration specifying model constraints. This structure mirrors standard logical notation while permitting precise control over the semantic search space. For example, constraining atomic propositions to be contingent (having both verifiers and falsifiers) filters out trivial models where propositions are necessarily true or false.

**Multi-Theory Comparison Architecture**

The input structure supports evaluating identical arguments across multiple semantic frameworks simultaneously. This enables direct empirical comparison: Given premises P and conclusion C, which theories validate the inference? How do computational costs differ? The comparative methodology addresses a longstanding challenge in semantic theory development—the lack of systematic empirical comparison methods.

**Configuration Hierarchy**

Settings follow a priority hierarchy where command-line flags override module-level specifications, which in turn override theory defaults. This design balances flexibility with sensible defaults: users can globally configure model size constraints while allowing individual examples to override these settings when needed. The hierarchy ensures predictable behavior while supporting diverse use cases from quick exploration to systematic benchmarking.

#### 2.1.2 Logical Processing Pipeline

The core transformation from symbolic formulas to validity determinations proceeds through four conceptual stages, each addressing a distinct aspect of the semantic evaluation problem.

**Stage 1: Syntactic Parsing**

Object-language formulas (e.g., "A ∧ B → C") must be transformed into structured representations amenable to semantic interpretation. The parser builds recursive sentence structures while remaining agnostic to operator semantics—it recognizes "∧" as a binary operator without knowing whether it represents classical conjunction, fusion, or some other operation. This separation between syntactic structure and semantic interpretation is fundamental to theory-agnosticism.

**Stage 2: Semantic Constraint Generation**

Each formula generates constraints in the SMT solver expressing what it means for that formula to be verified or falsified according to the chosen semantic theory. This translation from semantic metalanguage (the theory's truth/verification conditions) to SMT constraints is where theory-specific semantics enter the pipeline.

Four categories of constraints jointly specify the countermodel search problem:
1. **Frame constraints** encode the semantic structure (e.g., accessibility relations, mereological principles)
2. **Model constraints** ensure atomic propositions receive valid semantic values
3. **Premise constraints** require all premises to be satisfied
4. **Conclusion constraints** require conclusions to fail (the countermodel condition)

The combination forms a satisfiability problem: Does there exist a model satisfying the semantic framework's structural principles where premises are true but conclusions are not?

**Stage 3: SMT Solving**

The Z3 solver attempts to find a satisfying assignment to all constraints, bounded by user-specified timeouts and state-space size limits. This is bounded model checking for semantic theories: we search finite portions of the model space rather than attempting complete decision procedures. If the solver finds a satisfying assignment, it has discovered a countermodel. If no satisfying assignment exists within the bounded search, we gain evidence (though not proof) that the argument is valid.

**Stage 4: Model Iteration (Optional)**

When multiple countermodels are requested, the system iteratively excludes previously discovered models through additional constraints while checking for structural isomorphism to avoid presenting mere labelings of identical model structures. This exploration of countermodel diversity reveals the richness (or poverty) of the countermodel space for particular inferences.

**Isolation and Modularity**

A critical technical detail with conceptual significance: each argument evaluation occurs in an isolated solver context. This prevents constraint contamination between examples but, more importantly, reflects the philosophical principle that distinct arguments should receive independent semantic evaluation. The architecture enforces logical independence at the implementation level.

#### 2.1.3 Output Generation and Interpretation

The final stage transforms raw solver results into interpretable semantic information, with output formats tailored to different use cases.

**Validity Reporting**

For valid arguments (no countermodel found within search bounds), the system reports the search space explored. This qualified validity statement is epistemically honest: we have found no countermodel within a bounded search, providing evidence for but not proof of validity. As search bounds increase, confidence in genuine validity grows.

**Countermodel Visualization**

Invalid arguments yield countermodels displayed according to theory-specific conventions. A classical model shows atomic valuations; a modal model adds accessibility relations between worlds; a hyperintensional model displays state-based verification and falsification. The visualization adapts to the semantic primitives of the chosen theory.

**Comparative Analysis**

Comparison mode runs identical arguments through multiple theories, generating empirical data on how semantic frameworks differ in their validation patterns and computational costs. This produces the kind of systematic comparative data rarely available in traditional semantic theorizing: concrete, reproducible evidence of which theories validate which inferences and at what computational expense.

**Multiple Output Formats**

Different research activities require different output formats. Interactive console output supports rapid exploration; structured JSON enables programmatic analysis; Jupyter notebooks provide reproducible computational narratives. The framework recognizes that semantic research involves diverse workflows from initial exploration to formal publication.

**Pipeline Integration**

The three-stage architecture—input specification, constraint-based solving, and theory-specific output—achieves a crucial design goal: theory-agnostic infrastructure with theory-specific plugins. Core components (parsing, constraint solving, output management) operate independently of particular semantic frameworks, while theory modules provide the semantic interpretation that gives formal symbols their meaning. This separation enables the extensibility and systematic comparison that subsequent sections explore in detail.

### 2.2 Modularity Through Operator Classes

The framework's modularity emerges from a design principle: logical operators should be self-contained units that encapsulate syntactic recognition, semantic interpretation, and result presentation. This operator-centric architecture enables theory composition, selective loading, and systematic reuse across semantic frameworks. Understanding how operators bridge syntax, semantics, and models reveals the mechanism underlying the framework's extensibility.

#### 2.2.1 Three-Layer Operator Architecture

Logical operators in the framework simultaneously operate at three distinct conceptual levels, each addressing a different aspect of the semantic evaluation problem. This layered design enforces separation of concerns while maintaining compositional coherence.

**Layer 1: Syntactic Recognition (Theory-Independent)**

At the syntactic level, operators are purely structural entities characterized by their symbol, arity, and parsing behavior. A binary operator "∧" is recognized as requiring exactly two arguments and having specific precedence relationships, but nothing at this level specifies what conjunction *means*. This abstraction is what enables the same parser to handle classical, modal, hyperintensional, and temporal operators uniformly.

The critical innovation is that syntactic parsing proceeds without semantic knowledge. The parser builds recursive formula structures recognizing only operator arities and associativities, not their semantic interpretations. This means adding a new operator to a theory requires no modification to the parsing infrastructure—the parser recognizes any operator symbol meeting structural requirements.

Defined operators exemplify this separation: the material conditional can be treated syntactically as a primitive binary operator "→" while semantically being defined as "¬A ∨ B". The parser sees the structure; the semantic layer sees through the definition. This enables theoretical economy (fewer primitives) without sacrificing notational convenience.

**Layer 2: Semantic Interpretation (Theory-Specific Plugin)**

At the semantic level, operators implement methods translating informal semantic clauses into formal SMT constraints. This is where theory-specific semantics enter: a conjunction operator in classical logic implements different semantic methods than conjunction in hyperintensional truthmaker semantics, despite sharing syntactic structure.

Different semantic frameworks require different operator capabilities:
- **Intensional theories** require operators to specify truth conditions at evaluation points (worlds, times)
- **Bilateral theories** require independent specification of truth and falsity conditions
- **Hyperintensional theories** require verification and falsification conditions over partial states
- **All theories** require model extraction (translating solver assignments into readable semantic values)

This design accommodates semantic diversity: the framework does not impose a single semantic interface. Instead, operators implement whichever methods their semantic framework requires. Modal necessity implements truth-at-world methods; hyperintensional conjunction implements state-based verification methods. The framework adapts to the theory rather than forcing theories into a procrustean semantic template.

The evaluation point abstraction enables this flexibility. Rather than hardcoding "worlds" as evaluation points, the framework passes extensible dictionaries containing whatever semantic coordinates the theory requires: worlds for modal frameworks, world-time pairs for temporal frameworks, or more complex structures for hybrid systems. New semantic frameworks can introduce novel evaluation dimensions without modifying core infrastructure.

**Layer 3: Model Interpretation (Theory-Dependent Output)**

Once the solver produces a satisfying assignment, operators translate raw solver values into theory-appropriate semantic presentations. The same logical negation operator displays differently depending on the semantic framework: classical negation shows simple truth-value flips, while hyperintensional negation displays verifier-falsifier swaps at the state level.

This layer recognizes that semantic theories differ not just in their validation patterns but in how they conceptualize and present semantic information. The framework delegates presentation to operators because operators encapsulate semantic understanding. A counterfactual operator knows how to extract and display the alternative-world structures relevant to counterfactual semantics.

**Architectural Significance**

The three-layer architecture achieves theory-agnosticism through strategic abstraction points. Layers 1 and 3 (syntax and output) provide stable interfaces, while Layer 2 (semantics) serves as the plugin point where theory-specific interpretations enter. This design pattern—stable infrastructure with semantic plugins—recurs throughout the framework and enables the extensibility that subsequent sections explore.

#### 2.2.2 Subtheory Composition and Modular Loading

Semantic theories are not monolithic. Classical logic comprises connectives with distinct semantic behaviors; modal logic extends classical logic with intensional operators. The framework reflects this compositional structure through subtheory modules that can be selectively loaded and combined.

**Compositional Theory Design**

Rather than implementing theories as indivisible units, the framework treats them as compositions of operator subtheories. The Logos truthmaker framework, for instance, comprises five independent subtheories: extensional connectives, modal operators, constitutive operators, counterfactual conditionals, and relevance operators. Each subtheory can be loaded independently or in combination.

This modularity serves both practical and theoretical purposes. Practically, loading only required operators reduces the constraint set sent to the solver, improving performance. Theoretically, subtheory composition enables exploring "fragments" of semantic frameworks—what inferences does truthmaker semantics validate using only extensional operators versus including modal operators?

**Dependency Management**

Subtheories exhibit dependency relationships: modal operators are typically defined using extensional connectives; counterfactual operators may rely on both. The framework automatically resolves these dependencies, ensuring that loading a subtheory transitively loads all required dependencies. This enables users to request high-level operator sets while the system handles dependency graphs transparently.

The dependency structure also reveals semantic relationships. That modal operators depend on extensional operators reflects the standard semantic pattern where modal operators are defined using quantification over worlds where extensional operators apply. Dependency graphs thus encode semantic architectural decisions.

**Performance-Modularity Trade-off**

Modularity creates a performance optimization opportunity: fewer operators means fewer constraint variables and simpler search spaces. A user exploring purely extensional inferences can load only extensional operators, yielding significantly faster solving than loading the complete operator set. This demonstrates an important principle: semantic modularity translates directly into computational modularity.

The framework thus provides granular control over the theory-complexity-performance trade-off. Need comprehensive semantic coverage? Load all subtheories. Need fast iteration on specific fragments? Load minimal operator sets. The architecture makes this choice explicit and easy to modify.

#### 2.2.3 Semantic Framework Patterns and Operator Responsibilities

While operators are theory-specific plugins, certain patterns emerge across semantic frameworks. Understanding these patterns illuminates both the diversity and commonalities of formal semantic approaches.

**Intensional Semantics Pattern**

Intensional frameworks (modal, temporal, epistemic logics) share a common structure: operators define truth conditions relative to evaluation points in some structured space (possible worlds, times, epistemic states). Operators in these frameworks implement methods specifying truth-at-point conditions, typically involving quantification or relation-following through the evaluation space.

This pattern reflects a deep semantic commitment: meaning involves truth conditions across alternative scenarios. The framework accommodates this through evaluation-point-parameterized semantic methods, enabling operators to implement the "look at alternative points" semantic pattern that characterizes intensional logics.

**Bilateral Semantics Pattern**

Bilateral frameworks distinguish truth from falsity, allowing gaps or gluts. Operators must independently specify both truth and falsity conditions rather than defining falsity as negation of truth. Negation, paradigmatically, swaps truth and falsity conditions—an operation only meaningful in bilateral frameworks.

This semantic pattern challenges classical assumptions about the relationship between truth and falsity. The framework's support for independent truth/falsity methods enables exploring bilateral semantics computationally, testing whether bilateral distinctions affect validation patterns.

**Hyperintensional Semantics Pattern**

Hyperintensional frameworks (truthmaker semantics, situation semantics) evaluate formulas not at worlds but at partial states or situations. Operators implement verification and falsification methods that quantify over states, often with mereological structure (part-whole relations, fusion operations).

The key semantic innovation is *partiality*: formulas are verified or falsified by states that might be partial, representing fragmentary information. Conjunction, for instance, is verified by fusing the verifier states of its conjuncts. This semantic pattern enables hyperintensional distinctions between necessarily equivalent formulas based on their verification structure.

**Defined Operator Abstraction**

Some operators are not semantically primitive but defined in terms of others. The material conditional is standardly defined as "¬A ∨ B". Such operators need no semantic methods—they expand to their definitions before semantic evaluation. This enables notational richness without semantic complexity: users can write familiar notation while the system works with semantic primitives.

The framework thus distinguishes semantic from notational complexity. Defined operators have zero semantic cost (they disappear during semantic evaluation) while providing ergonomic benefits. This reflects sound design: separate the interface users interact with from the semantic machinery that performs evaluation.

**Implications for Theory Design**

These patterns suggest design principles for implementing semantic theories: Identify core semantic primitives, implement their semantic methods, define convenient abbreviations as derived operators. The framework's architecture encourages this separation, rewarding clean semantic design with improved performance and maintainability. Theories with fewer, simpler semantic primitives yield faster, more reliable implementations—a computational pressure toward semantic parsimony.

### 2.3 Configurable Semantic Constraints and Model Discovery

Semantic theories make diverse assumptions about model structure: some require propositions to be contingent, others permit necessary truths; some demand disjoint subject-matters, others allow overlap. The framework addresses this diversity through configurable semantic constraints that are enforced computationally rather than stipulated informally. This section examines how constraint configuration enables both precise model control and systematic countermodel exploration.

#### 2.3.1 Hierarchical Configuration and Research Flexibility

The framework implements a multi-level configuration hierarchy balancing global defaults with local overrides. This design reflects a methodological insight: semantic research involves different granularities of control depending on context.

**Configuration Hierarchy as Research Tool**

At the broadest level, framework-wide defaults ensure sensible baseline behavior. Theory-specific defaults capture semantic assumptions distinctive to particular frameworks—truthmaker semantics might default to requiring contingent propositions while classical logic does not. User-level preferences enable researchers to establish their own working assumptions. Example-level settings permit fine-grained control for specific test cases. Command-line flags provide immediate overrides for exploratory queries.

This hierarchy addresses a practical problem in semantic research: how to balance consistency with flexibility. Global defaults ensure reproducibility and comparability across experiments. Local overrides enable exploring variations without modifying core configurations. The architecture makes the distinction between standing assumptions and temporary variations explicit in the configuration structure itself.

**Methodological Significance**

The hierarchical design has methodological implications beyond mere convenience. It distinguishes theory-constitutive constraints (embedded in semantic implementations) from investigative constraints (imposed by researchers exploring consequences). A truthmaker theory might constitutively require state-based verification; a researcher might additionally investigate what follows if we require contingency. The configuration system makes this distinction computationally precise.

#### 2.3.2 Semantic Constraints as Computational Enforcements

Traditional semantic theorizing often leaves model constraints informal: "assume propositions are contingent," "suppose subject-matters are disjoint." The framework makes such constraints computationally explicit, enforcing them through SMT constraints rather than stipulating them in natural language.

**Computational vs. Informal Constraints**

The difference is significant. Informal constraints require human discipline to maintain—it's easy to accidentally consider models violating unstated assumptions. Computational constraints are enforced by the solver: models violating the constraints simply cannot be found. This shifts semantic assumptions from informal guidelines to formal requirements.

Consider contingency: requiring that atomic propositions have both possible verifiers and possible falsifiers. Informally, this requires checking each model manually. Computationally, the solver only returns models satisfying the contingency constraints. The semantic assumption becomes part of the search specification rather than a post-hoc filter.

**Types of Semantic Constraints**

The framework supports several categories of semantic constraints, each enforcing different theoretical commitments:

- **Search space bounds** control the size of semantic structures explored (state space size, timeout limits)
- **Logical property constraints** enforce modal characteristics (contingency, necessity, possibility)
- **Structural constraints** impose mereological requirements (non-null states, non-empty valuations)
- **Semantic separation constraints** require independence (disjoint verifier/falsifier sets, distinct subject-matters)

Each constraint category translates theoretical assumptions into solver requirements, making implicit commitments explicit and computationally enforceable.

**Constraint Composition and Interaction**

Constraints compose: requiring both contingency and disjointness yields models satisfying both conditions. But constraints also interact: contingency implies non-emptiness (contingent propositions must have verifiers and falsifiers), so redundant constraints can be omitted. The framework handles these interactions, applying only the minimal constraint set expressing the desired conditions.

This compositional approach mirrors theoretical practice. Semantic theorists often build up model requirements incrementally: start with basic structural requirements, add contingency, impose subject-matter constraints. The framework's constraint composition enables the same incremental specification, with each addition narrowing the model space explored.

#### 2.3.3 Systematic Cross-Theory Comparison

A persistent challenge in semantic theory development is comparison: How do different frameworks fare on identical test cases? Which theories handle complexity better? Traditional comparison is informal and unsystematic. The framework enables systematic empirical comparison by running identical examples through multiple theories under controlled conditions.

**Comparative Methodology**

The comparison mode tests each theory on the same argument with identical settings, measuring both validation outcomes (which theories validate the inference?) and computational costs (how long did each theory take?). This produces concrete, reproducible comparative data replacing informal assessments like "theory X seems more complex than theory Y."

The methodology controls for confounds: same argument structure, same search bounds, same semantic constraints (when applicable). Differences in outcomes or performance reflect genuine theoretical differences rather than variations in test conditions. This experimental control is rarely achievable in traditional semantic theorizing.

**Empirical Complexity Metrics**

Comparison yields empirical complexity data: which theories timeout on which examples, which scale to larger state spaces, which validate or invalidate particular patterns. These metrics complement traditional theoretical complexity analysis with empirical performance data.

The distinction matters. Theoretical complexity (quantifier alternation, primitive arity) predicts computational cost; empirical performance measures actual cost. Sometimes they align, sometimes they diverge (optimizations, solver heuristics). The framework provides both: Section 4 develops theoretical complexity analysis, this section provides the empirical measurement methodology.

#### 2.3.4 Countermodel Discovery and Semantic Diversity

Finding a single countermodel establishes invalidity. But how many structurally distinct countermodels exist? Is the countermodel space rich or sparse? Exploring countermodel diversity reveals semantic properties invisible from single-model examination.

**The Model Iteration Problem**

Naively requesting multiple countermodels risks redundancy: the solver might return the same model structure with different variable assignments (world w₁ becomes w₂, etc.). Such label variants are structurally identical—they represent the same countermodel under different naming schemes. Meaningful diversity requires structural distinctness, not mere label variation.

This is the model iteration problem: how to systematically explore structurally distinct countermodels while avoiding label variants. The framework addresses this through iterative constraint-based exclusion combined with graph isomorphism detection.

**Constraint-Based Model Exclusion**

The core strategy is incremental: find one countermodel, add constraints excluding it, find another, add exclusion constraints, repeat. Each iteration narrows the search space by excluding previously discovered models while maintaining the original semantic requirements.

This approach has theoretical elegance: model exclusion is itself expressed as constraints, so the iteration process works within the same constraint-satisfaction framework used for initial discovery. We're not switching paradigms (from solving to enumeration); we're incrementally refining constraints to explore the solution space systematically.

**The Isomorphism Challenge**

But constraint-based exclusion alone is insufficient. Excluding a specific variable assignment doesn't exclude isomorphic variants—models with identical structure but different variable bindings. Without isomorphism detection, iteration might return infinitely many label variants of the same structural model.

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

#### 2.3.5 Termination and Search Space Boundaries

Model iteration raises a termination question: when should the search stop? Unlike validity checking (stop when countermodel found or search space exhausted), iteration could continue indefinitely seeking ever more countermodels. The framework employs multiple termination conditions reflecting different exhaustion scenarios.

**Termination Conditions**

Iteration terminates when: (1) the requested number of distinct models is found (successful completion), (2) timeout limits are reached (resource exhaustion), (3) the solver reports no more satisfying assignments exist (search space exhausted), or (4) consecutive isomorphism failures suggest we've found all non-isomorphic models in the accessible search space (heuristic exhaustion).

These conditions reflect different search outcomes. Successful completion means we found desired diversity. Resource exhaustion means computational limits constrained exploration. Search space exhaustion means we've found all countermodels within bounded space. Heuristic exhaustion suggests we've likely found all accessible distinct models given isomorphism clustering.

**Epistemic Status of Termination**

Each termination condition has different epistemic status. Successful completion: we have N distinct countermodels (definite). Resource exhaustion: countermodel space may be richer than explored (indefinite). Search space exhaustion within bounds: no more countermodels exist in bounded space (definite within bounds). Heuristic exhaustion: likely found all accessible distinct models (probabilistic).

The framework reports termination reasons, enabling users to interpret results epistemically. Finding 5 models then timing out means "at least 5 distinct countermodels exist"; finding 5 models then exhausting search space means "exactly 5 distinct countermodels exist within these bounds." The distinction matters for theoretical conclusions drawn from iteration results.


## 3. Modularity, Extensibility, and Systematic Theory Comparison

### 3.1 Theory-Agnostic Core Framework

#### Separation of Concerns Architecture
- Core abstractions independent of theories
- Plugin system for semantic implementations
- Benefits:
  - Implement new theories without core changes
  - Reuse infrastructure
  - Systematic comparison

### 3.2 Modular Operator Registry System
- Selective operator loading
- Subtheory composition
- Dependency resolution
- Example: Load only extensional, extensional+modal, or all operators

### 3.3 Systematic Comparative Analysis

#### Same Input, Multiple Theories
- Identical examples across frameworks
- Parallel evaluation
- Result comparison

#### Translation Mechanism
- Symbol mapping between theories
- Example: Logos � vs. Exclusion -

#### Comparative Results Database
- Structured output
- Divergence identification

### 3.4 Extensibility Dimensions
1. New operators in existing theories
2. New semantic theories
3. New semantic frameworks
4. New output formats
5. New solvers (beyond Z3)

---

## 4. Computational Complexity of Semantic Primitives and Arity

**Central Thesis**: Arity of semantic primitives directly determines computational tractability

### 4.1 Arity and Quantifier Complexity
- Unary functions: 1 quantifier (tractable)
- Binary functions/relations: 2 quantifiers (manageable)
- Ternary functions: 3 quantifiers (challenging)
- Quantifier alternation impact (hardest)

### 4.2 Theory Comparison by Primitive Arity
**Table**: Theories ranked by primitive complexity
- Classical: Unary/binary only - Fast
- Modal: Binary accessibility - Moderate
- Truthmaker: Binary verify/falsify - Moderate
- Imposition: Quaternary closeness - Slow

### 4.3 Constraint Structure and Primitive Interaction
Examples:
- Negation: Simple swap (no added quantifiers)
- Disjunction: Existential fusion (2 quantifiers)
- Necessity: Universal over worlds (1 quantifier + recursion)
- Counterfactual: Triple nesting + quaternary primitive (very expensive)

### 4.4 Empirical Performance by Arity
**Data**: Solve times and timeout rates by primitive arity

### 4.5 Optimization Strategies for High-Arity Primitives
- Currying: Reduce effective arity
- Lazy evaluation: Defer constraint generation
- Conditional loading: Only declare needed primitives

### 4.6 Theoretical Complexity Classification
**Complexity Hierarchy**:
- Class 1 (Fast): Arity ≤2, no alternation
- Class 2 (Moderate): Arity 3 or ∀∃ patterns
- Class 3 (Slow): Arity ≥4 or ∀∃∀ patterns

### 4.7 Design Principle: Minimize Arity
**Recommendation**: Prefer binary/unary primitives when designing theories

### 4.8 Case Study: Arity Impact on Logos Theory
- Binary truthmaking: Efficient core
- Counterfactuals: Performance bottleneck
- Optimization outcomes

### 4.9 Summary: Arity as Complexity Driver
Key findings:
- Arity predicts performance
- Quantifier structure matters
- Design implications for theorists

---

## 5. Finite Model Exploration and Countermodel Methodology

### 5.1 The Finite Model Approach

#### Rationale
- Bounded model checking for logics
- Evidence for validity via exclusion
- Practical exploration of model space

#### Not a Complete Decision Procedure
- Finite search doesn't prove validity
- But provides strong evidence
- Finds genuine countermodels

### 5.2 State Space Representation

#### Bitvector Encoding
- Mereological structure
- Fusion operations
- State ordering

#### Mereological Operations
- Part-of relations
- Fusion construction
- Null state handling

### 5.3 Constraint-Based Model Discovery

#### Process
1. Generate truth constraints
2. Add frame constraints
3. Encode inference structure
4. Query solver
5. Extract/display models

### 5.4 Evidence for Validity via Countermodel Exclusion

#### Progressive Search Strategy
- Start with small N
- Increase if no countermodel found
- Confidence grows with larger N

#### Countermodel Discovery Cases
- Invalid inferences detected
- Minimal distinguishing models
- Theory comparison insights

### 5.5 Model Iteration for Diversity
- Block previous models
- Explore alternative countermodels
- Understand solution space

### 5.6 Limitations and Future Work

#### Current Limitations
- No completeness guarantees
- Performance constraints
- Undecidability for some logics

#### Mitigation Strategies
- Progressive search
- Optimization techniques
- Bounded fragments

#### Future Extensions
- Decidability results for fragments
- Abstraction refinement
- Parallel solving

---

## 6. Theory-Agnostic Methodology and the TheoryLib Vision

### 5.1 TheoryLib: A Library of Executable Semantic Theories

#### Current Implementation (4 Theories)
1. **Logos**: Bilateral truthmaker semantics (19 operators)
2. **Exclusion**: Unilateral truthmaker semantics
3. **Imposition**: Fine's counterfactual theory
4. **Bimodal**: Temporal-modal logic

#### TheoryLib Architecture
- Standardized interfaces
- Shared infrastructure
- Theory registry
- Dependency management

### 5.2 Vision: A Collaborative Platform for Semantic Research

#### Ambitions
- 50+ theories
- Community contributions
- Comparative benchmarking
- Citation and versioning
- Educational resources

### 5.3 Theory-Agnostic Framework Design

#### Core Abstraction: The Semantic Interface
- `true_at()` method
- Frame constraint specification
- Operator registration
- Benefits of abstraction

### 5.4 Sharing, Reuse, and Modularity

#### Operator Sharing Across Theories
- Classical operators reused
- Consistent implementations

#### Subtheory Composition
- Dependency resolution
- Conflict handling
- Modular loading

#### Cross-Theory Utilities
- Parsing
- Output formatting
- Model iteration

### 5.5 Community and Contribution Model

#### Open Source Foundations
- GPL-3 license
- Public repository

#### Contribution Workflow
1. Implement theory
2. Add test suite
3. Submit PR
4. Review and merge
5. Documentation

#### Governance
- Maintainer oversight
- Standards enforcement
- Quality control

#### Incentives for Contribution
- Citation credit
- Academic recognition
- Research tool access

---

## 7. Case Study: Logos Theory and Unified Hyperintensional Semantics

### 6.1 Philosophical Background: The Language of Thought

#### Truthmaker Semantics Foundations
- States as truthmakers
- Bilateral verification/falsification
- Hyperintensional distinctions

### 6.2 Logos Implementation Strategy

#### Design Goals
- Unified framework for all operators
- Modular subtheories
- Systematic testing

#### Technical Architecture
- State space structure
- Bilateral semantics
- Five operator subtheories

### 6.3 Operator Semantics: Five Subtheories

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

### 6.4 Unification Across Domains
- Single semantic framework
- Consistent truthmaker base
- Operator interactions

### 6.6 Empirical Validation and Test Suite

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

#### Bug Discovery Through Testing
- Fusion closure bug example
- Diagnostic process

---

## 8. Implementation Results and Empirical Validation

### 7.1 Quantitative Metrics

#### Performance Benchmarks
- Solve times by theory
- State space sizes
- Timeout rates
- Success rates

### 7.2 Qualitative Validation: Case Studies

#### Case Study 1: Counterfactual Non-Transitivity
- Lewis's famous example
- ModelChecker test
- Countermodel structure
- Philosophical import

### 7.3 Theory Comparison Results

#### Comparative Inference Table
**Table showing**:
- Classical vs. Modal vs. Constitutive vs. Counterfactual
- Key inferences for each theory
- Validity/invalidity results
- Distinguishing features

**Observations**:
- Classical validates extensional inferences
- Modal adds necessity patterns
- Constitutive grounds and essence
- Counterfactuals non-monotonic
- Relevance filters irrelevance

### 7.4 Validation Against Philosophical Literature

#### Logos vs. Fine's Imposition Semantics
**Research Question**: How does Logos compare to Fine's primitive imposition?

**Key Findings**:
- Both satisfy same frame constraints
- Logically independent (neither entails other)
- Modal definability differences
- The "Jump Problem": Imposition permits unrelated world jumps
- Vacuous truth issue in Imposition
- Minimal countermodels (IM_CM_27, IM_CM_22, IM_CM_28)

**Methodology**: `derive_imposition=True` flag testing

**Conclusion**: Structural equivalence ` logical equivalence

#### Counterfactual Logic vs. Lewis
**TODO**: Fill out comparison (note: different semantic predictions)

### 7.5 Bug Discovery and Resolution

#### Example: Fusion Closure Bug in Early Logos
- Symptom: Unexpected validity
- Investigation: Z3 model inspection
- Diagnosis: Frame constraint too strong
- Fix: Corrected constraint
- Lesson: Automated testing catches errors

---

## 9. Related Work

### 8.1 Automated Reasoning in Philosophy

#### Computational Metaphysics
- G�del's ontological argument
- Modal metaphysics automation
- Previous applications

#### Automated Theorem Proving for Modal Logic
- Existing provers
- Comparison with ModelChecker

### 8.2 SMT Solvers in Verification

#### Program Verification
- SMT applications
- Constraint solving

#### Model Checking
- Bounded model checking
- State space exploration

### 8.3 Semantic Frameworks and Implementations

#### Computational Semantics
- Previous semantic tools
- Comparison with ModelChecker

#### Proof Assistants
- Coq, Isabelle, Lean
- Differences from SMT approach

### 8.4 Truthmaker Semantics Implementations
- Prior computational work
- ModelChecker's novelty

### 8.5 Modular Software Architecture for Logic

#### Logic Frameworks
- Existing modular systems
- Design patterns

#### Comparison: ModelChecker vs. Existing Approaches
**Table comparing**:
- Features
- Strengths
- Limitations

---

## 10. Discussion and Future Directions

### 9.1 Contributions Summary

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

### 9.2 Limitations and Challenges

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

### 9.4 Broader Impact

#### Philosophy and Logic
- Computational turn in semantics
- Empirical theory evaluation
- Systematic comparison
- Educational applications

#### Computer Science and AI
- SMT solver applications
- Knowledge representation
- Automated reasoning
- Program verification analogies

#### Cognitive Science
- Computational models of reasoning
- Semantic competence modeling
- Theory testing

### 9.5 Conclusion
- Recap main contributions
- Significance of computational approach
- TheoryLib vision
- Call for community engagement

---

## 11. References

### Primary Framework Papers
- ModelChecker documentation
- Logos theory papers
- Z3 solver

### Truthmaker Semantics
- Fine's truthmaker semantics
- Correia and Schneider
- Related bilateral frameworks

### Modal and Counterfactual Logic
- Lewis on counterfactuals
- Modal logic textbooks
- Hyperintensional logic

### Automated Reasoning
- SMT solver literature
- Model checking
- Automated theorem proving

### Computational Philosophy
- Previous computational metaphysics
- Logic automation

### SMT and Model Checking
- Z3 papers
- Constraint solving
- Satisfiability

### Proof Assistants
- Coq, Isabelle, Lean
- Interactive theorem proving

### Software Engineering and Modularity
- Design patterns
- Plugin architectures
- Software engineering principles

---

## Key Themes Throughout Paper

1. **Theory-agnosticism**: Framework independent of specific theories
2. **Modularity**: Compositional operator and subtheory design
3. **Empiricism**: Objective computational metrics replace subjective assessments
4. **Arity as complexity driver**: Central organizing principle
5. **Systematic comparison**: Same examples across theories
6. **Finite model methodology**: Evidence through countermodel exclusion
7. **TheoryLib vision**: Collaborative semantic research platform
8. **Practical validation**: Real implementation, 177+ examples
9. **Bug discovery**: Computational testing finds errors
10. **Extensibility**: Multiple dimensions of extension

---

## Tables and Figures

### Proposed Tables
1. Theory comparison by primitive arity (Section 2.5.2)
2. Performance benchmarks by arity (Section 2.5.4)
3. Complexity classification (Section 2.5.6)
4. Comparative inference table (Section 7.3)
5. Logos vs. Imposition comparison (Section 7.4)
6. ModelChecker vs. existing approaches (Section 8.5)

### Proposed Figures
1. Three-level architecture diagram (Section 2.1)
2. Builder pattern orchestration (Section 2.2)
3. Constraint generation pipeline (Section 2.4)
4. State space bitvector encoding (Section 4.2)
5. TheoryLib architecture (Section 5.1)
6. Logos subtheory structure (Section 6.3)

---

## Writing Notes

### Target Audience
- Automated reasoning researchers
- Computational philosophers
- Modal/non-classical logicians
- Semantic theorists
- SMT solver practitioners

### Tone
- Rigorous and technical
- Emphasize empirical results
- Balance theory and implementation
- Accessible to both CS and philosophy

### Key Messages
1. Semantic theories can be executable programs
2. Arity determines tractability
3. Modularity enables systematic comparison
4. Finite models provide practical evidence
5. TheoryLib enables collaborative semantics

### Emphasis
- Novel contributions (bilateral truthmaker, arity metrics)
- Practical validation (real examples, bug discovery)
- Extensibility and modularity
- Community vision
