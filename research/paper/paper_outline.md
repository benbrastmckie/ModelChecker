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

### 1.1 The Challenge of Semantic Theory Development
- Current state: Manual model construction and proofs
- Limitations:
  - Difficulty verifying complex interactions between many operators
  - No systematic method for theory comparison
  - Model space exploration is limited by manual validation
  - **Subjective complexity evaluation** (aesthetic vs. empirical)

### 1.2 The Computational Turn in Semantics
- **TODO**: Review recent comparable automated reasoning projects
- **TODO**: Identify remaining gaps to fill

### 1.3 Our Contribution
Six main contributions:
1. Compiles object language sentences to SMT constraints
2. Modular semantic clauses for easy importing
3. Systematic comparison framework
4. Finite model exploration
5. TheoryLib implementation for sharing semantic frameworks
6. Objective measures of the computability of a theory

**Paper Structure Preview**

---

## 2. ModelChecker Pipeline

### 2.1 Complete Pipeline Architecture

The ModelChecker implements a three-stage pipeline that transforms user-provided logical arguments into validity statements or countermodels.

#### 2.1.1 Input Processing

**Primary Input: Python Module File**

The system accepts a Python module containing three core structures:

1. **semantic_theories** (dict): Maps theory names to semantic implementations
   - Each theory provides: `semantics`, `model`, `operators`, `proposition` classes
   - Enables multi-theory comparison on identical examples

2. **example_range** (dict): Maps example names to argument specifications
   - Format: `[premises], [conclusions], {settings}`
   - Example: `["A", "A -> B"], ["B"], {"N": 3, "model": False}`

3. **general_settings** (dict): Global configuration overrides
   - Controls model size (`N`), timeout (`max_time`), debugging flags

**Command-Line Arguments**

- Theory Selection: `--load_theory`, `--subtheory`
- Model Constraints: `--contingent`, `--non_null`, `--non_empty`, `--disjoint`
- Output Control: `--save`, `--maximize` (cross-theory comparison)
- Debugging: `--print_constraints`, `--print_z3`

**Settings Resolution Hierarchy** (highest priority first):
1. CLI flag overrides
2. Module `general_settings`
3. Theory-specific defaults

**BuildModule Orchestration** (`builder/module.py:27-346`)

The `BuildModule` class serves as the central orchestrator:
- Dynamic module loading of `semantic_theories` and `example_range`
- Settings validation and merging across hierarchy
- Output management setup (OutputManager for file/console routing)
- Component instantiation (ModelRunner, ModelComparison, Translation)

#### 2.1.2 Logical Processing Pipeline

**Execution Flow** (`builder/runner.py:689-753`)

For each example and theory combination:
1. Z3 context isolation (`z3._main_ctx = None`) prevents state leakage
2. BuildExample construction per argument
3. Syntax parsing -> Constraint generation -> Z3 solving

**BuildExample Construction** (`builder/example.py:36-177`)

Each argument undergoes standardized processing:
- Initialize clean Z3 context
- Validate and extract semantic components (semantics, operators, proposition class)
- Merge theory + example + global settings
- Build model structure with constraints

**Syntax Processing** (`model_checker/syntactic/syntax.py`)

The `Syntax` class parses formulas into structured representations:
- Convert infix strings to `Sentence` objects recursively
- Link operators to semantic implementations from theory
- Extract atomic propositions (`sentence_letters`)
- Validate no circular operator definitions

**Constraint Generation** (`model_checker/models/constraints.py:19-150`)

The `ModelConstraints` class bridges syntax and semantics with four constraint categories:

1. **Frame constraints**: Define semantic structure (accessibility relations, mereology)
2. **Model constraints**: Ensure propositions have valid semantic values
3. **Premise constraints**: Require premises to be true (satisfied)
4. **Conclusion constraints**: Require conclusions to be false (for countermodel search)

All constraints combine: `frame + model + premise + conclusion`

**Z3 Solving** (`model_checker/models/structure.py`)

The `ModelDefaults` class handles SMT solving:
- Create fresh Z3 solver instance
- Add all constraints with tracking labels
- Check satisfiability with timeout
- Extract model (if SAT) or unsat core (if UNSAT)
- Store results: `z3_model`, `z3_model_status`, `z3_model_runtime`

**Model Iteration** (optional, if `iterate > 1`)

For multiple countermodels (`iterate/core.py`):
- Generator-based incremental display
- Create difference constraints to exclude previous models
- Isomorphism detection skips equivalent models (via NetworkX graph matching)
- Calculate and display model differences

#### 2.1.3 Output Generation

**Console Output** (standard)

If valid: `"No countermodel exists for N = 3. The argument is valid (within search space)."`

If invalid: Displays countermodel with premises, conclusions, settings, and theory-specific visualization (states, valuations, accessibility relations)

**File Outputs** (via `OutputManager`)

- **Markdown** (`--save markdown`): Formatted with ANSI color conversion
- **JSON** (`--save json`): Structured data with serialized valuations
- **Jupyter Notebook** (`--save jupyter`): Interactive notebook with regenerable models

**Comparison Mode** (`--maximize`)

Runs same examples across theories, displaying comparative results table:
- Theory name, validity status, runtime for each
- Enables empirical complexity comparison

**Key Implementation Locations**:
- Entry point: `__main__.py:main()` (line 229-312)
- CLI parsing: `ParseFileFlags` class
- Orchestration: `BuildModule` → `BuildExample` → `ModelDefaults`
- Core packages: `builder/`, `models/`, `syntactic/`, `iterate/`, `output/`

### 2.2 Modularity Through Operator Classes

The framework implements a three-layer modularity architecture where operator classes encapsulate syntax parsing, semantic interpretation, and model evaluation in unified, reusable components.

#### 2.2.1 Three-Layer Operator Architecture

Operators bridge three distinct layers with strict separation of concerns:

**Layer 1: Syntax (Theory-Independent)**

Location: `model_checker/syntactic/`

Core components provide theory-agnostic parsing infrastructure:

- **Operator Base Class** (`syntactic/operators.py:25-75`): Defines interface for all operators
  - Attributes: `name` (LaTeX symbol), `arity`, `primitive` flag
  - Instance reference: `semantics` (links to semantic framework)
  - Common methods: `__str__`, `__repr__`, `__eq__`, `__hash__`

- **DefinedOperator Class** (`syntactic/operators.py:262-344`): For derived operators
  - Implements `derived_definition(*args)` in prefix notation
  - Example: Material conditional as `[OrOperator, [NegationOperator, leftarg], rightarg]`

- **Syntax Parser** (`syntactic/syntax.py`): Converts infix strings to Sentence tree structures
  - Builds `all_sentences` dictionary mapping formulas to Sentence objects
  - Extracts atomic sentence letters
  - Theory-agnostic: Recognizes structural patterns without knowing operator semantics

- **OperatorCollection** (`syntactic/collection.py`): Registry mapping LaTeX names to operator classes

**Key Innovation**: Same parser handles classical, modal, hyperintensional, and temporal operators without modification.

**Layer 2: Semantics (Theory-Specific Plugin)**

Location: Each theory directory (e.g., `theory_lib/logos/`)

Operators implement up to 6 semantic methods depending on theory requirements:

1. **`true_at(self, *arguments, eval_point)`** (intensional theories)
   - Defines truth conditions as Z3 constraints
   - Example (NecessityOperator): `ForAll(u, Implies(is_world(u), true_at(argument, u)))`

2. **`false_at(self, *arguments, eval_point)`** (bilateral theories)
   - Defines falsity conditions independently of truth
   - Example (NegationOperator): Returns argument's `true_at` (swap)

3. **`extended_verify(self, state, *arguments, eval_point)`** (hyperintensional)
   - Defines verification conditions in state-based semantics
   - Example (AndOperator): `Exists([x, y], verify(x, left) AND verify(y, right) AND state == fusion(x, y))`

4. **`extended_falsify(self, state, *arguments, eval_point)`** (hyperintensional bilateral)
   - Defines falsification conditions (distinct from negation of verification)

5. **`find_verifiers_and_falsifiers(self, *arguments, eval_point)`** (model extraction)
   - Computes exact verifier/falsifier sets from Z3 model
   - Example (NegationOperator): Swaps argument's verifiers and falsifiers

6. **`print_method(self, sentence_obj, eval_point, indent_num, use_colors)`** (display)
   - Theory-specific result formatting

**Evaluation Point Dictionary**: Extensible context for diverse frameworks
- Modal: `{"world": w}`
- Bimodal: `{"world": w, "time": t}`
- Hyperintensional: Access to worlds and partial states

**Semantic Framework Class** (e.g., `logos/semantic.py:41-200`):
- Declares Z3 primitives (verify, falsify, possible functions)
- Defines frame constraints (structural semantic principles)
- Implements `true_at()`/`false_at()` dispatchers:
  - Atoms: Existential quantification over verifying/falsifying states
  - Complex formulas: Delegate to operator's semantic method

**Layer 3: Model (Theory-Dependent Interpretation)**

- Z3 constraint generation from operator semantics
- Fresh Z3 context per example prevents contamination
- Model extraction via `find_verifiers_and_falsifiers()` methods
- Theory-specific output formatting via `print_method()`

#### 2.2.2 Subtheory Organization and Dynamic Loading

**LogosOperatorRegistry** (`logos/operators.py:23-220`): Manages modular operator loading

**Available Subtheories** (5 independent modules):

1. **extensional**: neg, and, or, implies, iff, top, bottom (classical connectives)
2. **modal**: box, diamond (necessity, possibility)
3. **constitutive**: equiv, leq, sqsubseteq, preceq (identity, ground, essence, subject-matter)
4. **counterfactual**: box-arrow, diamond-arrow (counterfactual conditionals)
5. **relevance**: Content-sensitive relevance operators

**Dependency Resolution** (automatic):
- modal -> [extensional, counterfactual]
- counterfactual -> [extensional]
- relevance -> [constitutive]
- extensional, constitutive -> [] (no dependencies)

**Load Process**:
1. Check if subtheory already loaded
2. Recursively load dependencies first
3. Import subtheory module via `importlib`
4. Extract operators via `get_operators()` function
5. Add to `OperatorCollection`

**Subtheory Module Structure** (standard pattern):
- `operators.py`: Operator class implementations
- `__init__.py`: Exports `get_operators()` dictionary
- `examples.py`: Example formulas
- `tests/`: Test suites

**Public API**:
```python
get_theory(subtheories=['extensional', 'modal'])  # Load only these
get_theory()  # Load all subtheories
```

**Performance Benefit**: Fewer operators = fewer constraints = faster Z3 solving

#### 2.2.3 Operator Responsibilities by Theory Type

**Intensional Theories** (require `true_at`):
- Modal, temporal, epistemic frameworks
- Example: Box operator checks truth in all accessible worlds

**Bilateral Theories** (require `true_at` + `false_at`):
- Bilateralism with truth-falsity gaps
- Example: Negation swaps truth/falsity conditions

**Hyperintensional Theories** (require `extended_verify` + `extended_falsify`):
- State-based semantics with fusion operators
- Example: And operator fuses verifier states

**Defined Operators** (only `derived_definition`):
- Material conditional: `NOT A OR B`
- Biconditional: `(A -> B) AND (B -> A)`
- No semantic methods needed (expand to definition)

**Key Implementation Locations**:
- Base classes: `syntactic/operators.py`
- Subtheories: `theory_lib/logos/subtheories/`
- Registry: `theory_lib/logos/operators.py`
- Example theory: `theory_lib/logos/` (logos), `theory_lib/exclusion/` (exclusion)

### 2.3 Settings System and Model Discovery

The framework employs a hierarchical settings system controlling both general behavior and theory-specific semantic constraints, with specialized tools like iterate for systematic countermodel exploration.

#### 2.3.1 Hierarchical Settings Architecture

**Priority Order** (highest to lowest):
1. Command-line flags (e.g., `--contingent`, `--maximize`)
2. Example-specific settings (per-argument configuration)
3. User general preferences (`general_settings` in module)
4. Theory-specific defaults (`DEFAULT_EXAMPLE_SETTINGS`)
5. Framework global defaults

**SettingsManager Coordination**:
- `validate_general_settings()`: Validates against theory defaults
- `validate_example_settings()`: Ensures per-example consistency
- `apply_flag_overrides()`: Applies CLI as final overrides

Location: `settings/settings.py:36-176`

#### 2.3.2 Essential Model Configuration Settings

**Core Settings** (shared by all theories):

- **N**: State space size (number of atomic states, default: 16)
  - Binary encoding: 2^N total states
  - Directly impacts computational cost

- **max_time**: Z3 solver timeout in milliseconds (default: 10)
  - Prevents infinite searches
  - Theory-dependent optimal values

- **iterate**: Number of distinct countermodels to find (default: False)
  - When > 1, triggers multi-model search (see 2.3.5-2.3.8)
  - Uses isomorphism detection to ensure non-duplicate models

**Semantic Constraint Settings** (theory-specific):

- **contingent**: Requires propositions have both verifiers and falsifiers
  - Enforces modal contingency
  - Implicitly prevents null-state verification

- **non_empty**: Prevents empty verifier/falsifier sets
  - Ensures propositions have semantic content
  - Weaker than contingent

- **non_null**: Prevents null state as verifier/falsifier
  - Excludes trivial models
  - Often used with disjoint

- **disjoint**: Ensures disjoint subject-matters
  - Verifier and falsifier sets don't overlap
  - Enforces semantic separation

#### 2.3.3 Semantic Controls via Constraint Generation

**Example: `contingent` Setting**

When `contingent: True`, generates Z3 constraints requiring both possible verifiers and falsifiers:

```python
possible_verifier = Exists(x,
    And(possible(x), verify(x, sentence_letter)))
possible_falsifier = Exists(y,
    And(possible(y), falsify(y, sentence_letter)))
```

**Constraint Composition** (logos/semantic.py:626-637):
```python
constraints = get_classical_constraints()
if settings['contingent']:
    constraints.extend(get_contingent_constraints())
if settings['non_empty'] and not settings['contingent']:
    constraints.extend(get_non_empty_constraints())
if settings['disjoint']:
    constraints.extend(get_disjoint_constraints())
    constraints.extend(get_non_null_constraints())
```

Settings programmatically enforce logical properties through Z3 SMT solving.

#### 2.3.4 Cross-Theory Comparison with --maximize

**Operation**: `--maximize` flag enables systematic cross-theory comparison

**Mechanism** (__main__.py:297-305):
- Bypass standard execution
- Route to `ModelComparison` class
- Test same examples across multiple theories

**Comparison Process** (builder/comparison.py:78-138):
1. Take identical example (premises, conclusions, base settings)
2. Test incrementally larger N values for each theory
3. Use concurrent execution (ProcessPoolExecutor)
4. Return comparative results: which theories handled larger models

**Output**: Empirical complexity metrics
- Theory name, max N achieved, runtime
- Replaces subjective assessments with objective computational measures
- Demonstrates practical complexity differences (referenced in Section 2.5)

#### 2.3.5 The Iterate Setting for Model Discovery

**Purpose**: Systematic exploration of countermodel diversity

**Activation**: Set `iterate=N` where N > 1

**Mechanism**: Finds N distinct non-isomorphic countermodels through constraint-based search with graph isomorphism filtering

**Use Cases**:
- Demonstrate argument admits multiple countermodels
- Compare model structures across theories
- Explore semantic diversity within single framework

Location: `iterate/` package

#### 2.3.6 Constraint-Based Model Exclusion Algorithm

**High-Level Algorithm** (iterate/core.py:46-150):

```
1. Find initial model M_1 via Z3 solving original constraints C_original
2. For each iteration i (2 to N):
   a. Generate difference constraints C_diff excluding all previous models
   b. Solve SAT(C_original AND C_diff)
   c. Check if new model M_i is isomorphic to any previous model
   d. If isomorphic: strengthen C_diff and retry
   e. If non-isomorphic: accept M_i and continue
3. Report statistics and termination reason
```

**Persistent Solver Architecture**:
- Maintains original constraints C_original throughout
- Incrementally adds difference constraints C_diff per iteration
- Avoids re-solving base problem

**State-Based Difference Constraints**:
- World structure differences: Number of worlds, accessibility relations
- Possible state differences: Which states are possible
- Verification/falsification differences: Semantic value assignments

**Generator Pattern** (runner.py:574-643):
- Yields models incrementally for display
- Enables streaming output during long searches
- Allows early termination if sufficient models found

#### 2.3.7 Graph Isomorphism Detection

**Why Isomorphism Matters**: Models with same structure but different labels should be skipped

**Graph Representation**:
- Nodes: Worlds (labeled with propositions true/false at that world)
- Edges: Accessibility relations (or temporal precedence)

**Two-Stage Check** (iterate/graph.py):

**Stage 1: Quick Structural Rejection**
- Node count comparison
- Edge count comparison
- Degree sequence comparison
If any mismatch → models are non-isomorphic (accept)

**Stage 2: VF2 Algorithm** (via NetworkX)
- Full graph isomorphism test
- Checks if graph mapping preserves structure and labels
- If isomorphic → reject model, add stronger exclusion constraint

**Escape Strategy**:
- When isomorphic found: add constraint excluding specific Z3 assignment
- Prevents infinite loops on isomorphism class
- Ensures termination even if all non-isomorphic models exhausted

**Graceful Degradation**: Works without NetworkX but may find label-equivalent duplicates

#### 2.3.8 Iteration Statistics and Progress Tracking

**Per-Search Statistics** (displayed after iteration complete):

- Models found: Total non-isomorphic countermodels discovered
- Isomorphic skipped: Models rejected due to isomorphism
- Search duration: Total wall-clock time
- Termination reason: Max reached, timeout, exhausted, consecutive failures

**Termination Conditions**:
1. **Max reached**: Found requested N models
2. **Timeout**: Exceeded time limit (max_time × iterations)
3. **Search space exhausted**: Z3 returns UNSAT (no more models exist)
4. **Consecutive failures**: Too many isomorphic attempts (heuristic cutoff)

**Progress Tracking** (via UnifiedProgress):
- Real-time display during search
- Shows current iteration, models found, time elapsed
- Enables monitoring long-running searches

**Example Output**:
```
Iteration Statistics:
  Models found: 5
  Isomorphic skipped: 12
  Duration: 45.3s
  Termination: Max reached
```

**Key Implementation Locations**:
- Settings: `settings/settings.py`
- CLI parsing: `__main__.py:36-184`
- Semantic controls: `theory_lib/logos/semantic.py:569-637`
- Comparison: `builder/comparison.py`
- Iteration engine: `iterate/core.py`, `iterate/constraints.py`, `iterate/graph.py`


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
- Would-counterfactual (��)
- Might-counterfactual (ǒ)
- Alternative world selection

#### 5. Relevance Operators
- Relevance implication (�c)
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
