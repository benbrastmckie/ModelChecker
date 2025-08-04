# Documentation Audience and Accessibility Goals

[← Back to Maintenance](README.md) | [Style Guide →](../../Code/docs/STYLE_GUIDE.md)

## Overview

The ModelChecker documentation serves researchers and practitioners across multiple disciplines: logicians, linguists, computer scientists working in formal verification, and AI researchers focusing on automated reasoning. Rather than explaining everything to everyone, we strategically highlight what matters to each audience while maintaining technical precision.

Our aim is to spark curiosity and maintain engagement by revealing interesting connections and non-obvious insights. We avoid self-aggrandizing language (no calling things "sophisticated" or "powerful") and never label explanations as "for programmers" or "for logicians" - good explanations work for everyone who's curious.

## Primary Audiences

### 1. Logicians and Semanticists

Researchers developing formal theories who need to:
- Test semantic proposals computationally
- Find countermodels to proposed principles
- Compare different semantic frameworks

**What we highlight**: How implementations realize semantic concepts, what constraints capture which logical principles, where to modify code for theory variants.

### 2. Linguists

Those working on natural language semantics who want to:
- Model compositional semantics computationally
- Test predictions about meaning
- Explore intensional phenomena

**What we highlight**: How operators compose, where linguistic phenomena map to code structures, which settings control semantic properties.

### 3. Computer Scientists (Formal Verification)

Developers building verification tools who need to:
- Understand SMT solver integration patterns
- Implement custom constraint systems
- Optimize model finding algorithms

**What we highlight**: Z3 API usage patterns, constraint generation strategies, performance implications of design choices.

### 4. AI Researchers (Automated Reasoning)

Those developing reasoning systems who want to:
- Implement logical inference engines
- Handle non-classical logics
- Build explainable AI components

**What we highlight**: How inference patterns translate to constraints, where to hook in custom reasoning procedures, what makes explanations readable.

## Documentation Principles

### 1. Strategic Highlighting

We don't explain everything to everyone. Instead:
- **Point out non-obvious patterns** for newcomers to programming
- **Highlight semantic insights** for those without logic training  
- **Give searchable terms** rather than full explanations
- **Focus on what each implementation achieves**

### 2. Natural Explanation

Documentation follows what's most natural for each topic:
- **Some need programming context** (e.g., why use bit vectors for states)
- **Others need semantic insight** (e.g., why verifiers must be fusion-closed)
- **Many just need clearer description** of what's being implemented
- **Not every point needs both perspectives**

### 3. Technical Precision

We maintain rigor while being accessible:
- **Use proper terminology** with brief definitions
- **Keep explanations short** but accurate
- **Link to deeper resources** for those who want more
- **Trust readers to research** unfamiliar concepts

## Writing Guidelines

### Core Pattern

```python
# What this does
code_example()
```

Follow code with **only what's needed**:
- What non-obvious thing is happening
- Why this specific approach matters  
- What interesting property emerges
- What gets accomplished

Avoid labeling audience - write for the curious.

### Effective Code Comments

Inline comments should be:
- **Brief and purposeful** - Explain the "why" or non-obvious "what"
- **Placed strategically** - Right after the code they explain
- **Technically accurate** - Use proper terminology

Example patterns from BUILDER.md:
```python
'N': 3,  # Default 3 atomic states (2^3 = 8 possible combinations)
'contingent': True  # Require both verifiers and falsifiers
registry = LogosOperatorRegistry()  # Manages operator dependencies
```

### When to Add Explanation

Add brief context when:
- **Programming pattern isn't obvious** (e.g., "visitor pattern for operator traversal")
- **Semantic insight matters** (e.g., "fusion closure ensures that conjunction and disjunction are idempotent")
- **Effect isn't clear** (e.g., "controls how many models to find")
- **Choice has implications** (e.g., "bit vectors limit us to N ≤ 64 states and will typically be between 3 to 5")

### Multi-Line Code Commentary

For complex code blocks, use comment blocks after the code:
```python
example = BuildExample(build_module, semantic_theory, example_case, 'Brast-McKie')
# At this point:
# - Z3 context has been reset for isolation
# - Settings merged from all sources with proper priority
# - Syntax parsed, constraints generated, model solved
# - Result available via example.get_result()
```

This pattern works well for:
- Summarizing what just happened
- Listing side effects or state changes
- Pointing out what's available next

### When to Stay Terse

Keep it minimal when:
- **Code is self-explanatory** to target audience
- **Pattern is standard** in the domain
- **Details are covered elsewhere** (just link)
- **Concept is googleable** (give the term)

## Example Documentation Patterns

### Good: Paragraph After Code

From BUILDER.md:
```python
# Settings cascade: DEFAULT → general → example → command-line
```

The settings hierarchy ensures flexibility: theory defaults provide sensible baselines, module settings configure shared behavior, example settings handle special cases, and command-line flags enable quick experimentation without editing files.

This pattern:
- Summarizes complex behavior concisely
- Explains the "why" behind the design
- Connects to practical usage

### Good: Focused Explanation

```python
# Check if state s1 verifies proposition A
verify(s1, A) = True
```

Verifiers are states that make propositions true - the "truthmakers" of truthmaker semantics. We represent them as bit vectors for efficient subset operations.

### Good: Technical Note

```python
final_settings = merge(
    command_line,    # Highest priority
    example_specific,
    module_general,
    theory_defaults  # Lowest priority
)
```

Command-line flags override all other settings, allowing quick experimentation without editing files.

### Good: Semantic Insight

```python
# If s1 and s2 verify A, their fusion must too
verify(s1, A) ∧ verify(s2, A) → verify(s1|s2, A)
```

This constraint ensures classical behavior - without it, conjunction would fail to be idempotent.

## Key Terms for Googling

When readers encounter unfamiliar concepts, we provide the right search terms:

### For Programming Concepts
- **Design patterns**: visitor, builder, factory
- **Python features**: dataclasses, ABC (abstract base class), decorators
- **Z3 concepts**: SMT solver, satisfiability, unsat core
- **Algorithms**: constraint propagation, model enumeration

### For Logic/Semantic Concepts  
- **Truthmaker semantics**: verifiers, falsifiers, fusion
- **Modal logic**: possible worlds, accessibility, necessity
- **Model theory**: satisfaction, validity, logical consequence
- **Proof theory**: natural deduction, sequent calculus

## What Makes Good Documentation

### Effective Examples

✓ **Settings that affect constraints**
```python
'contingent': True  # Adds ∃s(verify(s,A)) ∧ ∃s(falsify(s,A))
```
This setting requires atomic propositions to be genuinely contingent.

✗ **Over-explaining standard patterns**
```python
# This is a for loop that iterates over items...
for item in items:  # Too basic
```

### Clear Connections

✓ **Non-obvious implementation choice**
```python
# Using bit vectors limits N to 64 but enables fast subset operations
states = BitVec('states', N)
```

✓ **Semantic implication**
```python
# Without disjoint verifiers/falsifiers, we get truth-value gluts
'disjoint': True
```

## Remember

- **Trust your readers** - They can look things up
- **Be precise** - Use correct terminology  
- **Stay focused** - Explain what matters for this code
- **Keep it short** - A sentence or two usually suffices
- **Link wisely** - Point to detailed explanations elsewhere
- **Stay humble** - Avoid words like "sophisticated", "powerful", "advanced"
- **Be inclusive** - Never say "for programmers" or "for logicians"
- **Spark curiosity** - Highlight what's interesting or unexpected

## Visual Documentation Standards

### Flowcharts and Diagrams

Use ASCII diagrams for clarity:
- **Box components** with descriptive labels
- **Arrow for data flow** (not object composition)
- **Group related items** in larger boxes
- **Include brief descriptions** inside boxes when helpful

Example from BUILDER.md:
```
┌─────────────────────┐
│ Z3 Model            │
│ • Variable bindings │
│ • Function values   │
│ • Satisfying assign │
└──────────┬──────────┘
           │
           ▼
```

### Containment vs Flow

- **Containment boxes**: Show object composition (BuildExample contains Syntax, ModelConstraints, etc.)
- **Arrows**: Show data flow or transformation
- **Never use arrows** for "has-a" relationships

## Document Enhancement Process

When elaborating a document to meet these specifications, follow this systematic approach:

### Phase 1: Deep Subsection Research and Elaboration

1. **Start with the deepest subsections** - Work from the most specific to the general
2. **Research each subsection thoroughly** - Understand the code, its purpose, and implications
3. **Add fitting elaboration** - Brief context, interesting insights, or clarifying notes
4. **Move systematically** - Complete each deep subsection before moving to the next

### Phase 2: Document-Wide Revision

After all deep subsections are enhanced:
1. **Check for redundancy** - Remove repeated explanations
2. **Identify gaps** - What connections are missing?
3. **Find opportunities** - Where can we spark more curiosity?
4. **Ensure consistency** - Tone and style throughout
5. **Update navigation** - Revise table of contents and internal cross-links
6. **Verify references** - Ensure all section links work correctly

### Phase 3: Higher-Level Enhancement

Now enhance less-deep sections with:
- **Orienting overviews** - Set the stage for what follows
- **High-level reflections** - Why this approach? What's the big picture?
- **Connections** - How do parts relate? What patterns emerge?
- **Points of interest** - What's surprising or clever here?
- **Professional flowcharts** - When relationships need visual clarity
- **Introductory links** - Point to relevant background material

### Example Enhancement

```markdown
## Component Architecture

<!-- Original -->
The system uses three main components.

<!-- Enhanced -->
The system orchestrates model checking through three components that mirror the logical inference process:

[Add flowchart showing: Examples → BuildModule → BuildExample → Model]

This separation allows concurrent theory comparison while maintaining isolation - each example gets its own Z3 context, preventing constraint leakage between different semantic theories. See [Z3 Context Management](../solver/README.md) for the isolation mechanism.
```

### Phase 4: Implementation Links Review

Before repository-wide integration, review all code examples:
1. **Identify substantive code blocks** - Look for class definitions, method implementations, and algorithm examples
2. **Check for full implementations** - Determine if the shown code is complete or excerpted
3. **Add implementation links** - For excerpted code, add links to the full source file
4. **Use consistent format** - Place links immediately after code blocks with clear labeling

#### When to Add Implementation Links

Add links for:
- **Class definitions** showing only key methods
- **Complex algorithms** where full context helps
- **Operator implementations** showing semantic patterns
- **Settings or configuration** examples

Don't add links for:
- **Complete code snippets** that are self-contained
- **Utility functions** shown in full
- **Pseudo-code** or conceptual examples
- **External library usage** (link to library docs instead)

#### Link Format Examples

For excerpted class implementations:
```python
class LogosSemantics(SemanticDefaults):
    """Hyperintensional truthmaker semantics for Logos theory."""
    
    def __init__(self, combined_settings):
        self.N = combined_settings['N']
        # ... excerpt showing key initialization ...
```
*Full implementation: [`model_checker/theory_lib/logos/semantic.py`](../../src/model_checker/theory_lib/logos/semantic.py)*

For operator examples:
```python
class AndOperator(Operator):
    def extended_verify(self, state, arg1, arg2, eval_point):
        """State verifies A∧B iff it's fusion of verifiers."""
        # ... simplified for clarity ...
```
*See also: [`model_checker/theory_lib/logos/extensional/operators.py`](../../src/model_checker/theory_lib/logos/extensional/operators.py)*

For algorithm implementations:
```python
def parse_expression(tokens):
    """Core parsing algorithm excerpt."""
    # ... key logic shown ...
```
*Complete function: [`model_checker/utils.py#L45`](../../src/model_checker/utils.py#L45)* (with line number if helpful)

### Phase 5: Repository-Wide Integration

After the document is fully enhanced and implementation links added:
1. **Search for references** - Find all documents that link to this one
2. **Update linking text** - Revise explanations in linking documents
3. **Fix broken links** - Update any changed section anchors
4. **Add new cross-references** - Link from related documents that should reference this one
5. **Verify bidirectional links** - Ensure complementary documents link to each other

### Key Principles

- **Bottom-up elaboration** - Details first, overview second
- **Research before writing** - Understand deeply, explain simply
- **Connect and contextualize** - Show how pieces fit together
- **Visual when helpful** - Flowcharts for complex relationships
- **Link generously** - Help readers explore further
- **Maintain link integrity** - Every enhancement preserves existing references

## Code Description Conventions

### Inline Comments

Place explanatory comments on the same line when brief:
```python
'N': 4,  # Override N for this example (2^4 = 16 states)
```

### Block Comments After Code

Use for listing what happened or what's available:
```python
self.example_syntax = Syntax(premises, conclusions, operators)
# Creates sentence objects:
#   - "A \\wedge B" (complexity: 1)
#   - "C" (complexity: 0)
```

### Paragraph Explanations

Follow code blocks with a paragraph when:
- The overall purpose needs clarification
- Multiple concepts connect together
- Design rationale matters

Example:
```
Dynamic loading enables modular theory development: load only the operators your examples use, avoiding unnecessary constraint generation.
```

### Stage Descriptions

For multi-stage processes, describe transformations:
```
Each stage transforms the logical problem: strings are parsed into ASTs...
```

This pattern helps readers understand data flow through the system.
