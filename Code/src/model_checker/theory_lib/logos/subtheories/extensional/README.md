# Extensional Subtheory

The **Extensional Subtheory** implements truth-functional operators following classical propositional logic. These operators form the foundation for more complex logical systems and are used as dependencies by other subtheories.

## Operators

### Primitive Operators

#### Negation (`\\neg`, �)
- **Arity**: 1
- **Description**: Logical negation - flips truth value
- **Semantics**: �A is true iff A is false

```python
# Examples
model.check_validity(["p"], ["\\neg \\neg p"])  # Double negation � True
model.check_validity(["p", "\\neg p"], ["\\bot"])  # Contradiction � True
```

#### Conjunction (`\\wedge`, ')
- **Arity**: 2  
- **Description**: Logical AND - true when both arguments are true
- **Semantics**: A ' B is true iff both A and B are true

```python
# Examples
model.check_validity(["p", "q"], ["p \\wedge q"])  # Introduction � True
model.check_validity(["p \\wedge q"], ["p"])       # Elimination � True
```

#### Disjunction (`\\vee`, ()
- **Arity**: 2
- **Description**: Logical OR - true when at least one argument is true  
- **Semantics**: A ( B is true iff at least one of A or B is true

```python
# Examples  
model.check_validity(["p"], ["(p \\vee q)"])         # Introduction - Returns True
model.check_validity([], ["(p \\vee \\neg p)"])      # Excluded middle - Returns True
```

#### Top (`\\top`, �)
- **Arity**: 0
- **Description**: Logical truth - always true
- **Semantics**: � is true in all models

```python
# Examples
model.check_validity([], ["\\top"])                # Tautology � True
model.check_validity(["\\top"], ["p \\vee \\neg p"])  # Truth implies tautology � True
```

#### Bottom (`\\bot`, �)
- **Arity**: 0
- **Description**: Logical falsehood - always false
- **Semantics**: � is false in all models

```python
# Examples
model.check_validity(["\\bot"], ["p"])             # Ex falso quodlibet � True
model.check_validity(["p \\wedge \\neg p"], ["\\bot"])  # Contradiction � True
```

### Defined Operators

#### Material Conditional (`\\rightarrow`, �)
- **Arity**: 2
- **Description**: Material implication - false only when antecedent true and consequent false
- **Definition**: A � B a �A ( B

```python
# Examples
model.check_validity(["p", "(p \\rightarrow q)"], ["q"])  # Modus ponens - Returns True
model.check_validity(["\\neg q", "(p \\rightarrow q)"], ["\\neg p"])  # Modus tollens - Returns True
```

#### Biconditional (`\\leftrightarrow`, �)
- **Arity**: 2
- **Description**: Logical equivalence - true when both sides have same truth value
- **Definition**: A � B a (A � B) ' (B � A)

```python
# Examples
model.check_validity(["(p \\leftrightarrow q)", "p"], ["q"])  # Forward direction - Returns True
model.check_validity(["(p \\leftrightarrow q)", "q"], ["p"])  # Backward direction - Returns True
```

## Usage Examples

### Basic Validity Checking

```python
from model_checker.theory_lib import logos

# Load extensional subtheory only
theory = logos.get_theory(['extensional'])

from model_checker import BuildExample
model = BuildExample("extensional_demo", theory)

# Test basic logical principles
model.check_validity([], ["(p \\rightarrow p)"])                    # Reflexivity
model.check_validity(["(p \\rightarrow q)", "(q \\rightarrow r)"], ["(p \\rightarrow r)"])  # Transitivity
model.check_validity(["(p \\wedge q)"], ["(q \\wedge p)"])            # Commutativity
```

## Testing

The extensional subtheory includes **14 comprehensive test examples** covering all seven truth-functional operators through both countermodel and theorem examples. Tests validate classical propositional logic principles and demonstrate the foundation for other subtheories.

```bash
# Run all extensional tests
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/

# Run specific example
pytest src/model_checker/theory_lib/logos/subtheories/extensional/tests/test_extensional_examples.py -k "EXT_TH_1"

# Run via project test runner
python test_theories.py --theories logos --extensional --examples
```

**For detailed test documentation, examples, and debugging guidance, see [tests/README.md](tests/README.md)**