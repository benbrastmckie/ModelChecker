# Code Review Standards and Checklist

[← Back to Quality](METRICS.md) | [Back to Maintenance](../README.md) | [Code Standards →](../CODE_STANDARDS.md)

## Overview

This document provides a comprehensive code review checklist to ensure consistent, thorough code reviews across the ModelChecker framework. It combines automated checks with human oversight to maintain high code quality while respecting the domain complexity of logical reasoning systems.

**Philosophy**: Code reviews should focus on correctness, maintainability, and knowledge sharing while being efficient and respectful of developer time.

---

## 1. Pre-Review Checklist (Authors)

### 1.1 Before Requesting Review

**Authors MUST complete these items before requesting review:**

- [ ] **All tests pass locally**
  ```bash
  pytest src/ -v
  ```

- [ ] **Type hints added where required**
  ```bash
  mypy src/ --strict --ignore-missing-imports
  ```

- [ ] **Code follows style standards**
  ```bash
  python scripts/check_code_style.py
  ```

- [ ] **No debugging artifacts remain**
  - [ ] No `print()` statements for debugging
  - [ ] No commented-out code blocks
  - [ ] No TODO comments without issue references
  - [ ] No hardcoded file paths or credentials

- [ ] **Documentation updated**
  - [ ] Docstrings added for new public methods
  - [ ] README.md updated if API changes
  - [ ] Architecture docs updated if needed

- [ ] **Self-review completed**
  - [ ] Read through entire diff as if reviewing someone else's code
  - [ ] Verified all changes are intentional and necessary
  - [ ] Checked for potential edge cases

### 1.2 Pull Request Description Requirements

**Every PR MUST include:**

```markdown
## Summary
Brief description of what this PR accomplishes

## Changes Made
- Specific change 1
- Specific change 2
- ...

## Testing
- How the changes were tested
- Any new test cases added
- Manual testing performed

## Review Notes
- Areas requiring special attention
- Known limitations or trade-offs
- Related issues or future work
```

---

## 2. Code Review Criteria (Reviewers)

### 2.1 Correctness and Logic

#### **Core Functionality Review**

- [ ] **Algorithm correctness**
  - [ ] Logic implements the intended behavior
  - [ ] Edge cases are handled appropriately
  - [ ] Mathematical properties are preserved (for theory implementations)

- [ ] **Error handling compliance**
  ```python
  # GOOD - Specific, actionable errors
  raise ValidationError(
      f"Invalid formula: '{formula}' should be '(A \\rightarrow B)'. "
      "Binary operators require parentheses.",
      context={'formula': formula, 'operator': '\\rightarrow'},
      suggestion="Add parentheses around binary operations"
  )
  
  # BAD - Generic, unhelpful errors
  raise ValueError("Invalid input")
  ```

- [ ] **Input validation**
  - [ ] All user inputs validated before processing
  - [ ] Appropriate limits enforced (formula length, iteration depth)
  - [ ] Proper handling of None/empty values

#### **Integration Correctness**

- [ ] **API contract adherence**
  - [ ] Method signatures match expected interfaces
  - [ ] Return types consistent with documentation
  - [ ] Side effects properly documented

- [ ] **Cross-component compatibility**
  - [ ] Changes don't break existing integrations
  - [ ] New dependencies appropriately managed
  - [ ] Backward compatibility maintained (when required)

### 2.2 Code Quality Standards

#### **Type Safety and Documentation**

- [ ] **Type annotations complete**
  ```python
  # GOOD - Complete type annotations
  def process_formula(
      formula: str,
      theory: Dict[str, Any],
      settings: Optional[ModelSettings] = None
  ) -> Tuple[bool, List[str]]:
      """Process formula with given theory and settings."""
  
  # BAD - Missing or incomplete types
  def process_formula(formula, theory, settings=None):
  ```

- [ ] **Docstring quality**
  - [ ] All public methods have complete docstrings
  - [ ] Args, Returns, Raises sections included
  - [ ] Examples provided for complex methods
  - [ ] Mathematical notation explained when used

#### **Code Organization and Style**

- [ ] **Import organization compliance**
  ```python
  # GOOD - Proper import ordering
  # Standard library
  import os
  from typing import Dict, List, Optional
  
  # Third-party
  import z3
  
  # Local application  
  from model_checker.defaults import DEFAULT_SETTINGS
  
  # Relative imports
  from .utils import helper_function
  ```

- [ ] **Naming conventions**
  - [ ] Classes use PascalCase (`ModelVariable`)
  - [ ] Functions/methods use snake_case (`extract_constraints`)
  - [ ] Constants use UPPER_SNAKE_CASE (`MAX_ITERATIONS`)
  - [ ] Private members have leading underscore (`_internal_helper`)

- [ ] **Method complexity appropriate**
  - [ ] Methods under 75 lines (or justified if longer)
  - [ ] Cyclomatic complexity reasonable for domain
  - [ ] Complex algorithms broken into helper methods

### 2.3 Security and Safety

#### **Input Security**

- [ ] **No dynamic execution**
  ```python
  # NEVER do this
  eval(user_input)  # Security risk!
  exec(code_string)  # Security risk!
  
  # Use safe parsing instead
  ast.parse(user_input, mode='eval')
  ```

- [ ] **Safe file operations**
  - [ ] File paths validated and sanitized
  - [ ] Proper error handling for file operations
  - [ ] No arbitrary file access

- [ ] **Resource management**
  - [ ] Memory usage bounded for user inputs
  - [ ] Timeouts set for Z3 solver operations
  - [ ] Proper cleanup of temporary resources

---

## 3. Testing Verification Checklist

### 3.1 Test Coverage Requirements

**Reviewers MUST verify:**

- [ ] **New functionality has tests**
  - [ ] Unit tests for new methods/functions
  - [ ] Integration tests for component interactions
  - [ ] End-to-end tests for user-facing features

- [ ] **Test quality standards met**
  ```python
  # GOOD - Descriptive test with clear documentation
  def test_module_loader_raises_import_error_when_file_not_found(self):
      """Test that ModuleLoader raises ImportError when module file does not exist.
      
      This ensures proper error handling for missing module files.
      """
      loader = ModuleLoader("nonexistent", "/path/that/does/not/exist.py")
      
      with self.assertRaises(ImportError) as context:
          loader.load_module()
      
      self.assertIn("not found", str(context.exception).lower(),
                    "Error message should indicate file not found")
  ```

- [ ] **Test isolation maintained**
  - [ ] Tests clean up after themselves
  - [ ] No dependencies between test cases
  - [ ] No test artifacts left in working directory

### 3.2 Test Type Distribution

- [ ] **Appropriate test types used**
  - **Unit tests**: Single component, minimal dependencies
  - **Integration tests**: Component interactions, real objects
  - **E2E tests**: Complete workflows, minimal mocking

- [ ] **Mocking strategy appropriate**
  - [ ] Only external dependencies mocked (Z3, file system)
  - [ ] Internal components use real objects
  - [ ] Mock objects created through centralized factories

### 3.3 Performance Test Considerations

- [ ] **Performance tests for critical paths**
  - [ ] Model checking operations benchmarked
  - [ ] Memory usage tested for large inputs
  - [ ] Timeout handling verified

---

## 4. Theory Compliance Checks

### 4.1 Semantic Theory Requirements

Based on [Research 042](../../specs/research/042_theory_lib_compliance_deep_analysis.md):

- [ ] **Theory implementation completeness**
  - [ ] All required operators implemented
  - [ ] Semantic validation rules complete
  - [ ] Example cases have expected outcomes

- [ ] **Mathematical correctness**
  ```python
  # GOOD - Proper mathematical implementation
  def validate_modal_formula(self, formula: str) -> bool:
      """Validate modal formula according to S4 axioms.
      
      Implements necessity (□) and possibility (◊) operators
      with proper accessibility relation constraints.
      """
      parsed = self.parse_formula(formula)
      return self.check_s4_axioms(parsed)
  ```

- [ ] **Cross-theory consistency**
  - [ ] Operator precedence consistent across theories
  - [ ] Unicode handling uniform
  - [ ] Error messages follow package standards

### 4.2 Formula Standards Compliance

- [ ] **LaTeX notation requirements**
  ```python
  # GOOD - Proper LaTeX notation
  premises = [
      "\\Box (A \\rightarrow B)",    # Binary needs parentheses
      "\\neg C",                     # Unary no parentheses  
      "((A \\wedge B) \\vee C)"     # Nested parentheses
  ]
  
  # BAD - Incorrect notation
  bad = [
      "□(a→b)",        # Unicode and lowercase
      "(\\neg C)",     # Unnecessary parentheses
      "A \\wedge B"    # Missing outer parentheses
  ]
  ```

---

## 5. Performance Review Criteria

### 5.1 Runtime Performance

**Reviewers MUST check for:**

- [ ] **Algorithm efficiency**
  - [ ] Time complexity appropriate for problem size
  - [ ] No obvious performance bottlenecks
  - [ ] Efficient data structures used

- [ ] **Z3 optimization compliance**
  ```python
  # GOOD - Reuse Z3 contexts and batch operations
  ctx = z3.Context()
  solver = z3.Solver(ctx=ctx)
  
  constraints = []
  for item in items:
      constraints.append(create_constraint(item, ctx))
  solver.add(*constraints)  # Add all at once
  
  # BAD - Create new context for each operation
  for item in items:
      ctx = z3.Context()  # Expensive!
      solver = z3.Solver(ctx=ctx)
      solver.add(create_constraint(item, ctx))
  ```

- [ ] **Memory management**
  - [ ] No obvious memory leaks
  - [ ] Large data structures cleaned up appropriately
  - [ ] Generator patterns used for large datasets

### 5.2 Build and Test Performance

- [ ] **Test execution time acceptable**
  - [ ] Unit tests: <50ms per test
  - [ ] Integration tests: <500ms per test
  - [ ] E2E tests: <5 seconds per test

- [ ] **No performance regressions**
  - [ ] Compare benchmark results with baseline
  - [ ] Investigate any >20% performance degradation

---

## 6. Documentation Review Requirements

### 6.1 API Documentation

- [ ] **Public interface documented**
  - [ ] All public classes have purpose and usage examples
  - [ ] All public methods have complete docstrings
  - [ ] Complex algorithms explained with mathematical background

- [ ] **README.md completeness**
  - [ ] Package purpose clearly stated
  - [ ] Usage examples with working code
  - [ ] Installation/setup instructions
  - [ ] Testing guidance

### 6.2 Architecture Documentation

- [ ] **Integration guidance provided**
  - [ ] How new component fits into overall architecture
  - [ ] Dependencies and interactions documented
  - [ ] Extension points identified

- [ ] **Change impact documented**
  - [ ] Breaking changes highlighted
  - [ ] Migration guidance provided
  - [ ] Deprecation notices where appropriate

---

## 7. Issue Classification System

### 7.1 Issue Severity Levels

#### **BLOCKER** 🚫
**Must be fixed before merge:**
- Breaks existing functionality
- Security vulnerabilities
- Data corruption risks
- Critical performance regressions (>50% slower)

#### **MAJOR** ⚠️
**Should be fixed before merge:**
- Incorrect algorithm implementation
- Missing error handling for common cases
- Significant performance issues (20-50% slower)
- Missing tests for new functionality
- API inconsistencies

#### **MINOR** 📝
**Should be addressed, can be follow-up:**
- Style guide violations
- Missing docstrings for private methods
- Minor performance optimizations
- Improved error messages

#### **SUGGESTION** 💡
**Optional improvements:**
- Alternative implementation approaches
- Code organization improvements
- Additional test cases
- Documentation enhancements

### 7.2 Review Comment Templates

#### **For Blockers:**
```markdown
**BLOCKER**: [Issue description]

**Problem**: [Specific problem and impact]
**Solution**: [Required fix]
**Risk**: [What happens if not fixed]

Example: [Code example if helpful]
```

#### **For Suggestions:**
```markdown
**SUGGESTION**: [Improvement idea]

**Rationale**: [Why this would be better]
**Alternative**: [Current approach is also acceptable]

```python
# Consider this approach:
[example code]
```

### 7.3 Resolution Guidelines

**Author responsibilities:**
- Address all BLOCKER and MAJOR issues
- Respond to MINOR issues (fix or explain why not)
- Consider SUGGESTIONS (implement or acknowledge)

**Reviewer responsibilities:**
- Clearly classify issue severity
- Provide actionable feedback
- Re-review after changes
- Approve when standards met

---

## 8. Review Workflow Process

### 8.1 Standard Review Process

#### **1. Initial Review (Reviewer)**
- [ ] Run automated checks locally
- [ ] Review entire changeset systematically
- [ ] Test critical functionality manually
- [ ] Provide comprehensive feedback

#### **2. Author Response**
- [ ] Address all BLOCKER and MAJOR issues
- [ ] Respond to MINOR issues and SUGGESTIONS
- [ ] Update PR with requested changes
- [ ] Provide response summary

#### **3. Follow-up Review (Reviewer)**
- [ ] Verify all critical issues addressed
- [ ] Re-test modified functionality
- [ ] Check for new issues introduced
- [ ] Approve or request additional changes

#### **4. Final Approval**
- [ ] All automated checks passing
- [ ] All critical issues resolved
- [ ] Code meets quality standards
- [ ] Documentation complete and accurate

### 8.2 Special Review Types

#### **Architecture Changes**
**Additional requirements:**
- [ ] Tech lead approval required
- [ ] Architecture documentation updated
- [ ] Migration plan provided for breaking changes
- [ ] Performance impact assessed

#### **Theory Implementation Changes**
**Additional requirements:**
- [ ] Mathematical correctness verified
- [ ] All example cases tested
- [ ] Cross-theory consistency maintained
- [ ] Academic references provided where applicable

#### **Security-Related Changes**
**Additional requirements:**
- [ ] Security team review (if available)
- [ ] Threat model considerations documented
- [ ] Input validation thoroughly tested
- [ ] No sensitive data exposure

---

## 9. Quick Reference Checklists

### 9.1 Reviewer Quick Checklist

**Essential checks for every review:**

```markdown
## Code Quality
- [ ] Functionality correct and complete
- [ ] Error handling appropriate
- [ ] Type hints present
- [ ] Documentation complete

## Testing
- [ ] New functionality tested
- [ ] Test quality meets standards  
- [ ] No test isolation issues

## Standards Compliance
- [ ] Code style followed
- [ ] Import organization correct
- [ ] Security practices followed
- [ ] Performance acceptable

## Process
- [ ] All issues classified by severity
- [ ] Feedback actionable and respectful
- [ ] Ready for author response
```

### 9.2 Author Pre-Submission Checklist

**Complete before requesting review:**

```markdown
## Pre-Review Self-Check
- [ ] All tests pass locally
- [ ] Type checking passes
- [ ] No debugging artifacts
- [ ] Documentation updated
- [ ] Self-review completed

## PR Description
- [ ] Summary clear and complete
- [ ] Changes listed specifically  
- [ ] Testing approach described
- [ ] Review notes provided

## Quality Gates
- [ ] Functionality works as intended
- [ ] Edge cases considered
- [ ] Performance acceptable
- [ ] Security implications reviewed
```

### 9.3 Merge Readiness Checklist

**Final checks before merge:**

```markdown
## Automated Checks
- [ ] All CI checks passing
- [ ] Test coverage meets requirements
- [ ] No security scan issues
- [ ] Performance benchmarks acceptable

## Review Process Complete  
- [ ] All reviewer feedback addressed
- [ ] Required approvals obtained
- [ ] No outstanding blocker issues
- [ ] Documentation complete

## Integration Ready
- [ ] No conflicts with main branch
- [ ] Breaking changes documented
- [ ] Release notes updated (if needed)
```

---

## 10. Review Examples and Anti-Patterns

### 10.1 Good Review Patterns

#### **Constructive Feedback Example:**
```markdown
**MAJOR**: Error handling could be more specific

The current error message doesn't give users enough information to fix the issue.

```python
# Current:
raise ValueError("Invalid formula")

# Suggested:
raise ValidationError(
    f"Invalid formula: '{formula}' should be '(A \\rightarrow B)'. "
    "Binary operators require parentheses.",
    context={'formula': formula, 'operator': '\\rightarrow'},
    suggestion="Add parentheses around binary operations"
)
```

This provides users with:
1. The exact problem
2. What the formula should look like  
3. A specific fix they can apply
```

#### **Effective Suggestion Example:**
```markdown
**SUGGESTION**: Consider using a generator for memory efficiency

For large datasets, this could reduce memory usage:

```python
# Instead of loading all at once:
all_models = [create_model(item) for item in large_dataset]

# Consider streaming:
def generate_models(dataset):
    for item in dataset:
        yield create_model(item)
```

This would be especially helpful for N>4 iterations where memory usage is a concern.
```

### 10.2 Anti-Patterns to Avoid

#### **Bad Review Examples:**

```markdown
❌ "This is wrong" 
✅ "MAJOR: Algorithm doesn't handle edge case X. When input Y occurs, 
    the system will Z. Consider adding validation for..."

❌ "Use better names"
✅ "MINOR: Consider more descriptive names. 'process_data' could be 
    'validate_formula_syntax' to clarify its specific purpose."

❌ "This won't work"
✅ "BLOCKER: This approach will cause memory issues with large inputs. 
    The current implementation loads all data into memory, but for 
    N>3 iterations this could exceed 500MB. Consider streaming approach..."
```

#### **Reviewer Anti-Patterns:**
- **Nitpicking style issues** instead of focusing on functionality
- **Requesting major architectural changes** late in the review process
- **Not providing examples** of suggested improvements
- **Blocking on personal preferences** rather than standards violations

#### **Author Anti-Patterns:**
- **Ignoring reviewer feedback** without explanation
- **Making unrelated changes** during review cycles
- **Arguing about style guide requirements** instead of following them
- **Submitting incomplete implementations** expecting "feedback first"

---

## 11. Training and Onboarding

### 11.1 New Reviewer Guidelines

**Before conducting first review:**

1. **Study the standards documentation:**
   - [CODE_STANDARDS.md](../CODE_STANDARDS.md)
   - [TESTING_STANDARDS.md](../TESTING_STANDARDS.md)
   - [ERROR_HANDLING.md](../ERROR_HANDLING.md)

2. **Shadow experienced reviewers** for 3-5 reviews

3. **Practice on older PRs** to calibrate feedback style

4. **Focus on learning** rather than finding every possible issue

### 11.2 Review Skill Development

**Common beginner mistakes:**
- Focusing too much on style over substance
- Not testing the changes locally
- Providing vague feedback without examples
- Missing the bigger picture for implementation details

**Skills to develop:**
- **Pattern recognition**: Identifying common bug patterns
- **Performance intuition**: Spotting potential bottlenecks
- **Security awareness**: Recognizing vulnerability patterns
- **Communication**: Providing helpful, respectful feedback

---

## Conclusion

This comprehensive review checklist ensures consistent, thorough code reviews that maintain high quality while being efficient and respectful of developer time. By following these guidelines, the ModelChecker project can maintain its high standards while scaling development across multiple contributors.

**Key Success Factors:**
- **Automation first**: Catch style and basic issues automatically
- **Human focus**: Reviewers focus on logic, architecture, and knowledge sharing
- **Clear communication**: Feedback is actionable and respectful
- **Continuous improvement**: Process evolves based on team feedback

**Remember**: The goal is to ship high-quality, maintainable code while helping all team members learn and grow. Reviews should be collaborative, not adversarial.

---

**Document Status**: Initial comprehensive framework  
**Last Updated**: 2025-01-11  
**Next Review**: 2025-02-11  
**Owner**: Development Team  

---

[← Back to Quality](METRICS.md) | [Back to Maintenance](../README.md) | [Code Standards →](../CODE_STANDARDS.md)