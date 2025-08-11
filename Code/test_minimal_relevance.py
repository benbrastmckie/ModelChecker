"""Minimal relevance theory test case for debugging iterator issues.

This example should find exactly 2 models:
- MODEL 1: A and B both true (validates premise and conclusion)  
- MODEL 2: A true, B false (validates conclusion but not premise)
"""

# Settings
N = 2
iterate = 2

# Syntax  
A = prop
B = prop

# Semantics
rule: All(p, state, iff(verify(state, p), atom(p, state)))

# Logic
{A and B} premise
A conclusion

# Model info
Model 1 expected: A=true, B=true
Model 2 expected: A=true, B=false