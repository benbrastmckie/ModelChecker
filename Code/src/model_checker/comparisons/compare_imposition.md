
Example: CF_T1 of [[], ['(A \\boxright A)']]
  Premises:
  Conclusions:
    (A \boxright A)
(Semantics): RUN TIME = 0.0083, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.0247, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.1649, MAX TIME = 1, N = 5.
(ImpositionSemantics): RUN TIME = 0.02, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.3229, MAX TIME = 1, N = 4.

Example: CF_T2 of [['A', '(A \\boxright B)'], ['B']]
  Premises:
    A
    (A \boxright B)
  Conclusions:
    B
(ImpositionSemantics): RUN TIME = 0.0182, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.1689, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.0101, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.0279, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.141, MAX TIME = 1, N = 5.

Example: CF_T3 of [['(A \\boxright B)', '((A \\wedge B) \\boxright C)'], ['(A \\boxright C)']]
  Premises:
    (A \boxright B)
    ((A \wedge B) \boxright C)
  Conclusions:
    (A \boxright C)
(Semantics): RUN TIME = 0.0152, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.1138, MAX TIME = 1, N = 4.
(ImpositionSemantics): RUN TIME = 0.0302, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.4945, MAX TIME = 1, N = 4.

Example: CF_CM1 of [['(A \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
  Premises:
    (A \boxright C)
  Conclusions:
    ((A \wedge B) \boxright C)
(ImpositionSemantics): RUN TIME = 0.0201, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.1457, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.0113, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.0271, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.1532, MAX TIME = 1, N = 5.
(Semantics): RUN TIME = 0.6449, MAX TIME = 1, N = 6.

Example: CF_CM2 of [['(A \\circleright C)'], ['((A \\wedge B) \\circleright C)']]
  Premises:
    (A \circleright C)
  Conclusions:
    ((A \wedge B) \circleright C)
(ImpositionSemantics): RUN TIME = 0.0209, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.1395, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.0124, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.028, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.1613, MAX TIME = 1, N = 5.
(Semantics): RUN TIME = 0.5725, MAX TIME = 1, N = 6.

Example: CF_CM3 of [['(A \\boxright C)', '\\Diamond (A \\wedge B)'], ['((A \\wedge B) \\boxright C)']]
  Premises:
    (A \boxright C)
    \Diamond (A \wedge B)
  Conclusions:
    ((A \wedge B) \boxright C)
(ImpositionSemantics): RUN TIME = 0.0194, MAX TIME = 1, N = 3.
(ImpositionSemantics): RUN TIME = 0.1459, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.0115, MAX TIME = 1, N = 3.
(Semantics): RUN TIME = 0.0263, MAX TIME = 1, N = 4.
(Semantics): RUN TIME = 0.1597, MAX TIME = 1, N = 5.
(Semantics): RUN TIME = 0.586, MAX TIME = 1, N = 6.
