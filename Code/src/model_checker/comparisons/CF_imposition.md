# Imposition Semantics Comparison

    Example: CF_T1 of [[], ['(A \\boxright A)']]
      Premises:
      Conclusions:
        (A \boxright A)
    (Semantics): RUN TIME = 0.0083, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0201, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1734, MAX TIME = 1, N = 5.
    (ImpositionSemantics): RUN TIME = 0.0196, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.3272, MAX TIME = 1, N = 4.

    Example: CF_T2 of [['A', '(A \\boxright B)'], ['B']]
      Premises:
        A
        (A \boxright B)
      Conclusions:
        B
    (Semantics): RUN TIME = 0.01, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0275, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.137, MAX TIME = 1, N = 5.
    (ImpositionSemantics): RUN TIME = 0.0183, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1756, MAX TIME = 1, N = 4.

    Example: CF_T3 of [['(A \\boxright B)', '((A \\wedge B) \\boxright C)'], ['(A \\boxright C)']]
      Premises:
        (A \boxright B)
        ((A \wedge B) \boxright C)
      Conclusions:
        (A \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0308, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.5132, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0148, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.115, MAX TIME = 1, N = 4.

    Example: CF_T4 of [['((A \\vee B) \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        ((A \vee B) \boxright C)
      Conclusions:
        ((A \wedge B) \boxright C)
    (Semantics): RUN TIME = 0.0136, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0701, MAX TIME = 1, N = 4.
    (ImpositionSemantics): RUN TIME = 0.0331, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.4362, MAX TIME = 1, N = 4.

    Example: CF_T5 of [['((A \\vee B) \\boxright C)'], ['(A \\boxright C)']]
      Premises:
        ((A \vee B) \boxright C)
      Conclusions:
        (A \boxright C)
    (Semantics): RUN TIME = 0.0122, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0528, MAX TIME = 1, N = 4.
    (ImpositionSemantics): RUN TIME = 0.0264, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.4375, MAX TIME = 1, N = 4.

    Example: CF_T6 of [['((A \\vee B) \\boxright C)'], ['((A \\boxright C) \\wedge (B \\boxright C))']]
      Premises:
        ((A \vee B) \boxright C)
      Conclusions:
        ((A \boxright C) \wedge (B \boxright C))
    (Semantics): RUN TIME = 0.0147, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0872, MAX TIME = 1, N = 4.
    (ImpositionSemantics): RUN TIME = 0.0333, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.6754, MAX TIME = 1, N = 4.

    Example: CF_T7 of [['(A \\boxright C)', '(B \\boxright C)', '((A \\wedge B) \\boxright C)'], ['((A \\vee B) \\boxright C)']]
      Premises:
        (A \boxright C)
        (B \boxright C)
        ((A \wedge B) \boxright C)
      Conclusions:
        ((A \vee B) \boxright C)
    (Semantics): RUN TIME = 0.0142, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0611, MAX TIME = 1, N = 4.
    (ImpositionSemantics): RUN TIME = 0.0311, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.6111, MAX TIME = 1, N = 4.

    Example: CF_T8 of [['(A \\boxright (B \\wedge C))'], ['(A \\boxright B)']]
      Premises:
        (A \boxright (B \wedge C))
      Conclusions:
        (A \boxright B)
    (Semantics): RUN TIME = 0.0115, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0391, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.5569, MAX TIME = 1, N = 5.
    (ImpositionSemantics): RUN TIME = 0.0237, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.3319, MAX TIME = 1, N = 4.

    Example: CF_T9 of [['(A \\boxright B)', '(A \\boxright C)'], ['(A \\boxright (B \\wedge C))']]
      Premises:
        (A \boxright B)
        (A \boxright C)
      Conclusions:
        (A \boxright (B \wedge C))
    (ImpositionSemantics): RUN TIME = 0.0394, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0145, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.1173, MAX TIME = 1, N = 4.

    Example: CF_T10 of [['A', 'B'], ['(A \\circleright B)']]
      Premises:
        A
        B
      Conclusions:
        (A \circleright B)
    (Semantics): RUN TIME = 0.0114, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0281, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1723, MAX TIME = 1, N = 5.
    (ImpositionSemantics): RUN TIME = 0.0188, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1628, MAX TIME = 1, N = 4.

    Example: CF_T11 of [['(\\neg A \\boxright \\bot)'], ['(\\top \\boxright A)']]
      Premises:
        (\neg A \boxright \bot)
      Conclusions:
        (\top \boxright A)
    (Semantics): RUN TIME = 0.0086, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.021, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1753, MAX TIME = 1, N = 5.
    (ImpositionSemantics): RUN TIME = 0.0164, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1306, MAX TIME = 1, N = 4.
