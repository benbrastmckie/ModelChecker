# Imposition Semantics Comparison

    Example: CF_CM1 of [['(A \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        (A \boxright C)
      Conclusions:
        ((A \wedge B) \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0189, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1429, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0118, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.027, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.157, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.6021, MAX TIME = 1, N = 6.

    Example: CF_CM2 of [['(A \\circleright C)'], ['((A \\wedge B) \\circleright C)']]
      Premises:
        (A \circleright C)
      Conclusions:
        ((A \wedge B) \circleright C)
    (Semantics): RUN TIME = 0.0112, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0278, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.155, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.5414, MAX TIME = 1, N = 6.
    (ImpositionSemantics): RUN TIME = 0.0197, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1396, MAX TIME = 1, N = 4.

    Example: CF_CM3 of [['(A \\boxright C)', '\\Diamond (A \\wedge B)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        (A \boxright C)
        \Diamond (A \wedge B)
      Conclusions:
        ((A \wedge B) \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0188, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1469, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.012, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0261, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1494, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.5774, MAX TIME = 1, N = 6.

    Example: CF_CM4 of [['\\neg A', '(A \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        \neg A
        (A \boxright C)
      Conclusions:
        ((A \wedge B) \boxright C)
    (Semantics): RUN TIME = 0.0145, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0316, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1615, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.7003, MAX TIME = 1, N = 6.
    (ImpositionSemantics): RUN TIME = 0.0189, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1605, MAX TIME = 1, N = 4.

    Example: CF_CM5 of [['(A \\boxright C)', '(B \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        (A \boxright C)
        (B \boxright C)
      Conclusions:
        ((A \wedge B) \boxright C)
    (ImpositionSemantics): RUN TIME = 0.019, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1495, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0147, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0335, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1555, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.583, MAX TIME = 1, N = 6.

    Example: CF_CM6 of [['(A \\boxright B)', '(A \\boxright C)'], ['((A \\wedge B) \\boxright C)']]
      Premises:
        (A \boxright B)
        (A \boxright C)
      Conclusions:
        ((A \wedge B) \boxright C)
    (Semantics): RUN TIME = 0.0132, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.028, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1568, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.6466, MAX TIME = 1, N = 6.
    (ImpositionSemantics): RUN TIME = 0.0195, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1431, MAX TIME = 1, N = 4.

    Example: CF_CM7 of [['(A \\boxright B)'], ['(\\neg B \\boxright \\neg A)']]
      Premises:
        (A \boxright B)
      Conclusions:
        (\neg B \boxright \neg A)
    (ImpositionSemantics): RUN TIME = 0.0224, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.146, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0092, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0202, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0762, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.4565, MAX TIME = 1, N = 6.

    Example: CF_CM8 of [['\\neg B', '(A \\boxright B)'], ['(\\neg B \\boxright \\neg A)']]
      Premises:
        \neg B
        (A \boxright B)
      Conclusions:
        (\neg B \boxright \neg A)
    (ImpositionSemantics): RUN TIME = 0.0181, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1457, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0116, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0357, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1017, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.6145, MAX TIME = 1, N = 6.

    Example: CF_CM9 of [['\\neg A', '\\neg B', '(A \\boxright B)'], ['(\\neg B \\boxright \\neg A)']]
      Premises:
        \neg A
        \neg B
        (A \boxright B)
      Conclusions:
        (\neg B \boxright \neg A)
    (ImpositionSemantics): RUN TIME = 0.0241, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1432, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0127, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0258, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1008, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.48, MAX TIME = 1, N = 6.

    Example: CF_CM10 of [['(A \\boxright B)', '(B \\boxright C)'], ['(A \\boxright C)']]
      Premises:
        (A \boxright B)
        (B \boxright C)
      Conclusions:
        (A \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0197, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1533, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0114, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0269, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.104, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.51, MAX TIME = 1, N = 6.

    Example: CF_CM11 of [['\\neg A', '(A \\boxright B)', '(B \\boxright C)'], ['(A \\boxright C)']]
      Premises:
        \neg A
        (A \boxright B)
        (B \boxright C)
      Conclusions:
        (A \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0196, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1459, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0112, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0277, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1059, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.4969, MAX TIME = 1, N = 6.

    Example: CF_CM12 of [['\\neg A', '\\neg B', '(A \\boxright B)', '(B \\boxright C)'], ['(A \\boxright C)']]
      Premises:
        \neg A
        \neg B
        (A \boxright B)
        (B \boxright C)
      Conclusions:
        (A \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0189, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.148, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0137, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0397, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1261, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.6319, MAX TIME = 1, N = 6.

    Example: CF_CM13 of [['(A \\boxright X)', '\\neg ((A \\wedge B) \\boxright X)', '(((A \\wedge B) \\wedge C) \\boxright X)', '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)', '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)', '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)', '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)'], []]
      Premises:
        (A \boxright X)
        \neg ((A \wedge B) \boxright X)
        (((A \wedge B) \wedge C) \boxright X)
        \neg ((((A \wedge B) \wedge C) \wedge D) \boxright X)
        (((((A \wedge B) \wedge C) \wedge D) \wedge E) \boxright X)
        \neg ((((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F) \boxright X)
        (((((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F) \wedge G) \boxright X)
      Conclusions:
    (ImpositionSemantics): RUN TIME = 0.0305, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1519, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0196, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0586, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.3442, MAX TIME = 1, N = 5.

    Example: CF_CM14 of [['\\Diamond A', '(A \\boxright X)', '\\Diamond (A \\wedge B)', '\\neg ((A \\wedge B) \\boxright X)', '\\Diamond ((A \\wedge B) \\wedge C)', '(((A \\wedge B) \\wedge C) \\boxright X)', '\\Diamond (((A \\wedge B) \\wedge C) \\wedge D)', '\\neg ((((A \\wedge B) \\wedge C) \\wedge D) \\boxright X)', '\\Diamond ((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E)', '(((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\boxright X)', '\\Diamond (((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F)', '\\neg ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\boxright X)', '\\Diamond ((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G)', '(((((((A \\wedge B) \\wedge C) \\wedge D) \\wedge E) \\wedge F) \\wedge G) \\boxright X)'], []]
      Premises:
        \Diamond A
        (A \boxright X)
        \Diamond (A \wedge B)
        \neg ((A \wedge B) \boxright X)
        \Diamond ((A \wedge B) \wedge C)
        (((A \wedge B) \wedge C) \boxright X)
        \Diamond (((A \wedge B) \wedge C) \wedge D)
        \neg ((((A \wedge B) \wedge C) \wedge D) \boxright X)
        \Diamond ((((A \wedge B) \wedge C) \wedge D) \wedge E)
        (((((A \wedge B) \wedge C) \wedge D) \wedge E) \boxright X)
        \Diamond (((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F)
        \neg ((((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F) \boxright X)
        \Diamond ((((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F) \wedge G)
        (((((((A \wedge B) \wedge C) \wedge D) \wedge E) \wedge F) \wedge G) \boxright X)
      Conclusions:
    (ImpositionSemantics): RUN TIME = 0.0299, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1566, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0205, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0641, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.3529, MAX TIME = 1, N = 5.

    Example: CF_CM15 of [['\\neg A'], ['(A \\boxright B)', '(A \\boxright \\neg B)']]
      Premises:
        \neg A
      Conclusions:
        (A \boxright B)
        (A \boxright \neg B)
    (ImpositionSemantics): RUN TIME = 0.0177, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1373, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0093, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0199, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0774, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.4296, MAX TIME = 1, N = 6.

    Example: CF_CM16 of [['\\neg A', '(A \\boxright (B \\vee C))'], ['(A \\boxright B)', '(A \\boxright C)']]
      Premises:
        \neg A
        (A \boxright (B \vee C))
      Conclusions:
        (A \boxright B)
        (A \boxright C)
    (ImpositionSemantics): RUN TIME = 0.02, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1442, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0121, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0273, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1144, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.5064, MAX TIME = 1, N = 6.

    Example: CF_CM17 of [['(A \\boxright C)', '(B \\boxright C)'], ['((A \\vee B) \\boxright C)']]
      Premises:
        (A \boxright C)
        (B \boxright C)
      Conclusions:
        ((A \vee B) \boxright C)
    (ImpositionSemantics): RUN TIME = 0.0186, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1487, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0153, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0567, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.1647, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.6186, MAX TIME = 1, N = 6.

    Example: CF_CM18 of [['A', 'B'], ['(A \\boxright B)']]
      Premises:
        A
        B
      Conclusions:
        (A \boxright B)
    (ImpositionSemantics): RUN TIME = 0.0169, MAX TIME = 1, N = 3.
    (ImpositionSemantics): RUN TIME = 0.1332, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0094, MAX TIME = 1, N = 3.
    (Semantics): RUN TIME = 0.0211, MAX TIME = 1, N = 4.
    (Semantics): RUN TIME = 0.0736, MAX TIME = 1, N = 5.
    (Semantics): RUN TIME = 0.4121, MAX TIME = 1, N = 6.
