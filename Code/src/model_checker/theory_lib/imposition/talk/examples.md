========================================

EXAMPLE IM_CM_0: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premises:
1. \neg A
2. (A \diamondright C)
3. (A \boxright C)

Conclusion:
4. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0167 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [36ma[0m
  [37m#b010 = [36mb[0m
  [37m#b011 = [34ma.b (world)[0m
  [37m#b100 = [36mc[0m
  [37m#b101 = [34ma.c (world)[0m
  [37m#b110 = [34mb.c (world)[0m

Imposition Relation:
  [34ma.b[0m →_[36m□[0m [34ma.b[0m
  [34ma.b[0m →_[36ma[0m [34ma.b[0m
  [34ma.b[0m →_[36mb[0m [34ma.b[0m
  [34ma.b[0m →_[34ma.b[0m [34ma.b[0m
  [34ma.b[0m →_[36mc[0m [34ma.c[0m
  [34ma.b[0m →_[34ma.c[0m [34ma.c[0m
  [34ma.b[0m →_[34mb.c[0m [34mb.c[0m
  [34ma.c[0m →_[36m□[0m [34ma.c[0m
  [34ma.c[0m →_[36ma[0m [34ma.c[0m
  [34ma.c[0m →_[36mc[0m [34ma.c[0m
  [34ma.c[0m →_[34ma.c[0m [34ma.c[0m
  [34mb.c[0m →_[36m□[0m [34mb.c[0m
  [34mb.c[0m →_[36mb[0m [34mb.c[0m
  [34mb.c[0m →_[36mc[0m [34mb.c[0m
  [34mb.c[0m →_[34mb.c[0m [34mb.c[0m

The evaluation world is: [34ma.b[0m

INTERPRETED PREMISES:

1.  [32m|\neg A| = < {a.b}, {c} >[0m  [32m(True in a.b)[0m
      [37m|A| = < {c}, {a.b} >[0m  [33m(False in a.b)[0m

2.  [32m|(A \diamondright C)| = < {a.b, a.c}, {b.c} >[0m  [32m(True in a.b)[0m
      [37m|A| = < {c}, {a.b} >[0m  [33m(False in a.b)[0m
      [36m|A|-alternatives to a.b = {a.c}[0m
        [37m|C| = < {a.c}, {a.b, b.c} >[0m  [33m(True in a.c)[0m

3.  [32m|(A \boxright C)| = < {a.b, a.c}, {b.c} >[0m  [32m(True in a.b)[0m
      [37m|A| = < {c}, {a.b} >[0m  [33m(False in a.b)[0m
      [36m|A|-alternatives to a.b = {a.c}[0m
        [37m|C| = < {a.c}, {a.b, b.c} >[0m  [33m(True in a.c)[0m

INTERPRETED CONCLUSION:

4.  [31m|((A \wedge B) \boxright C)| = < {a.c}, {a.b, b.c} >[0m  [31m(False in a.b)[0m
      [37m|(A \wedge B)| = < {b.c}, {a.b, a.c} >[0m  [33m(False in a.b)[0m
        [37m|A| = < {c}, {a.b} >[0m  [33m(False in a.b)[0m
        [37m|B| = < {b}, {a.c} >[0m  [33m(True in a.b)[0m
      [36m|(A \wedge B)|-alternatives to a.b = {b.c}[0m
        [37m|C| = < {a.c}, {a.b, b.c} >[0m  [33m(False in b.c)[0m

Total Run Time: 0.0841 seconds

========================================
========================================

EXAMPLE IM_CM_1: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0091 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [36ma[0m
  [37m#b010 = [34mb (world)[0m
  [37m#b100 = [36mc[0m
  [37m#b101 = [34ma.c (world)[0m

Imposition Relation:
  [34mb[0m →_[36m□[0m [34mb[0m
  [34mb[0m →_[34mb[0m [34mb[0m
  [34mb[0m →_[34ma.c[0m [34ma.c[0m
  [34ma.c[0m →_[36m□[0m [34ma.c[0m
  [34ma.c[0m →_[36ma[0m [34ma.c[0m
  [34ma.c[0m →_[36mc[0m [34ma.c[0m
  [34ma.c[0m →_[34ma.c[0m [34ma.c[0m

The evaluation world is: [34mb[0m

INTERPRETED PREMISES:

1.  [32m|\neg A| = < {b}, {c} >[0m  [32m(True in b)[0m
      [37m|A| = < {c}, {b} >[0m  [33m(False in b)[0m

2.  [32m|(A \boxright C)| = < {b}, {a.c} >[0m  [32m(True in b)[0m
      [37m|A| = < {c}, {b} >[0m  [33m(False in b)[0m
      [36m|A|-alternatives to b = ∅[0m

INTERPRETED CONCLUSION:

3.  [31m|((A \wedge B) \boxright C)| = < ∅, {a.c, b} >[0m  [31m(False in b)[0m
      [37m|(A \wedge B)| = < {a.c}, {b} >[0m  [33m(False in b)[0m
        [37m|A| = < {c}, {b} >[0m  [33m(False in b)[0m
        [37m|B| = < {a}, {b} >[0m  [33m(False in b)[0m
      [36m|(A \wedge B)|-alternatives to b = {a.c}[0m
        [37m|C| = < {b}, {c} >[0m  [33m(False in a.c)[0m

Total Run Time: 0.0633 seconds

========================================
========================================

EXAMPLE IM_CM_6: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premises:
1. \neg A
2. (A \boxright B)
3. (A \boxright C)

Conclusion:
4. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0085 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [36ma[0m
  [37m#b010 = [34mb (world)[0m
  [37m#b100 = [36mc[0m
  [37m#b101 = [34ma.c (world)[0m

Imposition Relation:
  [34mb[0m →_[36m□[0m [34mb[0m
  [34mb[0m →_[34mb[0m [34mb[0m
  [34mb[0m →_[34ma.c[0m [34ma.c[0m
  [34ma.c[0m →_[36m□[0m [34ma.c[0m
  [34ma.c[0m →_[36ma[0m [34ma.c[0m
  [34ma.c[0m →_[36mc[0m [34ma.c[0m
  [34ma.c[0m →_[34ma.c[0m [34ma.c[0m

The evaluation world is: [34mb[0m

INTERPRETED PREMISES:

1.  [32m|\neg A| = < {b}, {a} >[0m  [32m(True in b)[0m
      [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m

2.  [32m|(A \boxright B)| = < {a.c, b}, ∅ >[0m  [32m(True in b)[0m
      [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m
      [36m|A|-alternatives to b = ∅[0m

3.  [32m|(A \boxright C)| = < {b}, {a.c} >[0m  [32m(True in b)[0m
      [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m
      [36m|A|-alternatives to b = ∅[0m

INTERPRETED CONCLUSION:

4.  [31m|((A \wedge B) \boxright C)| = < ∅, {a.c, b} >[0m  [31m(False in b)[0m
      [37m|(A \wedge B)| = < {a, a.c}, {b} >[0m  [33m(False in b)[0m
        [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m
        [37m|B| = < {a, a.c, c}, {b} >[0m  [33m(False in b)[0m
      [36m|(A \wedge B)|-alternatives to b = {a.c}[0m
        [37m|C| = < {b}, {a} >[0m  [33m(False in a.c)[0m

Total Run Time: 0.0671 seconds

========================================
========================================

EXAMPLE IM_CM_10: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premises:
1. (A \boxright B)
2. (B \boxright C)

Conclusion:
3. (A \boxright C)

Z3 Run Time: 0.0093 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [34ma (world)[0m
  [37m#b010 = [36mb[0m
  [37m#b100 = [36mc[0m
  [37m#b110 = [34mb.c (world)[0m

Imposition Relation:
  [34ma[0m →_[36m□[0m [34ma[0m
  [34ma[0m →_[34ma[0m [34ma[0m
  [34ma[0m →_[34mb.c[0m [34mb.c[0m
  [34mb.c[0m →_[36m□[0m [34mb.c[0m
  [34mb.c[0m →_[36mb[0m [34mb.c[0m
  [34mb.c[0m →_[36mc[0m [34mb.c[0m
  [34mb.c[0m →_[34mb.c[0m [34mb.c[0m

The evaluation world is: [34ma[0m

INTERPRETED PREMISES:

1.  [32m|(A \boxright B)| = < {a, b.c}, ∅ >[0m  [32m(True in a)[0m
      [37m|A| = < {b.c}, {a} >[0m  [33m(False in a)[0m
      [36m|A|-alternatives to a = {b.c}[0m
        [37m|B| = < {b}, {a} >[0m  [33m(True in b.c)[0m

2.  [32m|(B \boxright C)| = < {a}, {b.c} >[0m  [32m(True in a)[0m
      [37m|B| = < {b}, {a} >[0m  [33m(False in a)[0m
      [36m|B|-alternatives to a = ∅[0m

INTERPRETED CONCLUSION:

3.  [31m|(A \boxright C)| = < ∅, {a, b.c} >[0m  [31m(False in a)[0m
      [37m|A| = < {b.c}, {a} >[0m  [33m(False in a)[0m
      [36m|A|-alternatives to a = {b.c}[0m
        [37m|C| = < {a}, {b.c} >[0m  [33m(False in b.c)[0m

Total Run Time: 0.0603 seconds

========================================
========================================

EXAMPLE IM_CM_22: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premise:
1. (\top \boxright A)

Conclusion:
2. \Box A

Z3 Run Time: 0.0065 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [36ma[0m
  [37m#b010 = [36mb[0m
  [37m#b011 = [34ma.b (world)[0m
  [37m#b100 = [36mc[0m
  [37m#b110 = [34mb.c (world)[0m

Imposition Relation:
  [34ma.b[0m →_[36m□[0m [34ma.b[0m
  [34ma.b[0m →_[36ma[0m [34ma.b[0m
  [34ma.b[0m →_[36mb[0m [34ma.b[0m
  [34ma.b[0m →_[34ma.b[0m [34ma.b[0m
  [34mb.c[0m →_[36m□[0m [34mb.c[0m
  [34mb.c[0m →_[36mb[0m [34mb.c[0m
  [34mb.c[0m →_[36mc[0m [34mb.c[0m
  [34mb.c[0m →_[34mb.c[0m [34mb.c[0m

The evaluation world is: [34mb.c[0m

INTERPRETED PREMISE:

1.  [32m|(\top \boxright A)| = < {b.c}, {a.b} >[0m  [32m(True in b.c)[0m
      [37m|\top| = < {a, a.b, b, b.c, c, □}, ∅ >[0m  [33m(True in b.c)[0m
      [36m|\top|-alternatives to b.c = {b.c}[0m
        [37m|A| = < {b.c}, {a.b} >[0m  [33m(True in b.c)[0m

INTERPRETED CONCLUSION:

2.  [31m|\Box A| = < ∅, {□} >[0m  [31m(False in b.c)[0m
      [37m|A| = < {b.c}, {a.b} >[0m  [33m(False in a.b)[0m
      [37m|A| = < {b.c}, {a.b} >[0m  [33m(True in b.c)[0m

Total Run Time: 0.0484 seconds

========================================
========================================

EXAMPLE IM_CM_23: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premise:
1. (A \boxright \bot)

Conclusion:
2. (\top \boxright \neg A)

Z3 Run Time: 0.0062 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [36ma[0m
  [37m#b010 = [34mb (world)[0m
  [37m#b100 = [36mc[0m
  [37m#b101 = [34ma.c (world)[0m

Imposition Relation:
  [34mb[0m →_[36m□[0m [34mb[0m
  [34mb[0m →_[34mb[0m [34mb[0m
  [34mb[0m →_[36mc[0m [34ma.c[0m
  [34mb[0m →_[34ma.c[0m [34ma.c[0m
  [34ma.c[0m →_[36m□[0m [34ma.c[0m
  [34ma.c[0m →_[36ma[0m [34ma.c[0m
  [34ma.c[0m →_[36mc[0m [34ma.c[0m
  [34ma.c[0m →_[34ma.c[0m [34ma.c[0m

The evaluation world is: [34mb[0m

INTERPRETED PREMISE:

1.  [32m|(A \boxright \bot)| = < {b}, {a.c} >[0m  [32m(True in b)[0m
      [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m
      [36m|A|-alternatives to b = ∅[0m

INTERPRETED CONCLUSION:

2.  [31m|(\top \boxright \neg A)| = < ∅, {a.c, b} >[0m  [31m(False in b)[0m
      [37m|\top| = < {a, a.c, b, c, □}, ∅ >[0m  [33m(True in b)[0m
      [36m|\top|-alternatives to b = {a.c, b}[0m
        [37m|\neg A| = < {b}, {a} >[0m  [33m(True in b)[0m
          [37m|A| = < {a}, {b} >[0m  [33m(False in b)[0m
        [37m|\neg A| = < {b}, {a} >[0m  [33m(False in a.c)[0m
          [37m|A| = < {a}, {b} >[0m  [33m(True in a.c)[0m

Total Run Time: 0.0458 seconds

========================================
========================================

EXAMPLE IM_CM_25: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premises:
1. A
2. \Diamond B
3. \neg \Diamond (A \wedge B)

Conclusion:
4. (B \boxright C)

Z3 Run Time: 0.0074 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [34ma (world)[0m
  [37m#b010 = [34mb (world)[0m
  [37m#b100 = [34mc (world)[0m

Imposition Relation:
  [34ma[0m →_[36m□[0m [34ma[0m
  [34ma[0m →_[34ma[0m [34ma[0m
  [34mb[0m →_[36m□[0m [34ma[0m
  [34mb[0m →_[36m□[0m [34mb[0m
  [34mb[0m →_[34ma[0m [34ma[0m
  [34mb[0m →_[34mb[0m [34mb[0m
  [34mb[0m →_[34mc[0m [34mc[0m
  [34mc[0m →_[36m□[0m [34mc[0m
  [34mc[0m →_[34mc[0m [34mc[0m

The evaluation world is: [34mb[0m

INTERPRETED PREMISES:

1.  [32m|A| = < {b}, {a, c} >[0m  [32m(True in b)[0m

2.  [32m|\Diamond B| = < {□}, ∅ >[0m  [32m(True in b)[0m
      [37m|B| = < {a, c}, {b} >[0m  [33m(True in a)[0m
      [37m|B| = < {a, c}, {b} >[0m  [33m(False in b)[0m
      [37m|B| = < {a, c}, {b} >[0m  [33m(True in c)[0m

3.  [32m|\neg \Diamond (A \wedge B)| = < {□}, ∅ >[0m  [32m(True in b)[0m
      [37m|\Diamond (A \wedge B)| = < ∅, {□} >[0m  [33m(False in b)[0m
        [37m|(A \wedge B)| = < ∅, {a, b, c} >[0m  [33m(False in a)[0m
          [37m|A| = < {b}, {a, c} >[0m  [33m(False in a)[0m
          [37m|B| = < {a, c}, {b} >[0m  [33m(True in a)[0m
        [37m|(A \wedge B)| = < ∅, {a, b, c} >[0m  [33m(False in b)[0m
          [37m|A| = < {b}, {a, c} >[0m  [33m(True in b)[0m
          [37m|B| = < {a, c}, {b} >[0m  [33m(False in b)[0m
        [37m|(A \wedge B)| = < ∅, {a, b, c} >[0m  [33m(False in c)[0m
          [37m|A| = < {b}, {a, c} >[0m  [33m(False in c)[0m
          [37m|B| = < {a, c}, {b} >[0m  [33m(True in c)[0m

INTERPRETED CONCLUSION:

4.  [31m|(B \boxright C)| = < ∅, {a, b, c} >[0m  [31m(False in b)[0m
      [37m|B| = < {a, c}, {b} >[0m  [33m(False in b)[0m
      [36m|B|-alternatives to b = {a, c}[0m
        [37m|C| = < ∅, {□} >[0m  [33m(False in c)[0m
        [37m|C| = < ∅, {□} >[0m  [33m(False in a)[0m

Total Run Time: 0.08 seconds

========================================
========================================

EXAMPLE IM_CM_26: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premise:
1. (A \boxright B)

Conclusion:
2. (A \boxrightlogos B)

Z3 Run Time: 0.0071 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [34ma (world)[0m
  [37m#b010 = [34mb (world)[0m

Imposition Relation:
  [34ma[0m →_[36m□[0m [34ma[0m
  [34ma[0m →_[34ma[0m [34ma[0m
  [34mb[0m →_[36m□[0m [34mb[0m
  [34mb[0m →_[34mb[0m [34mb[0m

The evaluation world is: [34mb[0m

INTERPRETED PREMISE:

1.  [32m|(A \boxright B)| = < {b}, {a} >[0m  [32m(True in b)[0m
      [37m|A| = < {a, □}, ∅ >[0m  [33m(True in b)[0m
      [36m|A|-alternatives to b = {b}[0m
        [37m|B| = < {b}, {a} >[0m  [33m(True in b)[0m

INTERPRETED CONCLUSION:

2.  [31m|(A \boxrightlogos B)| = < ∅, {a, b} >[0m  [31m(False in b)[0m
      [37m|A| = < {a, □}, ∅ >[0m  [33m(True in b)[0m
      [36m|A|-alternatives to b = {a, b}[0m
        [37m|B| = < {b}, {a} >[0m  [33m(True in b)[0m
        [37m|B| = < {b}, {a} >[0m  [33m(False in a)[0m

Total Run Time: 0.0689 seconds

========================================
========================================

EXAMPLE IM_CM_27: there is a countermodel.

Atomic States: 3

Semantic Theory: Fine

Premise:
1. (A \boxrightlogos B)

Conclusion:
2. (A \boxright B)

Z3 Run Time: 0.0076 seconds

========================================
State Space:
  [37m#b000 = [33m□[0m
  [37m#b001 = [34ma (world)[0m
  [37m#b100 = [34mc (world)[0m

Imposition Relation:
  [34ma[0m →_[36m□[0m [34ma[0m
  [34ma[0m →_[36m□[0m [34mc[0m
  [34ma[0m →_[34ma[0m [34ma[0m
  [34ma[0m →_[34mc[0m [34mc[0m
  [34mc[0m →_[36m□[0m [34mc[0m
  [34mc[0m →_[34mc[0m [34mc[0m

The evaluation world is: [34ma[0m

INTERPRETED PREMISE:

1.  [32m|(A \boxrightlogos B)| = < {a}, {c} >[0m  [32m(True in a)[0m
      [37m|A| = < {□}, ∅ >[0m  [33m(True in a)[0m
      [36m|A|-alternatives to a = {a}[0m
        [37m|B| = < {a}, {c} >[0m  [33m(True in a)[0m

INTERPRETED CONCLUSION:

2.  [31m|(A \boxright B)| = < ∅, {a, c} >[0m  [31m(False in a)[0m
      [37m|A| = < {□}, ∅ >[0m  [33m(True in a)[0m
      [36m|A|-alternatives to a = {a, c}[0m
        [37m|B| = < {a}, {c} >[0m  [33m(False in c)[0m
        [37m|B| = < {a}, {c} >[0m  [33m(True in a)[0m

Total Run Time: 0.0664 seconds

========================================
