========================================

EXAMPLE EX_CM_1: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. (A \vee B)

Conclusion:
2. (A \wedge B)

Z3 Run Time: 0.0022 seconds

========================================
World Histories:
  W_0: (0:a)

Evaluation Point:
  World History W_0: a
  Time: 0
  World State: a

INTERPRETED PREMISE:

1.  |(A \vee B)| = < {a}, {} >  (True in W_0 at time 0)
      |A| = < {a}, {} >  (True in W_0 at time 0)
      |B| = < {}, {a} >  (False in W_0 at time 0)

INTERPRETED CONCLUSION:

2.  |(A \wedge B)| = < {}, {a} >  (False in W_0 at time 0)
      |A| = < {a}, {} >  (True in W_0 at time 0)
      |B| = < {}, {a} >  (False in W_0 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 B = AtomSort!val!1,
 frame7 = True,
 is_world = [else -> And(0 <= Var(0), Not(1 <= Var(0)))],
 world_interval_start = [else ->
                         If(And(0 <= Var(0),
                                Not(1 <= Var(0))),
                            0,
                            2)],
 truth_condition = [(0, AtomSort!val!1) -> False,
                    else -> True],
 world_interval_end = [else ->
                       If(And(0 <= Var(0), Not(1 <= Var(0))),
                          0,
                          3)],
 forward_of = [else -> 4],
 world_function = [else ->
                   If(And(0 <= Var(0), Not(1 <= Var(0))),
                      K(Int, 0),
                      K(Int, 1))],
 backward_of = [else -> 5],
 Task = [else -> False]]

========================================

---

========================================

EXAMPLE MD_CM_1: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Box (A \vee B)

Conclusions:
2. \Box A
3. \Box B

Z3 Run Time: 0.0093 seconds

========================================
World Histories:
  W_0: (0:c)
  W_1: (0:a)
  W_2: (0:b)

Evaluation Point:
  World History W_0: c
  Time: 0
  World State: c

INTERPRETED PREMISE:

1.  |\Box (A \vee B)| = < {a, b, c}, {} >  (True in W_0 at time 0)
      |(A \vee B)| = < {a, b, c}, {} >  (True in W_0 at time 0)
        |A| = < {a, c}, {b} >  (True in W_0 at time 0)
        |B| = < {b, c}, {a} >  (True in W_0 at time 0)
      |(A \vee B)| = < {a, b, c}, {} >  (True in W_1 at time 0)
        |A| = < {a, c}, {b} >  (True in W_1 at time 0)
        |B| = < {b, c}, {a} >  (False in W_1 at time 0)
      |(A \vee B)| = < {a, b, c}, {} >  (True in W_2 at time 0)
        |A| = < {a, c}, {b} >  (False in W_2 at time 0)
        |B| = < {b, c}, {a} >  (True in W_2 at time 0)

INTERPRETED CONCLUSIONS:

2.  |\Box A| = < {}, {a, b, c} >  (False in W_0 at time 0)
      |A| = < {a, c}, {b} >  (True in W_0 at time 0)
      |A| = < {a, c}, {b} >  (True in W_1 at time 0)
      |A| = < {a, c}, {b} >  (False in W_2 at time 0)

3.  |\Box B| = < {}, {a, b, c} >  (False in W_0 at time 0)
      |B| = < {b, c}, {a} >  (True in W_0 at time 0)
      |B| = < {b, c}, {a} >  (False in W_1 at time 0)
      |B| = < {b, c}, {a} >  (True in W_2 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame4 = True,
 frame5 = True,
 conclusions2 = True,
 frame1 = True,
 frame7 = True,
 B = AtomSort!val!1,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!33(Var(0)) == 1,
                k!33(Var(0)) == 2,
                k!33(Var(0)) == 0)],
 world_interval_start = [else ->
                         If(Or(k!33(Var(0)) == 1,
                               k!33(Var(0)) == 2,
                               k!33(Var(0)) == 0),
                            0,
                            36)],
 k!33 = [else ->
         If(0 <= Var(0),
            If(1 <= Var(0),
               If(2 <= Var(0), If(3 <= Var(0), 3, 2), 1),
               0),
            -1)],
 world_interval_end = [else ->
                       If(Or(k!33(Var(0)) == 1,
                             k!33(Var(0)) == 2,
                             k!33(Var(0)) == 0),
                          0,
                          37)],
 backward_of = [else -> 41],
 Task = [else -> False],
 truth_condition = [(1, AtomSort!val!0) -> False,
                    (0, AtomSort!val!1) -> False,
                    else -> True],
 forward_of = [else -> 38],
 world_function = [else ->
                   If(k!33(Var(0)) == 1,
                      K(Int, 0),
                      If(k!33(Var(0)) == 0,
                         Store(K(Int, 0), 0, 2),
                         If(k!33(Var(0)) == 2,
                            Store(K(Int, 0), 0, 1),
                            K(Int, 3))))]]

========================================

---

========================================

EXAMPLE MD_CM_2: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Diamond (A \vee B)

Conclusion:
2. (\Diamond A \wedge \Diamond B)

Z3 Run Time: 0.0027 seconds

========================================
World Histories:
  W_0: (0:a)

Evaluation Point:
  World History W_0: a
  Time: 0
  World State: a

INTERPRETED PREMISE:

1.  |\Diamond (A \vee B)| = < {a}, {} >  (True in W_0 at time 0)
      |(A \vee B)| = < {a}, {} >  (True in W_0 at time 0)
        |A| = < {}, {a} >  (False in W_0 at time 0)
        |B| = < {a}, {} >  (True in W_0 at time 0)

INTERPRETED CONCLUSION:

2.  |(\Diamond A \wedge \Diamond B)| = < {}, {a} >  (False in W_0 at time 0)
      |\Diamond A| = < {}, {a} >  (False in W_0 at time 0)
        |A| = < {}, {a} >  (False in W_0 at time 0)
      |\Diamond B| = < {a}, {} >  (True in W_0 at time 0)
        |B| = < {a}, {} >  (True in W_0 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 frame7 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 B = AtomSort!val!1,
 is_world = [else -> And(0 <= Var(0), Not(1 <= Var(0)))],
 world_interval_start = [else ->
                         If(And(0 <= Var(0),
                                Not(1 <= Var(0))),
                            0,
                            9)],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 world_interval_end = [else ->
                       If(And(0 <= Var(0), Not(1 <= Var(0))),
                          0,
                          10)],
 forward_of = [else -> 11],
 world_function = [else ->
                   If(And(0 <= Var(0), Not(1 <= Var(0))),
                      K(Int, 0),
                      K(Int, 1))],
 backward_of = [else -> 12],
 Task = [else -> False]]

========================================

---

========================================

EXAMPLE MD_CM_3: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. A

Conclusion:
2. \Box A

Z3 Run Time: 0.0571 seconds

========================================
World Histories:
  W_0: (0:c)
  W_1: (0:a)

Evaluation Point:
  World History W_0: c
  Time: 0
  World State: c

INTERPRETED PREMISE:

1.  |A| = < {c}, {a} >  (True in W_0 at time 0)

INTERPRETED CONCLUSION:

2.  |\Box A| = < {}, {a, c} >  (False in W_0 at time 0)
      |A| = < {c}, {a} >  (True in W_0 at time 0)
      |A| = < {c}, {a} >  (False in W_1 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame4 = True,
 frame7 = True,
 frame5 = True,
 frame1 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!428(Var(0)) == 1, k!428(Var(0)) == 0)],
 world_interval_start = [else ->
                         If(Or(k!428(Var(0)) == -9,
                               k!428(Var(0)) == 1,
                               k!428(Var(0)) == 0),
                            0,
                            48)],
 k!428 = [else ->
          If(-17 <= Var(0),
             If(-9 <= Var(0),
                If(-8 <= Var(0),
                   If(-7 <= Var(0),
                      If(-4 <= Var(0),
                         If(-3 <= Var(0),
                            If(-2 <= Var(0),
                               If(-1 <= Var(0),
                                  If(0 <= Var(0),
                                     If(1 <= Var(0),
                                        If(2 <= Var(0),
                                        If(3 <= Var(0),
                                        3,
                                        2),
                                        1),
                                        0),
                                     -1),
                                  -2),
                               -3),
                            -4),
                         -7),
                      -8),
                   -9),
                -17),
             -18)],
 world_interval_end = [else ->
                       If(Or(k!428(Var(0)) == -9,
                             k!428(Var(0)) == 1,
                             k!428(Var(0)) == 0),
                          0,
                          46)],
 backward_of = [else -> 49],
 Task = [else -> False],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 forward_of = [else -> 47],
 world_function = [else ->
                   If(k!428(Var(0)) == 2,
                      Store(K(Int, 1), -1, 0),
                      If(k!428(Var(0)) == -9,
                         Store(K(Int, 0), 0, 1),
                         If(k!428(Var(0)) == 1,
                            Store(K(Int, 0), -1, 1),
                            If(k!428(Var(0)) == 0,
                               Store(K(Int, 0), 0, 2),
                               K(Int, 3)))))]]

========================================

---

========================================

EXAMPLE MD_CM_4: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Diamond A

Conclusion:
2. A

Z3 Run Time: 0.0061 seconds

========================================
World Histories:
  W_0: (0:a)
  W_1: (0:d)
  W_2: (0:c)
  W_3: (0:b)

Evaluation Point:
  World History W_0: a
  Time: 0
  World State: a

INTERPRETED PREMISE:

1.  |\Diamond A| = < {a, b, c, d}, {} >  (True in W_0 at time 0)
      |A| = < {b, c, d}, {a} >  (False in W_0 at time 0)
      |A| = < {b, c, d}, {a} >  (True in W_1 at time 0)
      |A| = < {b, c, d}, {a} >  (True in W_2 at time 0)
      |A| = < {b, c, d}, {a} >  (True in W_3 at time 0)

INTERPRETED CONCLUSION:

2.  |A| = < {b, c, d}, {a} >  (False in W_0 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame7 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!467(Var(0)) == 2,
                k!467(Var(0)) == 1,
                k!467(Var(0)) == 0,
                k!467(Var(0)) == 3)],
 world_interval_start = [else ->
                         If(Or(k!467(Var(0)) == 2,
                               k!467(Var(0)) == 1,
                               k!467(Var(0)) == 0,
                               k!467(Var(0)) == 3),
                            0,
                            35)],
 k!467 = [else ->
          If(0 <= Var(0),
             If(1 <= Var(0),
                If(2 <= Var(0),
                   If(3 <= Var(0), If(4 <= Var(0), 4, 3), 2),
                   1),
                0),
             -1)],
 world_interval_end = [else ->
                       If(Or(k!467(Var(0)) == 2,
                             k!467(Var(0)) == 1,
                             k!467(Var(0)) == 0,
                             k!467(Var(0)) == 3),
                          0,
                          36)],
 backward_of = [else -> 38],
 Task = [else -> False],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 forward_of = [else -> 37],
 world_function = [else ->
                   If(k!467(Var(0)) == 1,
                      Store(K(Int, 0), 0, 3),
                      If(k!467(Var(0)) == 2,
                         Store(K(Int, 0), 0, 2),
                         If(k!467(Var(0)) == 0,
                            K(Int, 0),
                            If(k!467(Var(0)) == 3,
                               Store(K(Int, 0), 0, 1),
                               Store(K(Int, 1), 34, 0)))))]]

========================================

---

========================================

EXAMPLE MD_CM_5: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Diamond A

Conclusion:
2. \Box A

Z3 Run Time: 0.0041 seconds

========================================
World Histories:
  W_0: (0:b)
  W_1: (0:a)

Evaluation Point:
  World History W_0: b
  Time: 0
  World State: b

INTERPRETED PREMISE:

1.  |\Diamond A| = < {a, b}, {} >  (True in W_0 at time 0)
      |A| = < {b}, {a} >  (True in W_0 at time 0)
      |A| = < {b}, {a} >  (False in W_1 at time 0)

INTERPRETED CONCLUSION:

2.  |\Box A| = < {}, {a, b} >  (False in W_0 at time 0)
      |A| = < {b}, {a} >  (True in W_0 at time 0)
      |A| = < {b}, {a} >  (False in W_1 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame7 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!505(Var(0)) == 0, k!505(Var(0)) == 1)],
 world_interval_start = [else ->
                         If(Or(k!505(Var(0)) == 0,
                               k!505(Var(0)) == 1),
                            0,
                            18)],
 world_interval_end = [else ->
                       If(Or(k!505(Var(0)) == 0,
                             k!505(Var(0)) == 1),
                          0,
                          19)],
 backward_of = [else -> 22],
 Task = [else -> False],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 forward_of = [else -> 20],
 k!505 = [else ->
          If(0 <= Var(0),
             If(1 <= Var(0), If(2 <= Var(0), 2, 1), 0),
             -1)],
 world_function = [else ->
                   If(k!505(Var(0)) == 0,
                      Store(K(Int, 0), 0, 1),
                      If(k!505(Var(0)) == 1,
                         K(Int, 0),
                         K(Int, 2)))]]

========================================

---

========================================

EXAMPLE MD_CM_6: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premises:
1. \Diamond A
2. \Diamond B

Conclusion:
3. \Diamond (A \wedge B)

Z3 Run Time: 0.0077 seconds

========================================
World Histories:
  W_0: (0:c)
  W_1: (0:b)
  W_2: (0:a)

Evaluation Point:
  World History W_0: c
  Time: 0
  World State: c

INTERPRETED PREMISES:

1.  |\Diamond A| = < {a, b, c}, {} >  (True in W_0 at time 0)
      |A| = < {b}, {a, c} >  (False in W_0 at time 0)
      |A| = < {b}, {a, c} >  (True in W_1 at time 0)
      |A| = < {b}, {a, c} >  (False in W_2 at time 0)

2.  |\Diamond B| = < {a, b, c}, {} >  (True in W_0 at time 0)
      |B| = < {a}, {b, c} >  (False in W_0 at time 0)
      |B| = < {a}, {b, c} >  (False in W_1 at time 0)
      |B| = < {a}, {b, c} >  (True in W_2 at time 0)

INTERPRETED CONCLUSION:

3.  |\Diamond (A \wedge B)| = < {}, {a, b, c} >  (False in W_0 at time 0)
      |(A \wedge B)| = < {}, {a, b, c} >  (False in W_0 at time 0)
        |A| = < {b}, {a, c} >  (False in W_0 at time 0)
        |B| = < {a}, {b, c} >  (False in W_0 at time 0)
      |(A \wedge B)| = < {}, {a, b, c} >  (False in W_1 at time 0)
        |A| = < {b}, {a, c} >  (True in W_1 at time 0)
        |B| = < {a}, {b, c} >  (False in W_1 at time 0)
      |(A \wedge B)| = < {}, {a, b, c} >  (False in W_2 at time 0)
        |A| = < {b}, {a, c} >  (False in W_2 at time 0)
        |B| = < {a}, {b, c} >  (True in W_2 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame7 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 premises2 = True,
 B = AtomSort!val!1,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!542(Var(0)) == 1,
                k!542(Var(0)) == 2,
                k!542(Var(0)) == 0)],
 world_interval_start = [else ->
                         If(Or(k!542(Var(0)) == 1,
                               k!542(Var(0)) == 2,
                               k!542(Var(0)) == 0),
                            0,
                            51)],
 k!542 = [else ->
          If(0 <= Var(0),
             If(1 <= Var(0),
                If(2 <= Var(0), If(3 <= Var(0), 3, 2), 1),
                0),
             -1)],
 world_interval_end = [else ->
                       If(Or(k!542(Var(0)) == 1,
                             k!542(Var(0)) == 2,
                             k!542(Var(0)) == 0),
                          0,
                          52)],
 backward_of = [else -> 54],
 Task = [else -> False],
 truth_condition = [(0, AtomSort!val!1) -> True,
                    (1, AtomSort!val!0) -> True,
                    else -> False],
 forward_of = [else -> 53],
 world_function = [else ->
                   If(k!542(Var(0)) == 0,
                      Store(K(Int, 0), 0, 2),
                      If(k!542(Var(0)) == 2,
                         K(Int, 0),
                         If(k!542(Var(0)) == 1,
                            Store(K(Int, 0), 0, 1),
                            K(Int, 3))))]]

========================================

---

========================================

EXAMPLE TN_CM_1: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. A

Conclusion:
2. \Future A

Z3 Run Time: 0.9238 seconds

========================================
World Histories:
  W_0:           (0:c) =⟹ (+1:a)
  W_1: (-1:c) =⟹ (0:a)

Evaluation Point:
  World History W_0: c =⟹ a
  Time: 0
  World State: c

INTERPRETED PREMISE:

1.  |A| = < {c}, {a} >  (True in W_0 at time 0)

INTERPRETED CONCLUSION:

2.  |\Future A| = < {a}, {c} >  (False in W_0 at time 0)
      |A| = < {c}, {a} >  (True in W_0 at time 0)
      |A| = < {c}, {a} >  (False in W_0 at time 1)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 frame7 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 is_world = [else ->
             Or(k!675(Var(0)) == 0, k!675(Var(0)) == 1)],
 world_interval_start = [else ->
                         If(Or(k!675(Var(0)) == -2,
                               k!675(Var(0)) == -1),
                            1,
                            If(k!675(Var(0)) == -5,
                               0,
                               If(k!675(Var(0)) == -4,
                                  -2,
                                  If(Or(k!675(Var(0)) == -3,
                                        k!675(Var(0)) == 1),
                                     -1,
                                     If(k!675(Var(0)) == 0,
                                        0,
                                        181)))))],
 world_interval_end = [else ->
                       If(Or(k!675(Var(0)) == -2,
                             k!675(Var(0)) == -1),
                          0,
                          If(k!675(Var(0)) == -5,
                             1,
                             If(Or(k!675(Var(0)) == -4,
                                   k!675(Var(0)) == -3,
                                   k!675(Var(0)) == 1),
                                0,
                                If(k!675(Var(0)) == 0,
                                   1,
                                   182))))],
 backward_of = [else -> If(k!675(Var(0)) == 0, 1, 186)],
 Task = [else -> True],
 k!675 = [else ->
          If(-5 <= Var(0),
             If(-4 <= Var(0),
                If(-3 <= Var(0),
                   If(-2 <= Var(0),
                      If(-1 <= Var(0),
                         If(0 <= Var(0),
                            If(1 <= Var(0),
                               If(2 <= Var(0),
                                  If(3 <= Var(0), 3, 2),
                                  1),
                               0),
                            -1),
                         -2),
                      -3),
                   -4),
                -5),
             -6)],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 forward_of = [else -> If(k!675(Var(0)) == 1, 0, 183)],
 world_function = [else ->
                   If(k!675(Var(0)) == -5,
                      Store(K(Int, 2), 25470, 0),
                      If(k!675(Var(0)) == -1,
                         Store(Store(Store(Store(Store(Store(Store(Store(Store(Store(Store(K(Int,
                                        0),
                                        99693,
                                        2),
                                        76498,
                                        2),
                                        -91487,
                                        1),
                                        21096,
                                        2),
                                        21097,
                                        2),
                                        76497,
                                        1),
                                        3829,
                                        2),
                                        -49538,
                                        2),
                                        -49539,
                                        1),
                                     3828,
                                     1),
                               -22033,
                               1),
                         If(k!675(Var(0)) == 1,
                            Lambda(k!0,
                                   If(And(-8945 <= k!0,
                                        -8944 <= k!0,
                                        -8943 <= k!0,
                                        -7478 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        2578 <= k!0,
                                        2579 <= k!0,
                                        2580 <= k!0,
                                        3827 <= k!0,
                                        3828 <= k!0,
                                        3829 <= k!0,
                                        3830 <= k!0,
                                        Not(5851 <= k!0)),
                                      1,
                                      If(And(-8945 <= k!0,
                                        -8944 <= k!0,
                                        -8943 <= k!0,
                                        -7478 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        2578 <= k!0,
                                        2579 <= k!0,
                                        2580 <= k!0,
                                        3827 <= k!0,
                                        3828 <= k!0,
                                        3829 <= k!0,
                                        3830 <= k!0,
                                        5851 <= k!0,
                                        5852 <= k!0,
                                        5853 <= k!0,
                                        6618 <= k!0,
                                        12148 <= k!0,
                                        12149 <= k!0,
                                        12150 <= k!0,
                                        12151 <= k!0,
                                        14264 <= k!0,
                                        14265 <= k!0,
                                        21095 <= k!0,
                                        21096 <= k!0,
                                        25468 <= k!0,
                                        25469 <= k!0,
                                        25470 <= k!0,
                                        41596 <= k!0,
                                        41597 <= k!0,
                                        Not(56238 <= k!0)),
                                        0,
                                        If(And(-8945 <= k!0,
                                        -8944 <= k!0,
                                        -8943 <= k!0,
                                        -7478 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        2578 <= k!0,
                                        2579 <= k!0,
                                        2580 <= k!0,
                                        3827 <= k!0,
                                        3828 <= k!0,
                                        3829 <= k!0,
                                        3830 <= k!0,
                                        5851 <= k!0,
                                        5852 <= k!0,
                                        5853 <= k!0,
                                        6618 <= k!0,
                                        12148 <= k!0,
                                        12149 <= k!0,
                                        12150 <= k!0,
                                        12151 <= k!0,
                                        14264 <= k!0,
                                        14265 <= k!0,
                                        21095 <= k!0,
                                        21096 <= k!0,
                                        25468 <= k!0,
                                        25469 <= k!0,
                                        25470 <= k!0,
                                        41596 <= k!0,
                                        41597 <= k!0,
                                        56238 <= k!0,
                                        56239 <= k!0,
                                        56240 <= k!0,
                                        56241 <= k!0,
                                        Not(99691 <= k!0)),
                                        1,
                                        If(And(-8945 <= k!0,
                                        -8944 <= k!0,
                                        -8943 <= k!0,
                                        -7478 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        2578 <= k!0,
                                        2579 <= k!0,
                                        2580 <= k!0,
                                        3827 <= k!0,
                                        3828 <= k!0,
                                        3829 <= k!0,
                                        3830 <= k!0,
                                        5851 <= k!0,
                                        5852 <= k!0,
...

========================================

---

TIMEOUT: Model search exceeded maximum time of 5 seconds
No model for example TN_CM_2 found before timeout.
Try increasing max_time > 5.

========================================

EXAMPLE TN_CM_2: there is no countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premises:
1. \future A
2. \future B

Conclusion:
3. \future (A \wedge B)

Z3 Run Time: 5.0005 seconds

========================================
UNSATISFIABLE CORE CONSTRAINTS:
- Frame constraints: 0
- Model constraints: 0
- Premise constraints: 0
- Conclusion constraints: 0

---

========================================

EXAMPLE BM_CM_1: there is a countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Future A

Conclusion:
2. \Box A

Z3 Run Time: 0.1425 seconds

========================================
World Histories:
  W_0:           (0:a) =⟹ (+1:d)
  W_1: (-1:a) =⟹ (0:d)

Evaluation Point:
  World History W_0: a =⟹ d
  Time: 0
  World State: a

INTERPRETED PREMISE:

1.  |\Future A| = < {a, d}, {} >  (True in W_0 at time 0)
      |A| = < {d}, {a} >  (False in W_0 at time 0)
      |A| = < {d}, {a} >  (True in W_0 at time 1)

INTERPRETED CONCLUSION:

2.  |\Box A| = < {}, {a, d} >  (False in W_0 at time 0)
      |A| = < {d}, {a} >  (False in W_0 at time 0)
      |A| = < {d}, {a} >  (True in W_1 at time 0)

[frame3 = True,
 premises1 = True,
 conclusions1 = True,
 frame8 = True,
 frame6 = True,
 frame7 = True,
 frame4 = True,
 frame5 = True,
 frame1 = True,
 model2 = True,
 frame9 = True,
 A = AtomSort!val!0,
 frame2 = True,
 model1 = True,
 is_world = [else ->
             Or(k!950(Var(0)) == 1, k!950(Var(0)) == 0)],
 world_interval_start = [else ->
                         If(k!950(Var(0)) == -1,
                            -2,
                            If(Or(k!950(Var(0)) == -3,
                                  k!950(Var(0)) == 1),
                               -1,
                               If(k!950(Var(0)) == 0, 0, 74)))],
 world_interval_end = [else ->
                       If(Or(k!950(Var(0)) == 1,
                             k!950(Var(0)) == -3,
                             k!950(Var(0)) == -1,
                             k!950(Var(0)) == -2),
                          0,
                          If(k!950(Var(0)) == 0, 1, 75))],
 backward_of = [else -> If(k!950(Var(0)) == 0, 1, 80)],
 Task = [else -> True],
 truth_condition = [(0, AtomSort!val!0) -> False,
                    else -> True],
 forward_of = [else -> If(k!950(Var(0)) == 1, 0, 76)],
 world_function = [else ->
                   If(k!950(Var(0)) == 1,
                      Lambda(k!0,
                             If(And(-1 <= k!0,
                                    0 <= k!0,
                                    1 <= k!0,
                                    2 <= k!0,
                                    5855 <= k!0,
                                    5856 <= k!0,
                                    8367 <= k!0,
                                    8368 <= k!0,
                                    Not(11798 <= k!0)),
                                1,
                                If(And(-1 <= k!0,
                                       0 <= k!0,
                                       Not(1 <= k!0)),
                                   3,
                                   If(-1 <= k!0,
                                      If(And(-1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        8367 <= k!0,
                                        8368 <= k!0,
                                        11798 <= k!0,
                                        11799 <= k!0,
                                        11800 <= k!0,
                                        11801 <= k!0),
                                        1,
                                        If(And(-1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        5855 <= k!0,
                                        Not(5856 <= k!0)),
                                        3,
                                        If(And(-1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        8367 <= k!0,
                                        8368 <= k!0,
                                        11798 <= k!0,
                                        Not(11799 <= k!0)),
                                        2,
                                        0))),
                                      2)))),
                      If(k!950(Var(0)) == -1,
                         Store(Store(K(Int, 2), 1, 0),
                               28102,
                               1),
                         If(k!950(Var(0)) == -4,
                            K(Int, 0),
                            If(k!950(Var(0)) == -3,
                               Store(K(Int, 0), 1143, 2),
                               If(k!950(Var(0)) == -2,
                                  Store(Store(K(Int, 1),
                                        5856,
                                        0),
                                        8368,
                                        0),
                                  If(k!950(Var(0)) == 0,
                                     Lambda(k!0,
                                        If(Or(And(-42736 <=
                                        k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        3 <= k!0,
                                        Not(5855 <= k!0)),
                                        And(-42736 <= k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        3 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        5857 <= k!0,
                                        8367 <= k!0,
                                        8368 <= k!0,
                                        Not(8369 <= k!0))),
                                        2,
                                        If(And(-42736 <= k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        3 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        Not(5857 <= k!0)),
                                        3,
                                        If(Or(And(-42736 <=
                                        k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        Not(3 <= k!0)),
                                        And(-42736 <= k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        3 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        5857 <= k!0,
                                        8367 <= k!0,
                                        8368 <= k!0,
                                        8369 <= k!0,
                                        Not(11799 <= k!0))),
                                        2,
                                        If(And(-42736 <= k!0,
                                        -284 <= k!0,
                                        Not(-1 <= k!0)),
                                        1,
                                        If(And(-42736 <= k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        Not(2 <= k!0)),
                                        3,
                                        If(And(-42736 <= k!0,
                                        -284 <= k!0,
                                        -1 <= k!0,
                                        0 <= k!0,
                                        1 <= k!0,
                                        2 <= k!0,
                                        3 <= k!0,
                                        5855 <= k!0,
                                        5856 <= k!0,
                                        5857 <= k!0,
                                        8367 <= k!0,
                                        8368 <= k!0,
                                        8369 <= k!0,
                                        11799 <= k!0,
                                        Not(11800 <= k!0)),
                                        2,
                                        0))))))),
                                     Store(K(Int, 0), 78, 1)))))))],
 k!950 = [else ->
          If(-4 <= Var(0),
             If(-3 <= Var(0),
                If(-2 <= Var(0),
                   If(-1 <= Var(0),
                      If(0 <= Var(0),
                         If(1 <= Var(0),
                            If(2 <= Var(0), 2, 1),
                            0),
                         -1),
                      -2),
                   -3),
...

========================================

---

TIMEOUT: Model search exceeded maximum time of 5 seconds
No model for example BM_CM_2 found before timeout.
Try increasing max_time > 5.

========================================

EXAMPLE BM_CM_2: there is no countermodel.

Atomic States: 2

Semantic Theory: Bimodal

Premise:
1. \Past A

Conclusion:
2. \Box A

Z3 Run Time: 5.0004 seconds

========================================
UNSATISFIABLE CORE CONSTRAINTS:
- Frame constraints: 0
- Model constraints: 0
- Premise constraints: 0
- Conclusion constraints: 0
