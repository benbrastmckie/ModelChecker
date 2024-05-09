# TITLE: testabc

"""

There are no 3-models of:

\neg (A vee neg A)

# unsatisfiable core constraints
1. And(Exists(f_x, And(f_x | w == w, falsify(f_x, A))),
    Exists(t_x, And(t_x | w == w, verify(t_x, A))))

2. ForAll([frame_x, frame_y],
       Exists(frame_z, frame_x | frame_y == frame_z))

"""
