from z3 import (
    Solver,
    DeclareSort,
    Consts,
    Function,
)




# From: https://ericpony.github.io/z3py-tutorial/advanced-examples.htm

# Function and constant symbols in pure first-order logic are uninterpreted or free, which means that no a priori interpretation is attached.
# This is in contrast to arithmetic operators such as + and - that have a fixed standard interpretation.
# Uninterpreted functions and constants are maximally flexible; they allow any interpretation that is consistent with the constraints over the function or constant.

# To illustrate uninterpreted functions and constants let us introduce an (uninterpreted) sort A, and the constants x, y ranging over A.
# Finally let f be an uninterpreted function that takes one argument of sort A and results in a value of sort A.
# The example illustrates how one can force an interpretation where f applied twice to x results in x again, but f applied once to x is different from x.

A    = DeclareSort('A')
x, y = Consts('x y', A)
f    = Function('f', A, A)

s    = Solver()
s.add(f(f(x)) == x, f(x) == y, x != y)

print (s.check())
m = s.model()
print (m)
print ("interpretation assigned to A:")
print (m[A])

# The resulting model introduces abstract values for the elements in A, because the sort A is uninterpreted.
# The interpretation for f in the model toggles between the two values for x and y, which are different.
# The expression m[A] returns the interpretation (universe) for the uninterpreted sort A in the model m.


