from z3 import *

Tie, Shirt = Bools("Tie Shirt")
s = Solver()
s.add(Or(Tie, Shirt), Or(Not(Tie), Shirt), Or(Not(Tie), Not(Shirt)))
# print(s.check())
# print(s.model())

p, q = Bools('p q')
demorgan = And(p, q) == Not(Or(Not(p), Not(q)))
# print (demorgan)

def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print ("proved")
    else:
        print ("failed to prove")

# print ("Proving demorgan...")
# prove(demorgan)

bitvec_attempt = BitVec('bitty',4)
print(bitvec_attempt)
x = BitVec('x', 16)
y = BitVec('y', 16)
print (x + 2)
# Internal representation
print ((x + 2).sexpr())

# -1 is equal to 65535 for 16-bit integers 
print (simplify(x + y - 1))

# Creating bit-vector constants
a = BitVecVal(-1, 16)
b = BitVecVal(65535, 16)
print (simplify(a == b)) # this shows that the bitvector wraps around

a = BitVecVal(-1, 32)
b = BitVecVal(65535, 32)
# -1 is not equal to 65535 for 32-bit integers bc it doesn't wrap around yet
print (simplify(a == b))
print (b.sexpr())


# Create to bit-vectors of size 32
x, y = BitVecs('x y', 32)

# solve(x + y == 2, x > 0, y > 0)

# Bit-wise operators
# & bit-wise and
# | bit-wise or
# ~ bit-wise not
# solve(x & y == ~y)

solve(x < 0)

# using unsigned version of < 
# solve(ULT(x, 0))


a,b = BitVecs('a b',4)
solve(x | y == 6, y != 0, x != 0) # it just goes all the way down on one (x), and then goes to the other (y). Nvm, seems more complicated than that, but kinda loosely that if you squint
print(a)
# here is a note
# here is another note

def is_atomic(bit_vector):
    return And(x != 0, 0 == (x & (x - 1))) # this is taken from a Z3 documentation place thing

def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t # I think this is the right OR operation?

def fusion(bit_s, bit_t): 
    return bit_s | bit_t
# seems that we set bitvectors just by setting it equal to a number. 
# I haven't found a way to actually see the bitvector itself. 