from z3 import (
    Solver,
    BitVec,
    BitVecs,
    BitVecVal,
    Not,
    And,
    simplify,
    Bools,
    Or,
    unsat,
    solve,
)



Tie, Shirt = Bools("Tie Shirt")
s = Solver()
s.add(Or(Tie, Shirt), Or(Not(Tie), Shirt), Or(Not(Tie), Not(Shirt)))
print(s.check())
print(s.model())


p, q = Bools("p q")
demorgan = And(p, q) == Not(Or(Not(p), Not(q)))
# print (demorgan)


def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print("proved")
    else:
        print("failed to prove")

print(bool(BitVecVal(0,5)))
# print ("Proving demorgan...")
# prove(demorgan)

bitvec_attempt = BitVec("bitty", 4)
print(bitvec_attempt)
x = BitVec("x", 16)
y = BitVec("y", 16)
print(x + 2)
# Internal representation
print((x + 2).sexpr())

# -1 is equal to 65535 for 16-bit integers
print(simplify(x + y - 1))

# Creating bit-vector constants
a = BitVecVal(-1, 16)
b = BitVecVal(65535, 16)
print(simplify(a == b))  # this shows that the bitvector wraps around

a = BitVecVal(-1, 32)
b = BitVecVal(65535, 32)
# -1 is not equal to 65535 for 32-bit integers bc it doesn't wrap around yet
print(simplify(a == b))
print(b.sexpr())
# is there a difference between saying `b = 5` for a bitvector `b` and saying `b = a` for another bitvector `a`?

# Create two bit-vectors of size 32
x, y = BitVecs("x y", 32)

# solve(x + y == 2, x > 0, y > 0)

# Bit-wise operators
# & bit-wise and
# | bit-wise or
# ~ bit-wise not
# solve(x & y == ~y)

solve(x < 0)

# using unsigned version of <
# solve(ULT(x, 0))


a, b = BitVecs("a b", 4)
solve(x | y == 6, y != 0, x != 0)
# it just goes all the way down on one (x), and then goes to the other (y).
# Nvm, seems more complicated than that, but kinda loosely that if you squint
print(a)


def is_atomic(bit_vector):
    return simplify(
        And(bit_vector != 0, 0 == (bit_vector & (bit_vector - 1)))
    )  # this is taken from a Z3 documentation place thing

def fusion(bit_s, bit_t):
    fused = bit_s | bit_t  # | is the or operator
    return simplify(
        fused
    )  # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object.

def is_part_of(bit_s, bit_t):
    return (
        fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
    )  # testing if fusion equals bit_t, as definition does
    # adding the sexpr()s above seemed to do the trick, not sure why.

def total_fusion(list_of_states):
    '''returns the fusion of a list of states'''
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2: # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion([fusion_of_first_two]+list_of_states[2:])
    new_list_of_states = [fusion_of_first_two]
    new_list_of_states.extend(list_of_states[2:])
    return total_fusion(new_list_of_states)

#short program to test total_fusion
atomic_states = []
for i in range(500): # this short for loop tests is_atomic. Uncomment it to use it; it works.
    bitvec = BitVecVal(i,9)
    if is_atomic(bitvec):
        print(bitvec.sexpr())
        atomic_states.append(bitvec)
print(atomic_states)
print(total_fusion(atomic_states).sexpr()) # prints #b111111111—so total_fusion works!

# we can set a bitvector equal to a number with BitVecVal(value, bits).
# THIS type of bitvector can be represented as a vector with self.sexpr()
# I'm honestly not sure what the BitVec class by itself is good for.
# also hexadecimal vs binary representation issue (easy fix, just need to be on same page)
# NOTE: what is the hexadecimal vs binary issue?
a = BitVec("a", 5)
x = BitVecVal(5, 5)  # x.sexpr() = #b00101
# print(type(a) == type(x)) # is False

y = BitVecVal(4, 5)  # y.sexpr() = #b00100
z = BitVecVal(2, 5)  # z.sexpr() = #b00010
alpha = fusion(x, y)  # want to print a BitVecNumRef with sexpr #b00101
print("THIs is alpha:", alpha, alpha.sexpr())
# print(alpha.sort()) # return BitVec(5)
# print(alpha.sexpr()) # prints (bvor #b00101 #b00100)
alpha_simplified = simplify(alpha)
print(alpha_simplified, alpha_simplified.sexpr())  # perfect! got it to work
print(is_part_of(y, x))  # want this to print True
print(is_part_of(z, x))  # want this to print False

beta = BitVecVal(21, 4)  # z.sexpr() = #b00010
print(beta.sexpr())
# next step could be making a class on python for states.
