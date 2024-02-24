# Glossary

- This is a place to collect relevant commands, terms,... for reference.
- Entries should include a brief note as a reminder and any links to further information.
- Eventually I would like to turn this into a resources for others who are new to the project.
- For now, it is OK to use this as much or as little as is helpful.

## Z3

Checks whether a bit vector has a single non-zero value.

    def is_atomic(bit_vector):
        return And(
            x != 0, 0 == (x & (x - 1))
        )  # this is taken from a Z3 documentation place thing

The fusion of two bit vectors takes the greatest value for each entry.

    def fusion(bit_s, bit_t):
        fused = bit_s | bit_t  # this 'or' function by itself isn't it
        return simplify(fused)  # this turns it from bvor to #b
        # NOTES: what do | and simplify do?

This provides an algebraic definition of parthood in terms of binary fusion.

    def is_part_of(bit_s, bit_t):
        return (
            fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
        )  # I think this is the right OR operation?
        # adding the sexpr()s above seemed to do the trick, not sure why.
