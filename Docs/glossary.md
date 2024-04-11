# Glossary

- This is a place to collect relevant commands, terms,... for reference.
- Entries should include a brief note as a reminder and any links to further information.
- Eventually I would like to turn this into a resources for others who are new to the project.
- For now, it is OK to use this as much or as little as is helpful.

## Z3

Checks whether a bit vector has a single non-zero value from [section 3.4](https://z3prover.github.io/papers/programmingz3.html#sec-sorts) of **Programming Z3**.

    def is_atomic(bit_vector):
        return And(
            bit_vector != 0, 0 == (bit_vector & (bit_vector - 1))
        ) 

The fusion of two bit vectors takes the greatest value for each entry.

    def fusion(bit_s, bit_t):
        fused = bit_s | bit_t  # | is the or operator
        return simplify(fused)  # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object. 

This provides an algebraic definition of parthood in terms of binary fusion.

    def is_part_of(bit_s, bit_t):
        return (
            fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
        )  # I think this is the right OR operation?
        # adding the sexpr()s above seemed to do the trick, not sure why.

This provides a fusion of a list of states.

    def total_fusion(list_of_states):
        '''returns the fusion of a list of states'''
        fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
        if len(list_of_states) == 2: # base case: fuse 2
            return fusion_of_first_two
        # recursive step: fuse first two and run the func on the next
        new_list_of_states = [fusion_of_first_two]
        new_list_of_states.extend(list_of_states[2:])
        return total_fusion(new_list_of_states)
