# NOTE: go in API
from syntactic import(
    Sentence,
)


# COMPLEXITY
example = "((A \\leftrightarrow \\neg \\neg (\\top \\wedge C)) \\wedge (A \\rightarrow (\\neg \\neg B \\wedge \\bot)))"
sent = Sentence(example)
prefix = sent.prefix(example)
print(prefix)
letters, subs, ops, comp = sent.constituents_of(prefix)
print(f"{len(letters)} sentence letters {letters}")
print(f"{len(ops)} operators {ops}")
print(f"{len(subs)} subsentences {subs}")
print(f"complexity {comp}")

