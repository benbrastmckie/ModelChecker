# NOTE: go in API
from syntactic import(
    Sentence,
)


# COMPLEXITY
example = "((A \\leftrightarrow (D \\wedge C)) \\wedge (A \\rightarrow (B \\wedge C)))"
sent = Sentence(example)
prefix = sent.prefix(example)
print(prefix)
letters, ops, subs, comp = sent.constituents_of(prefix)
print(f"{len(letters)} sentence letters {letters}")
print(f"{len(ops)} operators {ops}")
print(f"{len(subs)} subsentences {subs}")
print(f"complexity {comp}")

