# NOTE: go in API
from syntactic import(
    Sentence,
)


# COMPLEXITY
example = "((A \\rightarrow (B \\wedge C)) \\wedge (A \\rightarrow (B \\wedge C)))"
sent = Sentence(example)
prefix = sent.prefix(example)
print(prefix)
letters, subs, comp = sent.constituents_of(prefix)
print(f"{example} has sentence letters {letters}")
print(f"{example} has subsentences {subs}")
print(f"{example} has complexity {comp}")

