---
title: "Z3 timing variance dictates generous max_time budgets"
created: 2026-07-24
tags: [INSIGHT, testing, z3, flakiness]
topic: "modelchecker/testing/solver-timing"
source: "user input"
modified: 2026-07-24
keywords: [max_time, z3, timeout, timing-variance, pytest]
summary: "Z3 solve times vary ~20x run-to-run in ModelChecker; because a timeout is reported as model_found == False rather than an error, tight max_time budgets silently invert test conclusions."
retrieval_count: 0
last_retrieved:
category: INSIGHT
---

# Z3 timing variance dictates generous max_time budgets

Z3 solve times in ModelChecker vary roughly **20x run-to-run for the same formula on the same
machine**. Measured across repeated invocations of one unchanged bimodal countermodel test:
0.69s, 1.37s, 1.85s, 1.98s, and 15.08s. The variance tracks machine load, not test order.

## Why this is dangerous, not merely slow

Exceeding `max_time` is reported as `model_found == False` — **not** as an error. A timeout is
therefore indistinguishable from a genuine "no countermodel exists" result at the assertion site.
A test whose budget sits near its typical solve time does not fail loudly; it silently inverts its
semantic conclusion under load.

## Never size max_time from measured time plus a small margin

A ~1.7s solve was given a 10s budget — a ~6x margin — and **still** failed at 10.11s inside a
full-suite run. 30s is the working convention from sibling bimodal examples.

Omitting `max_time` entirely inherits `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS['max_time'] = 1`,
which is below the real solve time for many non-trivial formulas.

## Debugging corollary: suspect the budget before suspecting state leakage

When a test's outcome changes depending on how it is invoked (isolated vs file-scope vs
full-suite), check the timeout budget **first**. Solver isolation is already deliberate and
verified:

- `models/structure.py` creates a fresh solver context per solve
- `settings/settings.py` copies default dicts before merging (no in-place mutation)
- no memoization anywhere in the settings or model layers

Two independent investigations of apparent order-dependence in this repo both traced to timeout
races, not shared state.

## Concurrency and repeat-sweep variance

Concurrent pytest sessions in the same sandbox measurably affect each other's timing-sensitive
outcomes, and can kill a long suite outright via resource pressure. Before launching long or
timing-sensitive runs, check `ps aux | grep pytest` for a clear window, and use `pytest -n N` to
shrink the collision window.

Repeat full sweeps have differed from each other by several failures with no intervening code
change — so wall-clock assertions need generous tolerances or an opt-in marker.

## Where this is documented durably

`code/docs/core/TESTING_GUIDE.md` section 8.6, "Solver Timing Budgets and Machine Variance".

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
