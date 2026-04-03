# Dual-Solver Timing Comparison

- **Timestamp**: 2026-04-03T11:15:02
- **Z3 Version**: 4.15.8
- **CVC5 Version**: 1.3.3-modified
- **Total Examples**: 24
- **Curated**: Yes
- **Total Runtime**: 18.69s

## Timing Summary

| Metric | Z3 | CVC5 |
|--------|---:|-----:|
| Total Time | 3.8102s | 14.8689s |
| Avg Time | 0.158760s | 0.619536s |
| Fastest | FO_TH_5 (0.0081s) | FO_TH_5 (0.0136s) |
| Slowest | CF_CM_1 (1.7819s) | CF_TH_2 (2.7098s) |

## Comparison Statistics

| Metric | Value |
|--------|------:|
| Agreements | 24 |
| Disagreements | 0 |
| Z3 Faster | 19 |
| CVC5 Faster | 5 |
| Ties | 0 |
| Avg Time Ratio | 9.37x |

## Example Results

| Example | Z3 (s) | CVC5 (s) | Agree | Faster | Ratio |
|---------|-------:|--------:|:-----:|:------:|------:|
| EXT_TH_1 | 0.042625 | 0.367695 | Yes | z3 | 8.63x |
| EXT_TH_7 | 0.028701 | 0.408214 | Yes | z3 | 14.22x |
| EXT_CM_1 | 0.027466 | 0.034608 | Yes | z3 | 1.26x |
| EXT_CM_2 | 0.122346 | 0.217637 | Yes | z3 | 1.78x |
| MOD_TH_5 | 0.071247 | 2.011514 | Yes | z3 | 28.23x |
| MOD_TH_3 | 0.044126 | 1.086310 | Yes | z3 | 24.62x |
| MOD_CM_1 | 0.091309 | 0.112866 | Yes | z3 | 1.24x |
| MOD_CM_3 | 0.118218 | 0.086435 | Yes | cvc5 | 1.37x |
| CL_TH_1 | 0.064375 | 2.205706 | Yes | z3 | 34.26x |
| CL_TH_16 | 0.024175 | 0.119995 | Yes | z3 | 4.96x |
| CL_CM_1 | 0.229359 | 0.405672 | Yes | z3 | 1.77x |
| CL_CM_7 | 0.302790 | 0.345253 | Yes | z3 | 1.14x |
| CF_TH_1 | 0.132844 | 1.462411 | Yes | z3 | 11.01x |
| CF_TH_2 | 0.089787 | 2.709831 | Yes | z3 | 30.18x |
| CF_CM_1 | 1.781852 | 0.796455 | Yes | cvc5 | 2.24x |
| CF_CM_7 | 0.176442 | 0.172598 | Yes | cvc5 | 1.02x |
| REL_TH_1 | 0.043642 | 1.029148 | Yes | z3 | 23.58x |
| REL_TH_7 | 0.034282 | 0.496513 | Yes | z3 | 14.48x |
| REL_CM_1 | 0.122809 | 0.341064 | Yes | z3 | 2.78x |
| REL_CM_3 | 0.140619 | 0.124297 | Yes | cvc5 | 1.13x |
| FO_TH_1 | 0.020363 | 0.221213 | Yes | z3 | 10.86x |
| FO_TH_5 | 0.008056 | 0.013556 | Yes | z3 | 1.68x |
| FO_CM_1 | 0.022927 | 0.019549 | Yes | cvc5 | 1.17x |
| FO_CM_3 | 0.069872 | 0.080317 | Yes | z3 | 1.15x |
