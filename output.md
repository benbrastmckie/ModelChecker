# Dual-Solver Timing Comparison

- **Timestamp**: 2026-04-03T11:33:49
- **Z3 Version**: 4.15.8
- **CVC5 Version**: 1.3.3-modified
- **Total Examples**: 24
- **Curated**: Yes
- **Total Runtime**: 20.71s

## Timing Summary

| Metric | Z3 | CVC5 |
|--------|---:|-----:|
| Total Time | 3.9777s | 16.7185s |
| Avg Time | 0.165737s | 0.696603s |
| Fastest | FO_TH_5 (0.0084s) | FO_TH_5 (0.0191s) |
| Slowest | CF_CM_1 (1.2238s) | CF_TH_2 (3.0082s) |

## Comparison Statistics

| Metric | Value |
|--------|------:|
| Agreements | 24 |
| Disagreements | 0 |
| Z3 Faster | 18 |
| CVC5 Faster | 6 |
| Ties | 0 |
| Avg Time Ratio | 9.25x |

## Example Results

| Example | Z3 (s) | CVC5 (s) | Agree | Faster | Ratio |
|---------|-------:|--------:|:-----:|:------:|------:|
| EXT_TH_1 | 0.044465 | 0.424858 | Yes | z3 | 9.55x |
| EXT_TH_7 | 0.037742 | 0.509182 | Yes | z3 | 13.49x |
| EXT_CM_1 | 0.029905 | 0.041205 | Yes | z3 | 1.38x |
| EXT_CM_2 | 0.126900 | 0.261089 | Yes | z3 | 2.06x |
| MOD_TH_5 | 0.078641 | 2.349381 | Yes | z3 | 29.87x |
| MOD_TH_3 | 0.047092 | 1.227560 | Yes | z3 | 26.07x |
| MOD_CM_1 | 0.095065 | 0.123345 | Yes | z3 | 1.30x |
| MOD_CM_3 | 0.150818 | 0.089928 | Yes | cvc5 | 1.68x |
| CL_TH_1 | 0.065383 | 2.319080 | Yes | z3 | 35.47x |
| CL_TH_16 | 0.024962 | 0.124603 | Yes | z3 | 4.99x |
| CL_CM_1 | 0.236657 | 0.452807 | Yes | z3 | 1.91x |
| CL_CM_7 | 0.282294 | 0.357861 | Yes | z3 | 1.27x |
| CF_TH_1 | 0.149012 | 1.558416 | Yes | z3 | 10.46x |
| CF_TH_2 | 0.096042 | 3.008219 | Yes | z3 | 31.32x |
| CF_CM_1 | 1.223842 | 0.960465 | Yes | cvc5 | 1.27x |
| CF_CM_7 | 0.644830 | 0.444369 | Yes | cvc5 | 1.45x |
| REL_TH_1 | 0.048388 | 1.101306 | Yes | z3 | 22.76x |
| REL_TH_7 | 0.036717 | 0.526844 | Yes | z3 | 14.35x |
| REL_CM_1 | 0.146095 | 0.406726 | Yes | z3 | 2.78x |
| REL_CM_3 | 0.214614 | 0.130254 | Yes | cvc5 | 1.65x |
| FO_TH_1 | 0.066036 | 0.166781 | Yes | z3 | 2.53x |
| FO_TH_5 | 0.008383 | 0.019053 | Yes | z3 | 2.27x |
| FO_CM_1 | 0.032543 | 0.030060 | Yes | cvc5 | 1.08x |
| FO_CM_3 | 0.091261 | 0.085072 | Yes | cvc5 | 1.07x |
