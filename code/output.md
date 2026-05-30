# Dual-Solver Timing Comparison

- **Timestamp**: 2026-04-03T12:42:54
- **Z3 Version**: 4.15.8
- **CVC5 Version**: 1.3.3-modified
- **Total Examples**: 24
- **Curated**: Yes
- **Total Runtime**: 6.01s

## Timing Summary

| Metric | Z3 | CVC5 |
|--------|---:|-----:|
| Total Time | 2.3224s | 3.6784s |
| Avg Time | 0.096765s | 0.153266s |
| Fastest | FO_TH_5 (0.0068s) | FO_TH_5 (0.0049s) |
| Slowest | CF_CM_1 (0.5017s) | CF_CM_1 (0.6901s) |

## Comparison Statistics

| Metric | Value |
|--------|------:|
| Agreements | 24 |
| Disagreements | 0 |
| Z3 Faster | 18 |
| CVC5 Faster | 6 |
| Ties | 0 |
| Avg Time Ratio | 1.62x |

## Example Results

| Example | Z3 (s) | CVC5 (s) | Agree | Faster | Ratio |
|---------|-------:|--------:|:-----:|:------:|------:|
| EXT_TH_1 | 0.041841 | 0.045840 | Yes | z3 | 1.10x |
| EXT_TH_7 | 0.029286 | 0.041511 | Yes | z3 | 1.42x |
| EXT_CM_1 | 0.026855 | 0.026089 | Yes | cvc5 | 1.03x |
| EXT_CM_2 | 0.109773 | 0.160403 | Yes | z3 | 1.46x |
| MOD_TH_5 | 0.081626 | 0.116500 | Yes | z3 | 1.43x |
| MOD_TH_3 | 0.040865 | 0.058053 | Yes | z3 | 1.42x |
| MOD_CM_1 | 0.084899 | 0.088252 | Yes | z3 | 1.04x |
| MOD_CM_3 | 0.076703 | 0.088385 | Yes | z3 | 1.15x |
| CL_TH_1 | 0.064901 | 0.130097 | Yes | z3 | 2.00x |
| CL_TH_16 | 0.022624 | 0.019315 | Yes | cvc5 | 1.17x |
| CL_CM_1 | 0.221683 | 0.339038 | Yes | z3 | 1.53x |
| CL_CM_7 | 0.242444 | 0.205060 | Yes | cvc5 | 1.18x |
| CF_TH_1 | 0.074936 | 0.196830 | Yes | z3 | 2.63x |
| CF_TH_2 | 0.088022 | 0.318553 | Yes | z3 | 3.62x |
| CF_CM_1 | 0.501745 | 0.690141 | Yes | z3 | 1.38x |
| CF_CM_7 | 0.146713 | 0.299049 | Yes | z3 | 2.04x |
| REL_TH_1 | 0.045280 | 0.063733 | Yes | z3 | 1.41x |
| REL_TH_7 | 0.033238 | 0.085865 | Yes | z3 | 2.58x |
| REL_CM_1 | 0.195835 | 0.464386 | Yes | z3 | 2.37x |
| REL_CM_3 | 0.078350 | 0.113554 | Yes | z3 | 1.45x |
| FO_TH_1 | 0.021267 | 0.042209 | Yes | z3 | 1.98x |
| FO_TH_5 | 0.006768 | 0.004853 | Yes | cvc5 | 1.39x |
| FO_CM_1 | 0.019224 | 0.018852 | Yes | cvc5 | 1.02x |
| FO_CM_3 | 0.067482 | 0.061817 | Yes | cvc5 | 1.09x |
