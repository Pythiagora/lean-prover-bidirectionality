# Selection summary — 20 focal theorems

Per-theorem mapping of the 20 focal theorems to corrigé abstraction level (annotated pre-K64) and K=64 PASS counts (from the run reported in the AITP 2026 abstract). The K=8 pilot band assignments that drove the original stratification are tracked in private notes (band thresholds: saturated 8/8, sweet-spot 1–7/8, low-PASS 1/8, 0-baseline 0/8 at the K=8 Goedel pilot) and were not regenerated for this release. The K=64 PASS counts below are the actual evaluation data and are independently verifiable from `verdicts/{goedel,kimina}.json`.

| Theorem ID | Problem | Subject | Level (pre-K64) | Goedel n_PASS @ K=64 | Kimina n_PASS @ K=64 |
|---|---:|---|---|---:|---:|
| P3.subq_P3_I_1_a | 3 | analysis | concrete | 12 | 6 |
| P4.subq_P4_III_1 | 4 | algebra | abstract | 4 | 4 |
| P6.subq_I_3_a_recurrent | 6 | algebra | concrete | 53 | 62 |
| P7.subq_A_2_a | 7 | algebra | abstract | 54 | 2 |
| P8.subq_A_1_a | 8 | algebra | standard | 12 | 2 |
| P9.subq_4 | 9 | analysis | standard | 59 | 28 |
| P9.subq_22 | 9 | algebra | abstract | 0 | 1 |
| P10.subq_II_B_1 | 10 | analysis | concrete | 2 | 0 |
| P10.subq_III_A_3_c | 10 | analysis | concrete | 4 | 1 |
| P11.subq_I_3_b | 11 | analysis | standard | 55 | 59 |
| P11.subq_II_3_a | 11 | analysis | standard | 51 | 0 |
| P11.subq_III_1 | 11 | analysis | abstract | 0 | 0 |
| P11.subq_III_5_a | 11 | analysis | standard | 7 | 0 |
| P11.subq_IV_2_a | 11 | analysis | standard | 35 | 5 |
| P12.subq_I_B_2_a | 12 | algebra | concrete | 56 | 63 |
| P13.subq_I_1 | 13 | analysis | standard | 3 | 2 |
| P15.subq_I_2 | 15 | algebra | abstract | 4 | 4 |
| P16.subq_IV_3 | 16 | analysis | standard | 26 | 16 |
| P17.subq_II_2 | 17 | analysis | concrete | 35 | 23 |
| P17.subq_II_4_a | 17 | analysis | concrete | 48 | 7 |

**Subject distribution.** 7 algebra (P4, P6, P7, P8, P9.subq_22, P12, P15) + 13 analysis = 20.

**Level distribution.** 7 concrete + 8 standard + 5 abstract = 20.

**Abstraction-level annotation** was applied pre-K64 based on the corrigé-route abstraction. See `analysis/abstraction_level_verify.py` for the route patterns (`route_pattern`) and lower-level detour patterns (`lower_level_pattern`) per theorem.

**K=64 PASS rate sanity check.** Aggregate Goedel = 520 / 1280 = 40.6%; Kimina = 285 / 1230 = 23.2%. (Kimina has 1230 attempts because 50 attempts errored or timed-out at the network layer and were not retried within the 9h wall-clock budget.)
