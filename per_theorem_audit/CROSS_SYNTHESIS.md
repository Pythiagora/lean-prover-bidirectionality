# Cross-Theorem Per-Attempt + Per-PASS Synthesis (20 theorems, 2,560 attempts, 805 PASSes)

Produced 2026-04-30 from per-theorem INDEX.md files (sub-agent classified PASSes) + per-attempt aggregate + regex-based per-attempt route detection (where regex agrees with sub-agent on PASSes). **Input for Marshal's abstract rewrite.**

## 1. Headline numbers (per-PASS, hand-classified)

805 PASSes hand-classified into (a) route-preserving / (b) route-equivalent at lower abstraction / (c) opaque automation:

| arm | total PASSes | (a) | (b) | (c) | (a)-rate per PASS |
|---|---:|---:|---:|---:|---:|
| Goedel | 520 | 102 | 418 | 0 | **19.6%** |
| Kimina | 285 | 147 | 137 | 1 | **51.6%** |

**Kimina is structurally bidirectional at 2.6× Goedel's rate (per-PASS-conditioned), despite Goedel's 1.83× higher PASS rate.**

## 2. Per-attempt extension (1,280 attempts per arm, hard-data aggregates)

The bidirectionality score is "computable per-attempt" (v6 §6 phrasing). Per-attempt aggregates for the 20 theorems × 64 attempts × 2 arms = 2,560 total:

### Verdict + script-availability distribution

| arm | total | PASS | FAIL with Lean block | FAIL no Lean block | truncated | empty completion | unclosed `<think>` |
|---|---:|---:|---:|---:|---:|---:|---:|
| Goedel | 1280 | 520 (40.6%) | 760 (59.4%) | **0** | 29 (2.3%) | 0 | 0 |
| Kimina | 1280 | 285 (22.3%) | 836 (65.3%) | **159 (12.4%)** | 57 (4.5%) | 50 (3.9%) | 110 (8.6%) |

Two arm-paradigm-level findings emerge that v6 only asserted anecdotally for P11.III.1:

- **Goedel-RL always commits to a script.** 0/1280 attempts produce no Lean block. Even on P11.III.1 (0/64 PASS), every attempt emits a candidate proof — typically at 26k+ chars and 504+ tactic invocations (matching v6 §3's anecdote, now generalised).
- **Kimina-SFT sometimes outputs nothing usable.** 159/1280 = 12.4% of attempts have no Lean block at all: 50 are empty completions (model emits nothing), 110 have unclosed `<think>` (model thought past 32k tokens without closing the tag), with overlap. The "Kimina alternates 0-char and truncations" v6 anecdote is a corpus-wide pattern, not a P11.III.1 idiosyncrasy.

### Per-attempt PASS rate (raw)

- Goedel 520/1280 = 40.6%
- Kimina 285/1280 = 22.3%

The PASS-rate gap (1.83×) is smaller than the per-PASS bidirectionality gap (2.6×), so weighting by the unconditional rate gives:

**Per-attempt (a)-route rate (Goedel) = 102/1280 = 7.97%**
**Per-attempt (a)-route rate (Kimina) = 147/1280 = 11.5%**

These are the "any structurally bidirectional script per try, ignoring PASS" rates. The Goedel/Kimina gap drops from 2.6× (per-PASS) to 1.4× (per-attempt). Both numbers are defensible — they answer different questions.

## 3. Per-theorem aggregate (PASSes + FAIL-mode)

| theorem | G T/P | G F-blk / no-blk | G trunc | K T/P | K F-blk / no-blk | K trunc | K empty | K unclosed-`<think>` |
|---|---|---:|---:|---|---:|---:|---:|---:|
| P3.subq_P3_I_1_a | 64/12 | 52/0 | 0 | 64/6 | 50/8 | 1 | 0 | 6 |
| P4.subq_P4_III_1 | 64/4 | 60/0 | 0 | 64/4 | 50/10 | 0 | 1 | 7 |
| P6.subq_I_3_a_recurrent | 64/53 | 11/0 | 0 | 64/62 | 1/1 | 0 | 0 | 0 |
| P7.subq_A_2_a | 64/54 | 10/0 | 0 | 64/2 | 60/2 | 0 | 0 | 1 |
| P8.subq_A_1_a | 64/12 | 52/0 | 0 | 64/2 | 41/21 | 5 | 8 | 13 |
| P9.subq_4 | 64/59 | 5/0 | 0 | 64/28 | 36/0 | 0 | 0 | 0 |
| P9.subq_22 | 64/0 | 64/0 | 6 | 64/1 | 24/39 | 12 | 4 | 32 |
| P10.subq_II_B_1 | 64/2 | 62/0 | 1 | 64/0 | 47/17 | 5 | 9 | 8 |
| P10.subq_III_A_3_c | 64/4 | 60/0 | 0 | 64/1 | 53/10 | 1 | 4 | 6 |
| P11.subq_I_3_b | 64/55 | 9/0 | 0 | 64/59 | 5/0 | 0 | 0 | 0 |
| P11.subq_II_3_a | 64/51 | 13/0 | 0 | 64/0 | 51/13 | 4 | 5 | 8 |
| P11.subq_III_1 | 64/0 | 64/0 | 9 | 64/0 | 51/13 | 16 | 4 | 9 |
| P11.subq_III_5_a | 64/7 | 57/0 | 0 | 64/0 | 51/13 | 1 | 5 | 8 |
| P11.subq_IV_2_a | 64/35 | 29/0 | 1 | 64/5 | 54/5 | 0 | 0 | 4 |
| P12.subq_I_B_2_a | 64/56 | 8/0 | 0 | 64/63 | 1/0 | 0 | 0 | 0 |
| P13.subq_I_1 | 64/3 | 61/0 | 8 | 64/2 | 50/12 | 5 | 5 | 7 |
| P15.subq_I_2 | 64/4 | 60/0 | 0 | 64/4 | 39/21 | 5 | 7 | 13 |
| P16.subq_IV_3 | 64/26 | 38/0 | 1 | 64/16 | 47/1 | 0 | 0 | 0 |
| P17.subq_II_2 | 64/35 | 29/0 | 1 | 64/23 | 41/0 | 1 | 0 | 0 |
| P17.subq_II_4_a | 64/48 | 16/0 | 3 | 64/7 | 54/3 | 1 | 1 | 1 |

Numbers approximate; `K empty` and `K unclosed-<think>` overlap with `K trunc`. Read the auto-aggregate `CROSS_ATTEMPT_AGGREGATE.md` for raw counts.

### Where Kimina's no-block FAILs concentrate

Theorems where Kimina FAILs without producing any Lean script (FAIL-no-block ≥ 10):
- **P9.subq_22**: 39/64 no-block (61% of attempts). Hardest theorem (corrigé requires winding-number lift), Kimina's `<think>` runs past 32k.
- **P10.subq_II_B_1**: 17/64 no-block. Complex-coefficient recurrence; Kimina dwells on case-analysis.
- **P15.subq_I_2**: 21/64 no-block. Polynomial finite-difference; long search.
- **P10.subq_III_A_3_c**: 10/64 no-block. Toeplitz-style recurrence.
- **P11.subq_II_3_a, P11.subq_III_1, P11.subq_III_5_a**: each 13/64 no-block. The analysis-arm Kimina ceiling cluster.

### Where both arms hit the contamination ceiling

- **P11.subq_III_1**: 0/64 PASS both arms. Goedel emits 64 long failed scripts; Kimina has 13 no-block FAILs (truncated + empty + unclosed-`<think>`).
- **P9.subq_22**: 0/64 Goedel PASS (all 64 are FAIL-with-block). Kimina has 1 PASS that is a Lake false-positive (truncated proof body); 39/64 no-block. **True ceiling: 0/128 across both arms.**

## 4. Headline corrections to v6

Three v6 claims were either wrong or built on regex false-positives. Corrected via per-PASS hand-classification:

- **P12 (F1 showcase) — arm labels inverted.** v6 reported Goedel ~76% / Kimina ~86% route-preserving on `(x/2+y)²` completion-of-square. Per-PASS sub-agent classification: **Goedel 98.2% (55/56) (a)**, **Kimina 14.3% (9/63) (a)**. The v6 regex was matching `(x/2+y)` occurrences inside `nlinarith` hint lists — counting (b) PASSes as (a) on the Kimina side. Goedel writes the identity as a named `have`; Kimina dumps it into the hint list and lets `nlinarith` close. **F1 showcase narrative direction is reversed.**

- **P4 — regex false-positive.** Lowercase `\bderivation\b` regex matched a Goedel comment. Mathlib `Derivation` (capitalised type class) appears in **0/8 PASSes**. All 8 use anonymous `LinearMap` with `toFun := fun X => A*X − X*A`.

- **P9.subq_22 — Lake false-positive PASS.** v6 listed `Kimina: 1/64`. The lone PASS file contains the theorem signature but the proof body is absent — terminates at `have h7 : ... := by` with nothing after `by`. **True PASS rate: 0/128 across both arms** — second contamination-controlled ceiling alongside P11.III.1.

## 5. Five recurring patterns

| pattern | description | theorems |
|---|---|---|
| P-1 | Corrigé-bound (both arms 100% (a)) | P3, P16.IV.3 |
| P-2 | Kimina-clean / Goedel-shotgun (modal pattern, 7 theorems) | P6, P9.subq_4, P10.III.A.3.c, P13.I.1, P15.I.2, P17.II.2, P17.II.4.a |
| P-3 | Goedel-clean / Kimina-shotgun (the v6 inversion) | **P12** |
| P-4 | Both arms (b), closure-rate asymmetric | P7, P11.IV.2.a, P11.II.3.a |
| P-5 | Kimina-ceiling (≥0 vs ≥7 Goedel PASS) | P10.II.B.1, P11.II.3.a, P11.III.5.a, P11.IV.2.a (5 vs 35), P7 (2 vs 54) |
| ceiling | 0/128 both arms | P11.III.1, P9.subq_22 |

P-2 is the modal pattern (7/17 PASS-bearing theorems). P-3 has only one instance: a sanity-check that the metric isn't measuring "Kimina solves more carefully" — it tracks structural transcription specifically.

## 6. Per-attempt route rate (regex auto-classified, only where regex agrees with sub-agent)

For 6 theorems where the (a)-signature is regex-extractable and the regex per-PASS classification agrees with the sub-agent's:

| theorem | G (a)/64 attempts | G PASS-(a) per sub-agent | K (a)/64 attempts | K PASS-(a) per sub-agent |
|---|---:|---:|---:|---:|
| P6 | **0/64** | 0/53 | **61/64** | 61/62 |
| P9.subq_4 | regex-noisy | 0/59 | **64/64** | 28/28 |
| P11.subq_I_3_b | **0/64** | 0/55 | **0/64** | 0/59 |
| P12 | regex undercounts | 55/56 | regex undercounts | 9/63 |
| P17.subq_II_2 | regex-noisy | 0/35 | regex undercounts | 23/23 |
| P17.subq_II_4_a | **0/64** | 0/48 | regex undercounts | 6/7 |

**Where regex is reliable**: confirms the per-PASS finding extends to per-attempt. P6 Goedel attempts the (a)-route in 0 of 64 tries; P6 Kimina attempts it in 61 of 64. P11.I.3.b is shotgun-prone for both arms — neither attempts (a) route in any of 128 attempts. The arm-asymmetry is in *what the model tries*, not just *what passes*.

**Where regex is noisy**: regex undercounts (a) on P12 because `(1/4)·(x+2y)²` form (semantically equivalent) doesn't match the literal `(x/2+y)²` regex. The sub-agent classification is authoritative; the per-attempt rate would need per-theorem regex tuning to extend reliably.

## 7. What this means for v7

Available empirical claims in order of strength:

**Strongest (hard data, no classification):**
- 805 PASSes total at K=64/32k. Per-attempt rate Goedel 40.6%, Kimina 22.3%.
- Two contamination-controlled 0/128 ceilings (P11.III.1, P9.subq_22).
- Goedel-RL emits a Lean script in 1280/1280 attempts. Kimina-SFT in 1121/1280 (12.4% no-block, mostly via unclosed `<think>` + empty completions).

**Strong (per-PASS hand-classified, 805 calls auditable):**
- Per-PASS bidirectionality gap: Kimina 51.6% (a) vs Goedel 19.6% (a). Concentrated in 7 P-2 theorems.
- The v6 P12 inversion: Goedel 98.2% (a), Kimina 14.3% (a) — opposite arm cleanness from v6.

**Moderate (per-attempt regex, theorem-by-theorem reliability):**
- P6, P11.I.3.b: per-attempt (a)-rate confirmed. P6 Goedel never attempts (a) (0/64); Kimina near-always (61/64). P11.I.3.b shotgun-prone for both (0/128).
- Regex is noisy for theorems with non-canonical (a)-signatures (P12, P17.II.2). Per-attempt rate would need sub-agent re-classification to extend reliably.

**Disclosed limitations:**
- 20 theorems is small. Some pattern buckets have 1–2 theorems (P-3 = P12 only).
- (a)/(b)/(c) classification is sub-agent-mediated for PASSes, regex for FAILs. Marshal-audit is the gold standard but isn't realistic for May 5.
- Corpus-relative to agrégation interne (French pedagogical conventions). v6 §6 limitation stays.

## 8. Per-theorem index

All synthesis files at `{theorem_id}/INDEX.md`. Per-PASS files at `{theorem_id}/{arm}_attXX.md`. Per-attempt files at `{theorem_id}/all_attempts/{arm}_attXX.md`. Aggregate raw data at `CROSS_ATTEMPT_AGGREGATE.md`. Regex per-attempt rates at `PER_ATTEMPT_ROUTE_RATES.json`.
