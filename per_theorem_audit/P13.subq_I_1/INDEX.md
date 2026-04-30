# P13.subq_I_1 — per-theorem deep dive

**Total PASSes**: 5 (3 Goedel + 2 Kimina); both arms at 3/64 and 2/64 respectively — near-floor pass rates indicating high difficulty.

## Statement

For `n ≥ 1`, prove `∃! u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ f n u = 0`, where `f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1`.

## Corrigé route summary

Existence: `f n 0 = -1 < 0`, `f n 1 = n - 1 ≥ 0`, continuity of polynomial → IVT → root in `[0,1]`. Uniqueness: `f n` strictly increasing on `[0,1]` (each term `x^(k+1)` strictly increases with `x`, so the sum does too) → at most one root.

Route classification:
- **(a) Route-preserving**: `intermediate_value_Icc` (or equivalent IVT lemma) for existence, named `StrictMonoOn` or `Finset.sum_lt_sum` via `pow_lt_pow_of_lt_left` for uniqueness.
- **(b) Lower-abstraction**: same logical skeleton but IVT invocation buried in a shotgun cascade (`simp_all`/`cases n`/`norm_num`/`linarith`), and/or uniqueness via inline `by_contra` + direct sum comparison without naming monotonicity.
- **(c) Opaque**: witness by coincidence or trivial case collapse.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque/degenerate |
|---|---:|---:|---:|---:|
| Goedel | 3 | 0 (0%) | 3 (100%) | 0 (0%) |
| Kimina | 2 | 2 (100%) | 0 (0%) | 0 (0%) |
| **Both** | **5** | **2 (40%)** | **3 (60%)** | **0 (0%)** |

No degenerate witness found: all five proofs correctly invoke IVT (or a continuous IVT-equivalent) and prove strict monotonicity via term-wise `pow_lt_pow_left`/`pow_lt_pow_of_lt_left`. The `∃!` is not trivialised.

## Per-PASS analysis

### Goedel — all (b) lower-abstraction

All three Goedel PASSes share a common macro-structure: large `have`-chain scaffolding (56–64 `have` nodes, 190–210 lines, 6626–7556 chars), `calc` blocks for sum comparisons, and a `simp_all`/`field_simp`/`ring_nf`/`linarith` shotgun for subgoals. None name a `StrictMonoOn` lemma; monotonicity is inlined via a `by_contra` + `lt_or_gt_of_ne` case split that duplicates the monotonicity argument twice (once per direction).

- **G-b1** (`goedel_att01.md`, 210 lines, 7174 chars): The deepest nesting. IVT invoked as `intermediate_value_Icc` with the condition discharged by a multi-`try` cascade (`cases n` + `simp_all [f_def, sum_range_succ]` + `linarith`). Uniqueness via `by_contra` + `h_strict_mono` helper have, itself closed by `Finset.sum_lt_sum` + `pow_lt_pow_of_lt_left`. Uses `tauto` for extracting `f n u₁ = 0` from the conjunction.

- **G-b2** (`goedel_att32.md`, 191 lines, 7556 chars): Structurally identical to G-b1 but uses `h_main_existence`/`h_main_uniqueness` as top-level named blocks. The IVT application (`intermediate_value_Icc`) has a noticeably messier fallback cascade: `simp_all [f_def]` + `norm_num at *` + `linarith` repeated twice. The `∑ 1^(k+1) = n` subgoal is closed via `Finset.sum_const`/`Finset.card_range` + `norm_cast`/`field_simp`/`ring` shotgun rather than `Finset.sum_range_succ`-induction.

- **G-b3** (`goedel_att44.md`, 190 lines, 6626 chars): The cleanest Goedel script. Uses `continuousOn_id.pow` for continuity (less verbose than G-b1/G-b2), and the IVT call is the same `intermediate_value_Icc` with a dual `cases' n` fallback cascade. Uniqueness is structured as a standalone `h₅` have proving `StrictMonoOn`-style `f n x < f n y`, then invoked inline; this is the closest a Goedel PASS comes to naming monotonicity, though it is not called `StrictMonoOn`.

### Kimina — all (a) route-preserving

Both Kimina PASSes are structurally leaner (142–161 lines, 4943–6436 chars) and use `Continuous` (global continuity) rather than `ContinuousOn`, which is a minor deviation from the corrigé but semantically equivalent.

- **K-a1** (`kimina_att08.md`, 142 lines, 4943 chars): Uses `Continuous.exists_mem_set_of_le_of_lt_of_continuous` as the IVT lemma — a non-standard name that may reflect a Mathlib API variant. Continuity proved via `continuity` tactic after `funext`-rewriting `f n`. Uniqueness via `by_cases h15 : d < c` / `by_cases h17 : d > c`, with strict monotonicity proved inline using `Finset.sum_lt_sum` + `pow_lt_pow_left`; no `0` index trick. No `calc` blocks, no `simp_all`, no `field_simp`.

- **K-a2** (`kimina_att48.md`, 161 lines, 6436 chars): Uses `Continuous.exists_eq_of_le_of_le` as the IVT lemma. Proves `∑ 1^(k+1) = n` by induction on `n` with `Finset.sum_range_succ` (route-aligned). Uniqueness by `by_cases h15 : v < u` / `by_cases h16 : v > u`, with strict sum comparison via `Finset.sum_lt_sum`; uses `pow_le_pow_left` + `pow_lt_pow_left` for the term-wise argument. More explicit case structure than K-a1; uses `tauto` for membership extraction in the `use 0` step.

The two Kimina scripts invoke different IVT lemma names (`exists_mem_set_of_le_of_lt_of_continuous` vs `exists_eq_of_le_of_le`), suggesting the CoT searched for IVT by description rather than by recalling a canonical name.

## Cross-arm divergence

The arm split is clean: all Goedel PASSes land in (b), all Kimina PASSes in (a). The divergence is not in logical structure — both arms use IVT + strict monotonicity via `Finset.sum_lt_sum` + `pow_lt_pow_left` — but in how these components are assembled. Goedel wraps the proof in a large `have`-chain with a duplicated uniqueness argument (the `by_contra` case split is written out fully twice, once per direction), and relies on `simp_all` shotguns to close side conditions. Kimina avoids `simp_all` entirely (0/2 files), uses `nlinarith` instead of `linarith`+`ring_nf` for arithmetic, and never uses `field_simp`. Char-len ratio is roughly 1.2–1.5× Goedel-over-Kimina, smaller than in P6 (where the ratio was up to 6×), consistent with this theorem requiring a genuinely long proof for both arms. The `uses_Continuous` flag separates the arms sharply: 2/2 Kimina vs 0/3 Goedel (Goedel uses `ContinuousOn` instead).

## Bidirectionality verdict

Kimina's two scripts are weakly bidirectional: the IVT invocation and the term-wise monotonicity argument (`pow_lt_pow_left` per summand, summed by `Finset.sum_lt_sum`) correspond directly to the two named corrigé moves, and a reader can reconstruct both steps. Goedel's scripts carry the same logical moves but the IVT side-condition discharge is absorbed into a multi-`try` cascade that does not expose the key step (`f n 0 = -1`, `f n 1 = n - 1`) as named intermediate claims; the reasoning is recoverable by inspection but not by reading the tactic structure alone.
