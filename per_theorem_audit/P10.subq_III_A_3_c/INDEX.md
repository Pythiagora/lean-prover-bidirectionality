# P10.subq_III_A_3_c — per-theorem deep dive

**Total PASSes**: 5 (4 Goedel + 1 Kimina) — near-floor PASS counts (Goedel 4/64, Kimina 1/64)

## Statement

Given `x : ℕ → ℕ → ℂ` satisfying `x (n+1) k = (1/((k:ℂ)+1)) * ∑ j ∈ Finset.range (k+1), x n j`,
show `x (n+1) (k+1) = (1/((k:ℂ)+2)) * x n (k+1) + (1/((k:ℂ)+2)) * ∑ j ∈ Finset.range (k+1), x n j`.

## Corrigé route

Apply `hx_rec` at `(n, k+1)` to get `x (n+1) (k+1) = (1/((k:ℂ)+2)) * ∑ j ∈ Finset.range (k+2), x n j`.
Split the range-`(k+2)` sum via `Finset.sum_range_succ` to extract `x n (k+1)`. Distribute and close by `ring`.
Named moves: (1) recurrence instantiation, (2) `Finset.sum_range_succ` split, (3) distributivity (`ring`).

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 4 | 0 (0%) | 4 (100%) | 0 (0%) |
| Kimina | 1 | 1 (100%) | 0 (0%) | 0 (0%) |
| **Both** | **5** | **1 (20%)** | **4 (80%)** | **0 (0%)** |

## Per-PASS analysis

### Goedel — all (b) lower-abstraction (4/4)

All four Goedel PASSes share the same macro structure: a chain of `have` lemmas stepping through
(h1) apply `hx_rec`, (h2) simplify the cast denominator `((k+1:ℕ):ℂ)+1 = (k:ℂ)+2`, (h3) apply
`Finset.sum_range_succ`, (h4/h5) substitute and distribute. The corrigé structure is present at
the coarse level, but each step is closed by an overlong tactic cascade rather than a single
`ring` or `norm_cast`.

- **goedel_att13.md** (73 lines, 2680 chars, 11 `have`s): most verbose. The denominator
  simplification h2 is closed by `norm_cast <;> simp [add_assoc] <;> ring_nf <;> norm_num
  <;> simp_all [Complex.ext_iff] <;> norm_num <;> linarith`. The distributivity step h6
  is similarly closed by a 5-tactic cascade. `Finset.sum_range_succ` is called inside h4,
  but is followed by `ring_nf <;> simp_all <;> linarith` rather than a direct rewrite. Route
  structure legible; arithmetic closures opaque.

- **goedel_att25.md** (52 lines, 2393 chars, 7 `have`s, 2 `calc`): uses `calc` blocks to
  sequence the steps explicitly — the most readable Goedel PASS. The denominator cast `h3` is
  still closed by `norm_cast <;> field_simp <;> ring_nf <;> norm_num <;> simp_all <;> linarith`.
  `Finset.sum_range_succ` appears in h4 via `rw [Finset.sum_range_succ, add_comm]`. `mul_add`
  distributivity is not used; the final `ring_nf <;> simp_all <;> linarith` shotgun closes h_final.

- **goedel_att28.md** (53 lines, 2127 chars, 8 `have`s): shortest Goedel PASS. Same h₁/h₃/h₄
  pattern; `h₃` denominator simplification closed by `norm_cast <;> ring_nf <;> simp
  <;> norm_num <;> ring_nf <;> simp_all <;> linarith`. The distributivity step uses `ring_nf
  <;> simp [Complex.ext_iff, mul_add, add_mul] <;> ...` instead of `mul_add`. No `field_simp`.

- **goedel_att32.md** (67 lines, 2357 chars, 8 `have`s, 2 `calc`): uses `calc` for h4 and h5.
  Uniquely among Goedel PASSes, the distributivity step h5 applies `mul_add` explicitly before
  fallback cascade (`rw [mul_add] <;> ring_nf <;> simp_all <;> linarith`). The `mul_add` call
  is the closest any Goedel PASS comes to naming the distributivity move, but it is still
  followed by an arithmetic shotgun. `Finset.sum_range_succ` appears directly in h3.

**Common Goedel pattern**: `simpa [add_assoc]` to apply the recurrence; `Finset.sum_range_succ`
named once in a `rw`; denominator cast never closed by `norm_cast` alone (always extended with
`ring_nf`, `simp_all`, `linarith`); distributivity never closed by `ring` alone. Char-len
2127–2680 (mean 2389).

### Kimina — (a) route-preserving (1/1)

- **kimina_att25.md** (28 lines, 1152 chars, 6 `have`s): the most compact PASS in the set.
  Applies the recurrence via `specialize hx_rec n (k+1); simpa`. Rewrites the denominator via
  an explicit `have h1 : (k+1:ℂ)+1 = (k:ℂ)+2 := by simp [Complex.ext_iff]; all_goals omega`,
  closed by `omega` — a single decision procedure, not a cascade. Splits the sum via a direct
  `rw [Finset.sum_range_succ]` (h3). Closes distributivity via `ring` (eq2). The three corrigé
  moves — recurrence instantiation, `Finset.sum_range_succ` split, ring distributivity — map
  one-to-one to named `have` statements eq1, h3, eq2. The intermediate eq3 links the two
  representations of the sum explicitly before the final double `rw [eq3]; rw [eq2]`.

## Cross-arm comparison

Both arms identify `Finset.sum_range_succ` as the key sum-splitting lemma; it appears by name in
all 5 PASSes. The divergence is in the closing tactics. Kimina closes the denominator cast with
`simp [Complex.ext_iff]; all_goals omega` (clean, single-shot) and distributivity with `ring`
(one tactic). Goedel closes both with cascades of 4–7 tactics (`ring_nf <;> simp_all <;>
norm_num <;> linarith`) that do not identify which algebraic move discharges the goal. Goedel
scripts are 1.8–2.3x longer (2127–2680 chars vs 1152 for Kimina). No Goedel PASS uses `omega`
for the cast; no Kimina PASS uses `field_simp`, `simp_all`, or `linarith`. The Goedel structural
scaffold (sequence of `have` lemmas with `exact` or `apply` at the close) parallels the corrigé
steps but the sub-closures are opaque.

## Bidirectionality verdict

Kimina att25 is fully bidirectional: the six `have` statements correspond one-to-one to the four
corrigé moves, and each sub-tactic (`simpa`, `omega`, `rw [Finset.sum_range_succ]`, `ring`) names
the operation being performed. The Goedel PASSes are structurally bidirectional at the `have`-skeleton
level — the corrigé route is recoverable — but the arithmetic sub-closures (cascades of `ring_nf
<;> simp_all <;> norm_num <;> linarith`) are opaque: a reader cannot identify which algebraic law
discharges each sub-goal without executing the cascade.
