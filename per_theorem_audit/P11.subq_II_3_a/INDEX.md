# P11.subq_II_3_a — per-theorem deep dive

**Total PASSes**: 51 (51 Goedel + 0 Kimina)

## Statement

Given `lam t : ℝ` with `t < lam`, let `α s = 1 / (lam − s)` and `f s x = x² + sin(s·x)²`.
Prove: `HasDerivAt α (1 / (lam − t)²) t` and `1 / (lam − t)² ≤ f t (α t)`.

## Corrigé route

Two parts. (1) Derivative: `α = (λ−s)⁻¹`; chain rule on sub + inv gives `(λ−t)⁻²` at `t`.
(2) Bound: `f(t, α(t)) = α(t)² + sin(t·α(t))² ≥ α(t)² = 1/(λ−t)²`; drop non-negative `sin²`.

- **(a) Route-preserving**: named `HasDerivAt.inv` (or `HasDerivAt.div_const`) on `λ−s`, then explicit `sq_nonneg (Real.sin _)` for the bound.
- **(b) Lower-abstraction**: derivative via `HasDerivAt.div` wrapped in `convert`, followed by `field_simp <;> ring_nf` to normalize the value; bound by `pow_two_nonneg`/`positivity` + `linarith`.
- **(c) Opaque**: `fun_prop`/`differentiability` shotgun, or pure `nlinarith` chain hiding the sin² drop.

## PASS counts — arm asymmetry flag

| arm | pass | total | pass rate |
|---|---:|---:|---:|
| Goedel | 51 | 64 | 80% |
| Kimina | **0** | 64 | **0%** |

**Arm-asymmetric solving failure.** Kimina 0/64 is a hard zero — no partial passes. This matches the pattern at P7-Kimina and P11.III.5.a: Kimina fails entirely on theorems requiring explicit `HasDerivAt` construction combined with an analytic inequality, while Goedel succeeds at 80%. The asymmetry does not trace to route divergence; it traces to Kimina being unable to close the `convert <;> field_simp` derivative-value normalization sub-goal.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 51 | 0 (0%) | 51 (100%) | 0 (0%) |
| Kimina | 0 | — | — | — |
| **Both** | **51** | **0 (0%)** | **51 (100%)** | **0 (0%)** |

`HasDerivAt.inv` appears in 0 Lean scripts (mentioned in reasoning of att16, att23, att25, att40, att43, att53 then dropped). `fun_prop` and `differentiability` appear in 0 scripts. Route (a) and route (c) are absent.

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (51/51)

Every Goedel PASS shares an identical macro-structure: `intro α f`, two top-level `have h_deriv`
and `have h_ineq` blocks, closed by `exact ⟨h_deriv, h_ineq⟩` (or `constructor`). The derivative
block uniformly opens with `(hasDerivAt_const t lam).sub (hasDerivAt_id t)` (via `simpa`) to
establish `HasDerivAt (fun s => lam - s) (-1) t`, then calls `HasDerivAt.div` wrapped in
`convert ... using 1`, followed by `<;> field_simp [h, sub_ne_zero] <;> ring_nf` to close the
value-normalization sub-goal. Three sub-styles differ only in how the inequality part closes:

- **G-b1** (~32 files): `pow_two_nonneg _` for `sin² ≥ 0`, then `linarith`.
  Most compact; `ring_nf` in derivative, `dsimp` or `simp [α]` to unfold.
  See `goedel_att02.md`, `goedel_att03.md`, `goedel_att05.md`, `goedel_att16.md`, `goedel_att39.md`.

- **G-b2** (~15 files): `positivity` for `sin² ≥ 0`, then `linarith`.
  Derivative scaffold identical; `positivity` replaces `pow_two_nonneg` as the non-negativity witness.
  See `goedel_att23.md`, `goedel_att40.md`, `goedel_att53.md`.

- **G-b3** (~4 files): `nlinarith [Real.sin_le_one (t * (α t)), Real.neg_one_le_sin (t * (α t))]`
  — bounds sin explicitly from [-1,1] before combining. More verbose; derivative scaffold unchanged.
  See `goedel_att25.md`, `goedel_att43.md`.

Across all 51: `field_simp` 51/51, `linarith` 51/51, `nlinarith` 51/51 (fires in at least one
sub-goal per file), `Real.sin` 51/51, `HasDerivAt.div` 41/51 (remainder use `.div` via
`(hasDerivAt_const ...).div` dot-notation). `sq_nonneg` as a named tactic: 0/51.
Char-len range 1515–2929, mean 2079; line count 42–73, mean 54.

### Kimina — empty (0/64)

No Kimina PASS exists. Row is blank across all sub-style buckets.

## Cross-arm divergence

The asymmetry is total: 51/64 Goedel vs 0/64 Kimina. Since no Kimina proof closes, the
divergence cannot be attributed to route choice. The most plausible failure point is the
`HasDerivAt.div` + `convert ... using 1` + `field_simp [sub_ne_zero]` normalization step,
which requires reducing `1 * (lam - t)^2 - 1 * (-1) * ...` to `1 / (lam - t)^2` under
`field_simp` — a cascaded shotgun that Goedel's generation pattern handles but Kimina's
apparently cannot. No Goedel PASS uses `HasDerivAt.inv` in the actual Lean script despite
6 files mentioning it in the reasoning prefix, confirming that the corrigé's (a)-route is
inaccessible to both arms.

## Bidirectionality verdict

The two-part split (derivative + inequality) and the sin²-drop argument are structurally
recoverable from every script, placing these proofs at weak bidirectionality. Full
bidirectionality is absent: the core corrigé move — chain rule via `HasDerivAt.inv` on
`(λ−s)⁻¹` composed with `HasDerivAt.sub` — is nowhere inscribed; the derivative value is
established by `convert <;> field_simp <;> ring_nf`, an opaque normalization whose steps do
not correspond to named mathematical operations, and `sq_nonneg` is never cited by name.
