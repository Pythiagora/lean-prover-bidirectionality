# P10.subq_II_B_1 — per-theorem deep dive

**Total PASSes**: 2 (2 Goedel + 0 Kimina)

**Arm asymmetry**: Goedel 2/64, Kimina 0/64. The zero Kimina PASS rate makes cross-arm comparison impossible; all analysis below is single-arm.

## Statement

Show that for a sequence `α : ℕ → ℂ` defined by `α 0 = 1/(1−λ)` and `α k = α(k−1) / (1 + (1 − 1/λ)·(1/k))` for `k ≥ 1`, every `α k` is non-zero, given that `λ ≠ 0`, `λ ≠ 1/(k+1)` for all `k : ℕ`, and `(1/λ).re ≠ 1`.

## Corrigé route summary

Induction on `k`. Base: `α 0 = 1/(1−λ) ≠ 0` because `λ ≠ 1` (from `hlam_notA 0`). Step: denominator `1 + (1 − 1/λ)·(1/k) = 0` would force `λ = 1/(k+1)`, contradicting `hlam_notA k`; so numerator and denominator are both non-zero, giving `α(k+1) ≠ 0` by `div_ne_zero`.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 2 | 2 (100%) | 0 (0%) | 0 (0%) |
| Kimina | 0 | — | — | — |
| **Both** | **2** | **2 (100%)** | **0 (0%)** | **0 (0%)** |

## Analysis of Goedel PASSes

Both attempts follow an identical three-block structure: `h_one_sub_lam_ne_zero` / `h1_sub_lam_ne_zero` (base condition), `h_denom_ne_zero` / `hDk_ne_zero` (denominator lemma), then `h_main` by `induction`. Both explicitly identify the resonance mechanism and close with `div_ne_zero`. This is **route (a)** by the corrigé's own criteria: the two named steps (base non-zero via `hlam_notA 0`, denominator non-zero via `hlam_notA k` after algebraic chain) are spelled out as named `have` blocks, and the induction structure is explicit.

### goedel_att02 (137 lines, 4495 chars)

Classification: **(a) route-preserving**.

The denominator lemma is proved via a `calc` chain:

> `(1 - 1 / lam : ℂ) = (1 - 1 / lam : ℂ) * (1 / (n : ℂ)) * (n : ℂ) := by field_simp [h₆] ... _ = (-1 : ℂ) * (n : ℂ) := by rw [h₇] _ = - (n : ℂ) := by ring`

followed by a second `calc` inverting to `lam = 1 / ((n : ℂ) + 1)`. The algebraic chain from `D_n = 0` to `λ = 1/(n+1)` is fully inscribed. The inductive step uses `Nat.sub_add_cancel` to simplify `k.succ - 1` and closes with `div_ne_zero h₆ h₇`. Closing tactics include `ring_nf <;> simp_all [Complex.ext_iff] <;> norm_num <;> linarith` as shotgun fallback inside the `calc` steps, but the proof skeleton itself is clean. The `hlam_re` hypothesis goes unused (noted in att33 reasoning and implied in att02).

### goedel_att33 (184 lines, 5595 chars)

Classification: **(a) route-preserving**.

Structurally identical to att02 but longer. Uses `by_contra` for both the base and denominator blocks instead of `intro h; ... ; exact h₂ h₁`. Denominator derivation uses a four-step `calc`:

> `(1 - 1 / lam : ℂ) = (1 - 1 / lam : ℂ) * 1 := by ring _ = (1 - 1 / lam : ℂ) * ((k : ℂ) * (1 / (k : ℂ))) := by field_simp [h₄] ... _ = (-1 : ℂ) * (k : ℂ) := by rw [h₂] _ = - (k : ℂ) := by ring`

Additional shotgun lines include `nlinarith [sq_nonneg (lam.re - 1), sq_nonneg (lam.im), ...]` as fallback in the denominator block, suggesting uncertainty in the complex arithmetic steps. The reasoning prefix explicitly notes: "The condition `Re(1/λ) ≠ 1` is not actually used in the proof." The final induction closes identically with `div_ne_zero h₈ h₇`.

## Cross-attempt comparison

Both PASSes exhibit the same proof shape. The difference is cosmetic: att02 uses `intro h; contradiction` style, att33 uses `by_contra h; simpa using h`. Att33 is 1.24× longer due to more verbose `norm_cast/linarith` fallback chains in the `calc` side conditions. Neither uses `hlam_re`; both reasoning traces flag this omission. The mean `n_have` is 35–36, `n_calc` is 3–4; these figures reflect the multi-step algebraic derivation required by the denominator lemma.

## Kimina arm — 0/64 PASSes

No Kimina PASS was produced. The likely failure mode is tactic failure in the complex field arithmetic required to derive `λ = 1/(k+1)` from `D_k = 0`: this involves a `field_simp`-based chain over `ℂ` that is sensitive to coercion issues (`(k : ℕ)` vs `(k : ℂ)`). Alternatively, Kimina may fail to produce the `h_denom_ne_zero` lemma cleanly without the verbose `calc` scaffolding Goedel uses. Whether Kimina would choose route (a) or (b) if it did PASS cannot be determined.

## Bidirectionality verdict

Both Goedel PASSes are route (a): the corrigé's two key moves — derive base non-zero from `hlam_notA 0`, derive denominator non-zero by algebraic contradiction using `hlam_notA k` — appear as explicit named `have` blocks and the induction structure is recoverable from the script without execution. The `div_ne_zero` close is transparent. The shotgun tails (`simp_all <;> norm_num <;> linarith`) in the `calc` side conditions are not corrigé-level but are confined to bookkeeping steps (non-zeroness of `(n : ℂ)`, commutativity of `1 + k`), not the main reasoning moves; the proof is therefore bidirectional at the corrigé grain.
