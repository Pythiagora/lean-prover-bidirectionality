import Mathlib

open BigOperators

/-- **Sous-question II.B.1.** Sous les hypothèses `(L)` (`λ ≠ 0`, `λ ∉ 𝒜`,
`Re(1/λ) ≠ 1`), la suite `α` définie par `α 0 = 1/(1−λ)` et
`α k = α (k−1) / (1 + (1 − 1/λ)·(1/k))` pour `k ≥ 1` ne s'annule jamais.

Transcription Myers du corrigé Mercier–Rombaldi : trois mouvements nommés ↦
trois opérations Lean nommées.

* Mouvement 1 (base) : `α 0 = 1/(1−λ) ≠ 0`. Il faut `1 − λ ≠ 0`, c'est-à-dire
  `λ ≠ 1`. Or `λ = 1 = 1/((0 : ℂ) + 1)` est exclu par `hlam_notA 0`.
  ↦ Lean : `have h_one_sub_lam_ne_zero` via instanciation de `hlam_notA 0`.

* Mouvement 2 (dénominateur) : pour tout `n ≥ 1`,
  `1 + (1 − 1/λ)·(1/n) ≠ 0`. Si le dénominateur s'annule, alors
  `(1 − 1/λ)·(1/n) = −1`, donc `(λ − 1)/(λ·n) = −1`, donc `λ − 1 = −λn`,
  donc `λ·(1 + n) = 1`, donc `λ = 1/(n + 1)`, contredisant `hlam_notA n`.
  ↦ Lean : `have h_denom_ne_zero` via `by_contra` et `field_simp` puis
  application de `hlam_notA n`.

* Mouvement 3 (récurrence) : par récurrence sur `k`, base `α 0 ≠ 0` (Move 1),
  hérédité `α (k+1) = α k / D_{k+1}` avec `D_{k+1} ≠ 0` (Move 2) et `α k ≠ 0`
  (hypothèse de récurrence), donc `α (k+1) ≠ 0` par `div_ne_zero`.
  ↦ Lean : `induction k with | zero => ...; | succ k ih => ...` puis
  `div_ne_zero ih h_denom`. -/
theorem subq_II_B_1
    (lam : ℂ) (hlam_ne_zero : lam ≠ 0)
    (hlam_notA : ∀ k : ℕ, lam ≠ 1 / ((k : ℂ) + 1))
    (hlam_re : (1 / lam).re ≠ 1)
    (α : ℕ → ℂ)
    (hα0 : α 0 = 1 / (1 - lam))
    (hαk : ∀ k, 1 ≤ k →
      α k = α (k - 1) / (1 + (1 - 1 / lam) * (1 / (k : ℂ)))) :
    ∀ k, α k ≠ 0 := by
  -- Mouvement 1 (base) : `1 − λ ≠ 0` car `λ ≠ 1` via `hlam_notA 0`.
  have h_one_sub_lam_ne_zero : (1 : ℂ) - lam ≠ 0 := by
    intro h
    have hlam_eq_one : lam = 1 := by linear_combination -h
    have hlam_notA0 : lam ≠ 1 / (((0 : ℕ) : ℂ) + 1) := hlam_notA 0
    have hone_eq : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) = 1 := by norm_num
    rw [hone_eq] at hlam_notA0
    exact hlam_notA0 hlam_eq_one
  -- Mouvement 2 (dénominateur) : pour `n ≥ 1`, `D_n = 1 + (1 − 1/λ)·(1/n) ≠ 0`.
  -- Si `D_n = 0`, alors par chaîne algébrique `λ = 1/((n : ℂ) + 1)`, ce qui
  -- contredit `hlam_notA n`.
  have h_denom_ne_zero :
      ∀ (n : ℕ), 1 ≤ n →
        (1 : ℂ) + (1 - 1 / lam) * (1 / (n : ℂ)) ≠ 0 := by
    intro n hn
    have hn_cast_ne : (n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
    intro hD
    -- À partir de `D_n = 0`, dériver `λ = 1/((n : ℂ) + 1)`.
    -- D_n = 0 ⇒ multiplie par `λ·n`, obtient `λ·n + (λ − 1) = 0`,
    -- donc `λ·(n + 1) = 1`, donc `λ = 1/(n + 1)`.
    have hsum_ne : ((n : ℂ) + 1) ≠ 0 := by
      -- Si `n + 1 = 0` dans `ℂ`, alors `(n : ℝ) = -1`, impossible car `n : ℕ`.
      intro hsum
      have hreal : ((n : ℝ) + 1 : ℂ) = 0 := by exact_mod_cast hsum
      have : (n : ℝ) + 1 = 0 := by exact_mod_cast hreal
      have hpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    -- Multiplier `D_n = 0` par `λ·n` pour éliminer les divisions :
    --   λ·n + (λ − 1) = 0,  i.e.  λ·(n + 1) = 1.
    have h_mul_eq_one : lam * ((n : ℂ) + 1) = 1 := by
      have hD' : lam * (n : ℂ) * (1 + (1 - 1 / lam) * (1 / (n : ℂ))) =
          lam * (n : ℂ) * 0 := by rw [hD]
      have : lam * (n : ℂ) + (lam - 1) = 0 := by
        have hlamn_ne : lam * (n : ℂ) ≠ 0 := mul_ne_zero hlam_ne_zero hn_cast_ne
        field_simp at hD'
        linear_combination hD'
      linear_combination this
    -- Donc `λ = 1/(n + 1)`.
    have h_lam_eq : lam = 1 / ((n : ℂ) + 1) := by
      field_simp
      linear_combination h_mul_eq_one
    exact hlam_notA n h_lam_eq
  -- Mouvement 3 (récurrence) : `α k ≠ 0` pour tout `k`.
  intro k
  induction k with
  | zero =>
      -- Base : `α 0 = 1/(1 − λ) ≠ 0` via Move 1.
      rw [hα0]
      exact div_ne_zero one_ne_zero h_one_sub_lam_ne_zero
  | succ k ih =>
      -- Hérédité : `α (k+1) = α k / D_{k+1}`, dénominateur non nul (Move 2),
      -- `α k ≠ 0` (HR), donc `α (k+1) ≠ 0` par `div_ne_zero`.
      have hk1 : 1 ≤ k + 1 := by omega
      have h_rec : α (k + 1) =
          α ((k + 1) - 1) / (1 + (1 - 1 / lam) * (1 / ((k + 1 : ℕ) : ℂ))) :=
        hαk (k + 1) hk1
      have h_idx : (k + 1) - 1 = k := by omega
      rw [h_idx] at h_rec
      rw [h_rec]
      exact div_ne_zero ih (h_denom_ne_zero (k + 1) hk1)
