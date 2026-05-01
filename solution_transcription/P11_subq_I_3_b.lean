import Mathlib

open BigOperators

theorem subq_I_3_b
    (q : ℝ) (hq : 0 < q)
    (u₁ u₂ : ℝ → ℝ)
    (p : ℝ)
    (hp : ∀ t : ℝ,
      (u₁ t) ^ 2 + (q / 2) * (u₁ t) ^ 4 + (u₂ t) ^ 2 = p) :
    0 ≤ p ∧ (p = 0 → ∀ t : ℝ, u₁ t = 0 ∧ u₂ t = 0) := by
  refine ⟨?_, ?_⟩
  · -- First conjunct: p ≥ 0.
    -- Move 1 (corrigé): "φ est à valeurs positives ou nulles (somme de carrés)".
    -- Instantiate hp at t = 0; the three terms are non-negative; sum = p.
    have h0 : (u₁ 0) ^ 2 + (q / 2) * (u₁ 0) ^ 4 + (u₂ 0) ^ 2 = p := hp 0
    have h_u1_sq_nn : 0 ≤ (u₁ 0) ^ 2 := sq_nonneg _
    have h_u2_sq_nn : 0 ≤ (u₂ 0) ^ 2 := sq_nonneg _
    have h_u1_4_nn : 0 ≤ (u₁ 0) ^ 4 := by
      have : (u₁ 0) ^ 4 = ((u₁ 0) ^ 2) ^ 2 := by ring
      rw [this]; exact sq_nonneg _
    have h_q_half_nn : 0 ≤ q / 2 := by linarith
    have h_q_term_nn : 0 ≤ (q / 2) * (u₁ 0) ^ 4 := mul_nonneg h_q_half_nn h_u1_4_nn
    -- Move 2 (corrigé): "p ≥ 0".
    linarith
  · -- Second conjunct: p = 0 → ∀ t, u₁ t = 0 ∧ u₂ t = 0.
    -- Move 3 (corrigé): "Si p = 0, ... tous les termes sont positifs ou nuls,
    -- donc u₁(t) = u₂(t) = 0".
    intro hp_zero t
    have ht : (u₁ t) ^ 2 + (q / 2) * (u₁ t) ^ 4 + (u₂ t) ^ 2 = p := hp t
    have h_u1_sq_nn : 0 ≤ (u₁ t) ^ 2 := sq_nonneg _
    have h_u2_sq_nn : 0 ≤ (u₂ t) ^ 2 := sq_nonneg _
    have h_u1_4_nn : 0 ≤ (u₁ t) ^ 4 := by
      have : (u₁ t) ^ 4 = ((u₁ t) ^ 2) ^ 2 := by ring
      rw [this]; exact sq_nonneg _
    have h_q_half_nn : 0 ≤ q / 2 := by linarith
    have h_q_term_nn : 0 ≤ (q / 2) * (u₁ t) ^ 4 := mul_nonneg h_q_half_nn h_u1_4_nn
    -- Sum of three non-negatives equals 0, so each is 0.
    have h_sum_zero : (u₁ t) ^ 2 + (q / 2) * (u₁ t) ^ 4 + (u₂ t) ^ 2 = 0 := by
      rw [ht]; exact hp_zero
    have h_u1_sq_zero : (u₁ t) ^ 2 = 0 := by linarith
    have h_u2_sq_zero : (u₂ t) ^ 2 = 0 := by linarith
    -- From (u₁ t)² = 0 deduce u₁ t = 0 via sq_eq_zero_iff (named, not nlinarith).
    refine ⟨?_, ?_⟩
    · exact sq_eq_zero_iff.mp h_u1_sq_zero
    · exact sq_eq_zero_iff.mp h_u2_sq_zero
