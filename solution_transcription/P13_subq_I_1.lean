import Mathlib

open BigOperators

theorem subq_I_1
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃! u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ f n u = 0 := by
  -- Move 1 (corrigé): f_n(0) = -1.
  --   Each x^(k+1) with k+1 ≥ 1 evaluates to 0 at x = 0.
  have h_f0 : f n 0 = -1 := by
    rw [f_def]
    have h_sum_zero : (∑ k ∈ Finset.range n, (0 : ℝ) ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact zero_pow (Nat.succ_ne_zero k)
    rw [h_sum_zero]; ring
  -- Move 2 (corrigé): f_n(1) = n - 1 ≥ 0 (using hn : 1 ≤ n).
  have h_f1 : f n 1 = (n : ℝ) - 1 := by
    rw [f_def]
    have h_sum_one : (∑ k ∈ Finset.range n, (1 : ℝ) ^ (k + 1)) = (n : ℝ) := by
      simp
    rw [h_sum_one]
  have h_f1_nn : 0 ≤ f n 1 := by
    rw [h_f1]
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h_f0_neg : f n 0 ≤ 0 := by rw [h_f0]; norm_num
  -- Move 3 (corrigé): f_n is continuous on [0, 1] (polynomial-continuity).
  have h_cont : ContinuousOn (f n) (Set.Icc (0 : ℝ) 1) := by
    have h_eq : (f n) = (fun x : ℝ => (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1) := by
      funext x; exact f_def n x
    rw [h_eq]
    refine ContinuousOn.sub ?_ continuousOn_const
    refine continuousOn_finset_sum _ ?_
    intro k _
    exact (continuousOn_id).pow (k + 1)
  -- Move 4 (corrigé): IVT — apply intermediate_value_Icc with a=0, b=1.
  --   Since f_n(0) ≤ 0 ≤ f_n(1), 0 ∈ Icc (f_n 0) (f_n 1) ⊆ f_n '' Icc 0 1.
  have h_ivt : ∃ u ∈ Set.Icc (0 : ℝ) 1, f n u = 0 := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have h_subset := intermediate_value_Icc h01 h_cont
    have h_zero_mem : (0 : ℝ) ∈ Set.Icc (f n 0) (f n 1) :=
      ⟨h_f0_neg, h_f1_nn⟩
    obtain ⟨u, hu_mem, hu_eq⟩ := h_subset h_zero_mem
    exact ⟨u, hu_mem, hu_eq⟩
  -- Move 5 (corrigé): strict monotonicity of f_n on [0, 1].
  --   For 0 ≤ x < y ≤ 1, x^(k+1) < y^(k+1) (term-wise) ⇒ ∑ x^(k+1) < ∑ y^(k+1).
  have h_strict_mono : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ 1 → f n x < f n y := by
    intro x y hx hxy hy
    rw [f_def, f_def]
    have h_sum_lt :
        (∑ k ∈ Finset.range n, x ^ (k + 1)) <
          (∑ k ∈ Finset.range n, y ^ (k + 1)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.nonempty_range_iff.mpr (by omega)
      · intro k _
        exact pow_lt_pow_left₀ hxy hx (Nat.succ_ne_zero k)
    linarith
  -- Move 6 (corrigé): existence + uniqueness ⇒ ∃!.
  obtain ⟨u, hu_mem, hu_eq⟩ := h_ivt
  refine ⟨u, ⟨hu_mem.1, hu_mem.2, hu_eq⟩, ?_⟩
  rintro y ⟨hy0, hy1, hy_eq⟩
  -- Uniqueness via strict monotonicity: f_n y = 0 = f_n u, with both in [0, 1].
  rcases lt_trichotomy y u with hlt | heq | hgt
  · exfalso
    have := h_strict_mono y u hy0 hlt hu_mem.2
    linarith
  · exact heq
  · exfalso
    have := h_strict_mono u y hu_mem.1 hgt hy1
    linarith
