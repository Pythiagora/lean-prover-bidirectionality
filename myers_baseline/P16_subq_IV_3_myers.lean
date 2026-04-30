import Mathlib

open BigOperators

theorem subq_IV_3
    (f : ℝ → ℝ)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hH : ∀ x y : ℝ, x ≠ y →
      m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M)
    (k : ℝ) (hk : k = (m + M) / 2)
    (F : ℝ → ℝ) (hF : ∀ x, F x = f x - k * x) :
    ∀ x y : ℝ, |F y - F x| ≤ ((M - m) / 2) * |y - x| := by
  intro x y
  -- Move 1 (corrigé): case-split on x = y vs x ≠ y.
  by_cases hxy : x = y
  · -- Trivial case: F y - F x = 0 and |y - x| = 0.
    subst hxy
    simp
  · -- Main case: x ≠ y.
    -- Move 2 (corrigé): slope bound from (H).
    --   m ≤ (f y - f x) / (y - x) ≤ M
    have h_slope := hH x y hxy
    have h_slope_lo : m ≤ (f y - f x) / (y - x) := h_slope.1
    have h_slope_hi : (f y - f x) / (y - x) ≤ M := h_slope.2
    have h_yx_ne : y - x ≠ 0 := sub_ne_zero.mpr (fun h => hxy h.symm)
    -- Move 3 (corrigé): midpoint algebra.
    --   slope - k ∈ [-(M-m)/2, (M-m)/2]
    have h_dev_lo : -((M - m) / 2) ≤ (f y - f x) / (y - x) - k := by
      rw [hk]; linarith
    have h_dev_hi : (f y - f x) / (y - x) - k ≤ (M - m) / 2 := by
      rw [hk]; linarith
    -- Move 4 (corrigé): pass to absolute value via abs_le.
    have h_abs_dev : |(f y - f x) / (y - x) - k| ≤ (M - m) / 2 :=
      abs_le.mpr ⟨h_dev_lo, h_dev_hi⟩
    -- Move 5 (corrigé): factor F y - F x = (slope - k) * (y - x).
    have h_factor : F y - F x = ((f y - f x) / (y - x) - k) * (y - x) := by
      rw [hF y, hF x]
      field_simp
      ring
    -- Move 6 (corrigé): take absolute values and multiply.
    have h_abs_factor : |F y - F x| =
        |(f y - f x) / (y - x) - k| * |y - x| := by
      rw [h_factor, abs_mul]
    rw [h_abs_factor]
    have h_yx_abs_nn : 0 ≤ |y - x| := abs_nonneg _
    exact mul_le_mul_of_nonneg_right h_abs_dev h_yx_abs_nn
