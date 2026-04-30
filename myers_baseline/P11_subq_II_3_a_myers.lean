import Mathlib

open BigOperators

/-!
Myers-style transcription of Mercier–Rombaldi P11, sub-question II.3.a.

Corrigé moves:
1. λ - t ≠ 0 from t < λ.
2. Derivative of (s ↦ λ - s) at t is -1.
3. Apply `HasDerivAt.inv` to get derivative of (s ↦ 1/(λ - s)) at t,
   then post-process the constant `-(-1)/(λ-t)² = 1/(λ-t)²`.
4. f(t, α t) = α(t)² + sin(t·α(t))² ≥ α(t)² = 1/(λ-t)² since sin² ≥ 0.
-/

theorem subq_II_3_a
    (lam : ℝ) (t : ℝ) (ht : t < lam) :
    let α : ℝ → ℝ := fun s => 1 / (lam - s)
    let f : ℝ → ℝ → ℝ := fun s x => x ^ 2 + Real.sin (s * x) ^ 2
    HasDerivAt α (1 / (lam - t) ^ 2) t ∧
      (1 / (lam - t) ^ 2) ≤ f t (α t) := by
  intro α f
  refine ⟨?_, ?_⟩
  · -- Move 1 (corrigé): the side condition λ - t ≠ 0.
    have h_ne : lam - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht)
    -- Move 2 (corrigé): derivative of (s ↦ λ - s) at t is -1.
    have h_inner : HasDerivAt (fun s : ℝ => lam - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub lam
    -- Move 3 (corrigé): HasDerivAt.inv on h_inner gives the derivative
    -- of (s ↦ (λ - s)⁻¹) at t, equal to -(-1) / (λ - t)² = 1 / (λ - t)².
    have h_inv : HasDerivAt (fun s : ℝ => (lam - s)⁻¹)
        (-(-1) / (lam - t) ^ 2) t :=
      h_inner.inv h_ne
    -- α s = 1 / (λ - s) = (λ - s)⁻¹; rewrite the function using one_div.
    have h_fun : (fun s : ℝ => 1 / (lam - s)) = (fun s : ℝ => (lam - s)⁻¹) := by
      funext s; exact one_div _
    -- Clean up the derivative constant: -(-1)/(λ-t)² = 1/(λ-t)².
    have h_const : (-(-1) / (lam - t) ^ 2 : ℝ) = 1 / (lam - t) ^ 2 := by ring
    -- α unfolds to (fun s => 1 / (lam - s)); rewrite to (· ⁻¹) form.
    change HasDerivAt (fun s : ℝ => 1 / (lam - s)) (1 / (lam - t) ^ 2) t
    rw [h_fun, ← h_const]
    exact h_inv
  · -- Move 4 (corrigé): f(t, α t) = α(t)² + sin(t·α(t))² ≥ α(t)² = 1/(λ-t)².
    have h_ne : lam - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht)
    -- α(t)² = 1/(λ-t)² (named identity, from the definition of α).
    have h_alpha_sq : (α t) ^ 2 = 1 / (lam - t) ^ 2 := by
      change (1 / (lam - t)) ^ 2 = 1 / (lam - t) ^ 2
      field_simp
    -- sin² is non-negative (named lemma, no shotgun).
    have h_sin_sq_nn : 0 ≤ Real.sin (t * α t) ^ 2 := sq_nonneg _
    -- f(t, α t) = α(t)² + sin(t·α(t))² (from the definition of f).
    change 1 / (lam - t) ^ 2 ≤ (α t) ^ 2 + Real.sin (t * α t) ^ 2
    linarith
