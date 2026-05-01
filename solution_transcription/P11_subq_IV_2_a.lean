import Mathlib

open BigOperators

/-!
Faithful transcription of P11 sub-question IV.2.a.

Corrigé moves (from Mercier-Rombaldi P11, page 026/027):
  1. v(τ) = u(τ + T); chain rule on s ↦ s + T (derivative 1).
  2. Apply hu at (τ + T) to get the derivative of u at (τ + T).
  3. Apply f_periodic to convert f(τ + T, _) to f(τ, _).

Each move is one named Lean operation; no `<;>`, no shotgun.
-/
theorem subq_IV_2_a
    (T : ℝ) (f : ℝ → ℝ → ℝ)
    (f_periodic : ∀ t x : ℝ, f (t + T) x = f t x)
    (u : ℝ → ℝ)
    (hu : ∀ t : ℝ, HasDerivAt u (f t (u t)) t) :
    ∀ τ : ℝ,
      HasDerivAt (fun s => u (s + T))
        (f τ (u (τ + T))) τ := by
  intro τ
  -- Move 1 (corrigé): chain rule on s ↦ s + T, derivative is 1.
  have h_chain : HasDerivAt (fun s : ℝ => s + T) 1 τ :=
    (hasDerivAt_id τ).add_const T
  -- Move 2 (corrigé): apply hu at τ + T, compose with the chain rule.
  have h_step := (hu (τ + T)).comp τ h_chain
  -- h_step : HasDerivAt (u ∘ fun s ↦ s + T) (f (τ + T) (u (τ + T)) * 1) τ
  rw [mul_one] at h_step
  -- Move 3 (corrigé): apply f_periodic to rewrite f (τ + T) _ ↦ f τ _.
  rw [f_periodic] at h_step
  exact h_step
