import Mathlib

open BigOperators

theorem subq_III_5_a
    (f : ℝ → ℝ → ℝ) (u : ℝ → ℝ) :
    (∀ t : ℝ, HasDerivAt u (f t (u t)) t) ↔
      (∀ τ : ℝ, HasDerivAt (fun s => u (-s))
        (-f (-τ) (u (-τ))) τ) := by
  constructor
  · -- Forward direction: u solves x' = f(t,x)  ⇒  v(τ) := u(-τ) solves v' = -f(-τ, v).
    -- Corrigé move: chain rule on  v = u ∘ (s ↦ -s),  with derivative of (s ↦ -s) equal to -1.
    intro h τ
    -- Move 1 (corrigé): the inner map s ↦ -s has derivative -1 at τ.
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) τ := (hasDerivAt_id τ).neg
    -- Move 2 (corrigé): u has derivative f(-τ, u(-τ)) at the point -τ (instantiate hypothesis).
    have h_u : HasDerivAt u (f (-τ) (u (-τ))) (-τ) := h (-τ)
    -- Move 3 (corrigé): chain rule, v(s) = u(-s) has derivative f(-τ, u(-τ)) * (-1) at τ.
    have h_comp : HasDerivAt (fun s => u (-s))
        (f (-τ) (u (-τ)) * (-1 : ℝ)) τ := h_u.comp τ h_neg
    -- Move 4 (corrigé): rewrite f(-τ, u(-τ)) * (-1) = -f(-τ, u(-τ)).
    have h_rw : f (-τ) (u (-τ)) * (-1 : ℝ) = -f (-τ) (u (-τ)) := by ring
    rw [h_rw] at h_comp
    exact h_comp
  · -- Backward direction: symmetric. Apply the same chain rule to v(s) = u(-s) at -t,
    -- yielding a derivative for w(s) := v(-s) = u(--s) = u(s) at t.
    intro h t
    -- Move 1 (corrigé, mirrored): inner map s ↦ -s has derivative -1 at t.
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
    -- Move 2 (corrigé, mirrored): v = (s ↦ u(-s)) has derivative -f(-(-t), u(-(-t))) at -t.
    have h_v : HasDerivAt (fun s => u (-s))
        (-f (-(-t)) (u (-(-t)))) (-t) := h (-t)
    -- Move 3 (corrigé, mirrored): chain rule, w(s) := (fun s => u(-s)) (-s) = u(s)
    -- has derivative (-f (-(-t)) (u (-(-t)))) * (-1) at t.
    have h_comp : HasDerivAt (fun s => (fun r => u (-r)) (-s))
        ((-f (-(-t)) (u (-(-t)))) * (-1 : ℝ)) t := h_v.comp t h_neg
    -- Move 4 (corrigé, mirrored): the composite (fun s => u (-(-s))) is pointwise u, and
    -- (-f (t, u t)) * (-1) = f(t, u t) (using -(-t) = t).
    have h_fun : (fun s : ℝ => (fun r => u (-r)) (-s)) = u := by
      funext s; simp
    have h_val : (-f (-(-t)) (u (-(-t)))) * (-1 : ℝ) = f t (u t) := by
      rw [neg_neg]; ring
    rw [h_fun, h_val] at h_comp
    exact h_comp
