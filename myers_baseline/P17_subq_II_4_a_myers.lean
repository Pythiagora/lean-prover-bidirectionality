import Mathlib

open BigOperators

theorem subq_II_4_a
    (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - |2 * x - 1|)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∃ a b : ℤ, f^[n] x = (a : ℝ) * x + (b : ℝ) := by
  -- Move 1: induction on n.
  induction n with
  | zero =>
    -- Base case: f^0(x) = x = 1·x + 0.
    refine ⟨1, 0, ?_⟩
    simp [Function.iterate_zero]
  | succ k ih =>
    -- Inductive step: from f^k(x) = a·x + b, build witnesses for f^(k+1).
    obtain ⟨a, b, hab⟩ := ih
    -- Move 2: unfold one iteration: f^(k+1)(x) = f(f^k(x)) = f(a·x + b).
    rw [Function.iterate_succ_apply', hab, hf]
    -- Move 3: case-split on the tent map at the point a·x + b, mirroring
    -- the corrigé's split "si a_n x + b_n ∈ [0, 1/2]" vs "∈ ]1/2, 1]".
    by_cases hle : (a : ℝ) * x + (b : ℝ) ≤ 1 / 2
    · -- Case ≤ 1/2: 2·(a·x + b) - 1 ≤ 0, so |·| = 1 - 2(a·x + b),
      -- hence f(a·x+b) = 1 - (1 - 2(a·x+b)) = 2a·x + 2b.
      -- Witnesses: (2a, 2b), as in the corrigé.
      have h_abs : |2 * ((a : ℝ) * x + (b : ℝ)) - 1| =
          1 - 2 * ((a : ℝ) * x + (b : ℝ)) := by
        rw [abs_of_nonpos (by linarith)]; ring
      refine ⟨2 * a, 2 * b, ?_⟩
      rw [h_abs]; push_cast; ring
    · -- Case > 1/2: 2·(a·x + b) - 1 > 0, so |·| = 2(a·x + b) - 1,
      -- hence f(a·x+b) = 1 - (2(a·x+b) - 1) = -2a·x + (2 - 2b).
      -- Witnesses: (-2a, 2 - 2b), as in the corrigé.
      have hgt : (1 : ℝ) / 2 < (a : ℝ) * x + (b : ℝ) := lt_of_not_ge hle
      have h_abs : |2 * ((a : ℝ) * x + (b : ℝ)) - 1| =
          2 * ((a : ℝ) * x + (b : ℝ)) - 1 := by
        rw [abs_of_nonneg (by linarith)]
      refine ⟨-2 * a, 2 - 2 * b, ?_⟩
      rw [h_abs]; push_cast; ring
