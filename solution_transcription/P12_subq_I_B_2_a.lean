import Mathlib

open BigOperators

theorem subq_I_B_2_a (x y : ℝ) :
    x ^ 2 + x * y + y ^ 2 ≥ (3 / 4 : ℝ) * x ^ 2 := by
  -- Move 1: the algebraic identity from the corrigé.
  --   x^2 + xy + y^2 = (y + x/2)^2 + (3/4) x^2
  have h_id : x ^ 2 + x * y + y ^ 2 = (y + x / 2) ^ 2 + (3 / 4 : ℝ) * x ^ 2 := by
    ring
  -- Move 2: non-negativity of the square (y + x/2)^2 ≥ 0.
  have h_sq : (y + x / 2) ^ 2 ≥ 0 := sq_nonneg _
  -- Move 3: combine (1) and (2): adding (3/4) x^2 to (y + x/2)^2 ≥ 0
  -- gives the desired inequality through the identity.
  linarith
