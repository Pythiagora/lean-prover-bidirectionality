import Mathlib

open BigOperators

theorem subq_III_A_3_c
    (x : ℕ → ℕ → ℂ)
    (hx_rec : ∀ n k, x (n + 1) k =
      (1 / ((k : ℂ) + 1)) * ∑ j ∈ Finset.range (k + 1), x n j)
    (k n : ℕ) :
    x (n + 1) (k + 1) =
      (1 / ((k : ℂ) + 2)) * x n (k + 1) +
        (1 / ((k : ℂ) + 2)) * ∑ j ∈ Finset.range (k + 1), x n j := by
  -- Move 1 (corrigé): instantiate the recurrence at (n, k+1).
  --   x (n+1) (k+1) = (1 / ((k+1:ℕ):ℂ + 1)) * ∑ j ∈ range ((k+1)+1), x n j
  have h_rec : x (n + 1) (k + 1) =
      (1 / (((k + 1 : ℕ) : ℂ) + 1)) * ∑ j ∈ Finset.range ((k + 1) + 1), x n j :=
    hx_rec n (k + 1)
  -- Move 2 (corrigé): split the sum at the top via Finset.sum_range_succ.
  --   ∑ j ∈ range (k+2), x n j = (∑ j ∈ range (k+1), x n j) + x n (k+1)
  have h_split :
      ∑ j ∈ Finset.range ((k + 1) + 1), x n j =
        (∑ j ∈ Finset.range (k + 1), x n j) + x n (k + 1) :=
    Finset.sum_range_succ (fun j => x n j) (k + 1)
  -- Move 3 (corrigé): the cast simplification ((k+1:ℕ):ℂ) + 1 = (k:ℂ) + 2.
  have h_cast : ((k + 1 : ℕ) : ℂ) + 1 = (k : ℂ) + 2 := by
    push_cast
    ring
  -- Move 4 (corrigé): rewrite and distribute.
  rw [h_rec, h_split, h_cast]
  ring
