import Mathlib

open BigOperators

theorem subq_A_2_a (n : ℕ) (hn : 2 ≤ n) :
    let L : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if i = j then 1 else - 1 / ((n : ℝ) - 1)
    let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
    L = ((n : ℝ) / (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)
        - (1 / ((n : ℝ) - 1)) • J := by
  intro L J
  -- Move 0 (side condition from the corrigé's "le degré est n - 1"):
  -- since n ≥ 2, the denominator (n - 1) is nonzero in ℝ.
  have h_n1 : (n : ℝ) - 1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- Move 1: matrix equality reduces to per-cell equality.
  ext i j
  -- Move 2: unfold the entries of L, J, scalar multiplication, subtraction,
  -- and the identity matrix at (i, j). These are the corrigé's references
  -- to "L_{ij}", "J_{ij}", and "I_{ij}".
  simp only [L, J, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
             smul_eq_mul]
  -- Move 3: case-split on the diagonal vs off-diagonal cell, exactly as
  -- the corrigé's "(L_{ii}) = 1" / "(L_{ij}) = -1/(n-1)" dichotomy.
  by_cases h : i = j
  · -- Diagonal cell: 1 = n/(n-1) · 1 - 1/(n-1) · 1 = (n - 1)/(n - 1) = 1.
    -- The arithmetic identity is the corrigé's "n/(n-1) - 1/(n-1) = 1".
    simp [h]
    field_simp
  · -- Off-diagonal cell: -1/(n-1) = n/(n-1) · 0 - 1/(n-1) · 1.
    -- The arithmetic identity is the corrigé's "0 - 1/(n-1) = -1/(n-1)".
    simp [h]
    ring
