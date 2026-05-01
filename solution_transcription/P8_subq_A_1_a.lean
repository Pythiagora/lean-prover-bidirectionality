import Mathlib

open BigOperators

theorem subq_A_1_a {n : ℕ} (M : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
  -- Move 1 (corrigé): "M ∈ GLₙ(ℤ) ⇒ det M est un entier inversible".
  --   `M.det : ℤˣ` is the determinant homomorphism `GL → ℤˣ`; its underlying
  --   `IsUnit` witness is `(M.det).isUnit`.
  have h_unit : IsUnit ((M : Matrix (Fin n) (Fin n) ℤ).det) := M.det.isUnit
  -- Move 2 (corrigé): "les inversibles de ℤ sont exactement ±1".
  --   Mathlib: `Int.isUnit_iff : IsUnit n ↔ n = 1 ∨ n = -1`.
  exact Int.isUnit_iff.mp h_unit
