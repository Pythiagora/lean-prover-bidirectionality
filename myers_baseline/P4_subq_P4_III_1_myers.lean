import Mathlib

open BigOperators

/-
Myers-style transcription of Mercier-Rombaldi P4, sub-question III.1.

Corrigé named moves:
  Move 1 (linearity of d_A): d_A(X + λY) = (AX − XA) + λ(AY − YA) = d_A(X) + λ d_A(Y).
  Move 2 (Leibniz expansion): d_A(XY) = AXY − XYA = (AX − XA)Y + X(AY − YA)
                                        = d_A(X) Y + X d_A(Y).

The Leibniz move rests on the cancellation identity
  A·(X·Y) − (X·Y)·A = (A·X − X·A)·Y + X·(A·Y − Y·A)
which holds in any (noncommutative) ring; it is inscribed verbatim as a
`have` and discharged by `noncomm_ring`.
-/

theorem subq_P4_III_1
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ d : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      (∀ X, d X = A * X - X * A) ∧
      (∀ X Y, d (X * Y) = d X * Y + X * d Y) := by
  -- Move 1: build d_A as a ℂ-linear map. Linearity in X of `A * X - X * A`
  -- decomposes into two named pieces, each a Mathlib LinearMap:
  --   X ↦ A * X       is `LinearMap.mulLeft  ℂ A`
  --   X ↦ X * A       is `LinearMap.mulRight ℂ A`
  -- Their difference is the inner derivation d_A.
  let d : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A
  refine ⟨d, ?_, ?_⟩
  · -- Defining equation: d X = A * X - X * A. By construction.
    intro X
    rfl
  · -- Move 2: Leibniz. The corrigé identity
    --   A·(X·Y) − (X·Y)·A = (A·X − X·A)·Y + X·(A·Y − Y·A)
    -- is a pure noncommutative-ring identity, inscribed as `h_leib`.
    intro X Y
    have h_leib :
        A * (X * Y) - (X * Y) * A
          = (A * X - X * A) * Y + X * (A * Y - Y * A) := by
      noncomm_ring
    -- The defining equation d Z = A * Z - Z * A reduces both sides of the
    -- goal to the two sides of `h_leib`.
    change A * (X * Y) - (X * Y) * A
        = (A * X - X * A) * Y + X * (A * Y - Y * A)
    exact h_leib
