import LeanCorpus.Common

/-!
# Problem 4 — Concrete reformulation (Mercier–Rombaldi 2008)

This file restates the eight theorems of `LeanCorpus.P4` while inlining the
custom predicate `IsIrreducible` directly into the theorem hypotheses.  The
goal is to remove any reliance on user-defined predicates whose body the
prover would otherwise have to unfold by hand: every irreducibility
assumption now appears as a quantified statement about submodules stable
under the algebra.

Throughout, `E` denotes a finite-dimensional `ℂ`-vector space and `Mₙ(ℂ)`
is encoded as `Matrix (Fin n) (Fin n) ℂ`.  Endomorphism algebras are
`Module.End ℂ E`.
-/

namespace AITP.P4Concrete

open Matrix LinearMap Module

/-! ## Partie I -/

/--
**P4.I.1** — Equivalence between (i) "the family `(pᵢ)` are the projectors of a
direct-sum decomposition" and (ii) "the `pᵢ` are pairwise-orthogonal idempotents
summing to the identity".
-/
theorem subq_P4_I_1
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {n : ℕ} (p : Fin n → Module.End ℂ W) :
    (DirectSum.IsInternal (fun i => LinearMap.range (p i)) ∧
      ∀ i, LinearMap.IsProj (LinearMap.range (p i)) (p i)) ↔
    ((∀ i, (p i) * (p i) = p i) ∧
      (∀ i j, i ≠ j → (p i) * (p j) = 0) ∧
      (∑ i, p i) = 1) := by
  sorry

/--
**P4.I.2.e** — Given a unital algebra morphism `ρ : Mₙ(ℂ) → End(W)`, there
exists a basis of `W` indexed by `Fin n × Fin r` (for some `r`) such that, for
every `M ∈ Mₙ(ℂ)`, the matrix of `ρ M` in this basis is the block-diagonal
`diag(M, …, M)` with `r` blocks.
-/
theorem subq_P4_I_2_e
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {n : ℕ} [NeZero n] (ρ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Module.End ℂ W) :
    ∃ (r : ℕ) (b : Basis (Fin n × Fin r) ℂ W),
      ∀ (M : Matrix (Fin n) (Fin n) ℂ),
        LinearMap.toMatrix b b (ρ M) =
          (Matrix.reindex (Equiv.refl _) (Equiv.refl _))
            (Matrix.blockDiagonal (fun _ : Fin r => M)) := by
  sorry

/-! ## Partie II -/

/--
**P4.II.1** — If `u` and `v ∈ End(E)` commute, then every eigenspace of `u` is
stable under `v`.
-/
theorem subq_P4_II_1
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u v : Module.End ℂ E) (hcomm : Commute u v) (μ : ℂ) :
    Set.MapsTo v (u.eigenspace μ) (u.eigenspace μ) := by
  sorry

/--
**P4.II.3** — If `𝒜 ⊆ End(E)` is an irreducible subalgebra containing `1_E`,
then the set of transposes `ᵗ𝒜 ⊆ End(E*)` is also irreducible.

The irreducibility hypothesis on `A` is inlined: every submodule `F` stable
under all elements of `A` is either `⊥` or `⊤`.  The conclusion likewise
spells out irreducibility for the image set: every submodule `G` of `E*`
stable under every transpose is either `⊥` or `⊤`.
-/
theorem subq_P4_II_3
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : Subalgebra ℂ (Module.End ℂ E))
    (h_irr : ∀ (F : Submodule ℂ E),
      (∀ u ∈ A, ∀ x ∈ F, u x ∈ F) → F = ⊥ ∨ F = ⊤) :
    ∀ (G : Submodule ℂ (Module.Dual ℂ E)),
      (∀ u ∈ A, ∀ φ ∈ G,
        (Module.Dual.transpose (R := ℂ) (u : Module.End ℂ E) :
          Module.End ℂ (Module.Dual ℂ E)) φ ∈ G) →
      G = ⊥ ∨ G = ⊤ := by
  sorry

/--
**P4.II.4** — If `𝒜 ⊆ End(E)` is an irreducible subalgebra containing `1_E`
and `x` is a nonzero vector of `E`, then `𝒜 · x = E`.

The irreducibility hypothesis on `A` is inlined as before.
-/
theorem subq_P4_II_4
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : Subalgebra ℂ (Module.End ℂ E))
    (h_irr : ∀ (F : Submodule ℂ E),
      (∀ u ∈ A, ∀ y ∈ F, u y ∈ F) → F = ⊥ ∨ F = ⊤)
    {x : E} (hx : x ≠ 0) :
    Submodule.span ℂ
        ((fun u : Module.End ℂ E => u x) '' (A : Set (Module.End ℂ E))) = ⊤ := by
  sorry

/--
**P4.II.5** — Every rank-`1` endomorphism `u ∈ End(E)` factors as
`u(x) = l(x) • y` for some `y ∈ E` and `l : E →ₗ[ℂ] ℂ`.
-/
theorem subq_P4_II_5
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : Module.End ℂ E) (hrank : Module.finrank ℂ (LinearMap.range u) = 1) :
    ∃ (y : E) (l : Module.Dual ℂ E), ∀ x : E, u x = l x • y := by
  sorry

/-! ## Partie III -/

/--
**P4.III.1** — For `A ∈ Mₙ(ℂ)`, the map `dₐ : Mₙ(ℂ) → Mₙ(ℂ)` defined by
`dₐ(X) = A·X − X·A` is a derivation, i.e. it is `ℂ`-linear and satisfies the
Leibniz rule `dₐ(X·Y) = dₐ(X)·Y + X·dₐ(Y)`.
-/
theorem subq_P4_III_1
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ d : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      (∀ X, d X = A * X - X * A) ∧
      (∀ X Y, d (X * Y) = d X * Y + X * d Y) := by
  sorry

/-! ## Partie IV -/

/--
**P4.IV.1.a** — The map `ψ : Mₙ(ℂ) × Mₙ(ℂ) → ℂ` given by `ψ(X, Y) = Tr(X·Y)`
is a symmetric, non-degenerate bilinear form.
-/
theorem subq_P4_IV_1_a
    {n : ℕ} :
    ∃ ψ : LinearMap.BilinForm ℂ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X Y, ψ X Y = Matrix.trace (X * Y)) ∧
      LinearMap.IsSymm ψ ∧
      ψ.Nondegenerate := by
  sorry

end AITP.P4Concrete
