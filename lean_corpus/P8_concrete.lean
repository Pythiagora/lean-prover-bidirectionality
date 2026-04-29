import LeanCorpus.Common

/-!
# Problem 8 — Concrete reformulation (Mercier–Rombaldi 2012)

This file restates the eight theorems of `LeanCorpus.P8` in *concrete* form:
every `let` binding inside a theorem statement is inlined, and the abstract
data of A.10.a (the minimum norm `m(Λ)` and the sphere `S(Λ)` of vectors
realizing it) is spelled out as explicit hypotheses on free variables. The
goal is to remove any reliance on local abbreviations or unstated
predicates, so a prover seeing only the theorem signature has the full
mathematical content available without unfolding.

Throughout, `E` is a real Euclidean space of dimension `n ≥ 1`, presented
in Mathlib via `EuclideanSpace ℝ (Fin n)` or any `[NormedAddCommGroup E]
[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`. A lattice `Λ ⊆ E` is
encoded as a `ℤ`-submodule equal to `Submodule.span ℤ (Set.range b)` for
some `Module.Basis (Fin n) ℝ E`.
-/

namespace AITP.P8Concrete

open scoped BigOperators
open Module

/-! ## A.1.a — `det M = ±1` for `M ∈ GLₙ(ℤ)` -/

/--
**A.1.a (Mercier–Rombaldi, P8).**

Let `M ∈ GLₙ(ℤ)`, that is, an `n × n` matrix with integer coefficients,
invertible over `ℝ`, with integer inverse. Then `det M = ±1`.

Mathlib encoding: an element of `GL (Fin n) ℤ = (Matrix (Fin n) (Fin n) ℤ)ˣ`
already carries an integer two-sided inverse, so its determinant is a unit
in `ℤ`, hence `±1`. Already self-contained — no inlining needed.
-/
theorem subq_A_1_a {n : ℕ} (M : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
  sorry

/-! ## A.2 — `Λ` is an additive subgroup of `(E, +)` -/

/--
**A.2 (Mercier–Rombaldi, P8).**

Let `E` be a real inner-product space and `b = (e₁, …, eₙ)` a basis of `E`.
The set `Λ` of integer linear combinations of `(e₁, …, eₙ)` is an additive
subgroup of `(E, +)`.

Concrete form: the lattice `Submodule.span ℤ (Set.range b)` is inlined; the
three closure properties (zero, addition, negation) are stated directly
without any local abbreviation.
-/
theorem subq_A_2
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Basis (Fin n) ℝ E) :
    (0 : E) ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E) ∧
    (∀ x ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E),
      ∀ y ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E),
        x + y ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E)) ∧
    (∀ x ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E),
      -x ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E)) := by
  sorry

/-! ## A.4.d — `Λ = {x₁e₁ + x₂e₂ : x₂ ≡ x₁ mod 3}` is a lattice of `ℝ²` -/

/--
**A.4.d (Mercier–Rombaldi, P8).**

In `ℝ²` with canonical basis `(e₁, e₂)`, the set
`Λ = { x₁·e₁ + x₂·e₂ : (x₁, x₂) ∈ ℤ², x₂ ≡ x₁ (mod 3) }`
is a lattice of `ℝ²`. Equivalently, there exists a `ℤ`-basis of `Λ` (one
may take `(e₁ + e₂, 3·e₂)`).

Concrete form: the set `Λ` is inlined directly as the existential
conclusion; no `let` binding is used.
-/
theorem subq_A_4_d :
    ∃ b : Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      ((Submodule.span ℤ (Set.range b) : Submodule ℤ _) : Set _) =
        {v : EuclideanSpace ℝ (Fin 2) |
          ∃ x₁ x₂ : ℤ,
            v = (x₁ : ℝ) • EuclideanSpace.single 0 (1 : ℝ) +
                (x₂ : ℝ) • EuclideanSpace.single 1 (1 : ℝ) ∧
            (x₂ - x₁) % 3 = 0} := by
  sorry

/-! ## A.6.a — Norm bound: `A · max|xᵢ| ≤ ‖x‖` -/

/--
**A.6.a (Mercier–Rombaldi, P8).**

Let `(e₁, …, eₙ)` be a basis of a finite-dimensional real inner-product
space `E`. There exists `A > 0` such that, for every `x ∈ E`,
`A · max₁≤ᵢ≤ₙ |xᵢ| ≤ ‖x‖`,
where `xᵢ = (b.repr x) i`.

This is a special case of the equivalence of norms in finite dimension:
the coordinate function `Basis.equivFun b` is continuous, hence bounded on
the unit sphere, which yields a constant `A` for the reverse direction.

We assume `n ≥ 1` so that the maximum is well defined. Already
self-contained: no `let` bindings, no custom predicates.
-/
theorem subq_A_6_a
    {n : ℕ} (hn : 0 < n) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Basis (Fin n) ℝ E) :
    ∃ A : ℝ, 0 < A ∧
      ∀ x : E,
        A * (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
              (fun i : Fin n => |b.repr x i|)) ≤ ‖x‖ := by
  sorry

/-! ## A.7 — A `ℤ`-spanning system of size `k` in `Λ` has `k = n` and is an `ℝ`-basis -/

/--
**A.7 (Mercier–Rombaldi, P8).**

Let `Λ` be a lattice of `E` with `ℤ`-basis `(e₁, …, eₙ)`. Suppose
`(u₁, …, u_k)` are `k` vectors of `Λ` such that every `x ∈ Λ` admits a
unique decomposition `x = ∑ᵢ xᵢ·uᵢ` with `(x₁, …, x_k) ∈ ℤᵏ`. Then `k = n`
and `(u₁, …, u_k)` is an `ℝ`-basis of `E`.

Concrete form: the lattice `Submodule.span ℤ (Set.range b)` is inlined
directly into the membership and uniqueness hypotheses.
-/
theorem subq_A_7
    {n k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Basis (Fin n) ℝ E) (u : Fin k → E)
    (_hu_mem : ∀ i, u i ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E))
    (_hu_unique : ∀ x ∈ (Submodule.span ℤ (Set.range b) : Submodule ℤ E),
      ∃! c : Fin k → ℤ, x = ∑ i, (c i : ℝ) • u i) :
    k = n ∧ ∃ B : Basis (Fin k) ℝ E, ∀ i, B i = u i := by
  sorry

/-! ## A.8.i — `ℝ·e₁ ∩ Λ = ℤ·e₁` -/

/--
**A.8.i (Mercier–Rombaldi, P8).**

Let `Λ` be the lattice with `ℤ`-basis `(e₁, …, eₙ)` and let `D₁ = ℝ·e₁`.
Then `D₁ ∩ Λ = ℤ·e₁`, i.e., the elements of `Λ` lying on the line `ℝ·e₁`
are exactly the integer multiples of `e₁`.

Concrete form: the local abbreviations `i₀`, `D₁`, `Λ` are all inlined
directly into the conclusion.
-/
theorem subq_A_8_i
    {n : ℕ} (hn : 0 < n) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Basis (Fin n) ℝ E) :
    ((Submodule.span ℝ ({b ⟨0, hn⟩} : Set E) : Submodule ℝ E) : Set E) ∩
        ((Submodule.span ℤ (Set.range b) : Submodule ℤ E) : Set E) =
      ((Submodule.span ℤ ({b ⟨0, hn⟩} : Set E) : Submodule ℤ E) : Set E) := by
  sorry

/-! ## A.9.e — Every nonzero subgroup of `Λ` is a lattice of some subspace -/

/--
**A.9.e (Mercier–Rombaldi, P8).**

Let `Λ` be a lattice of `E` and let `G` be a nonzero additive subgroup of
`Λ`. Then there exists a vector subspace `F ⊆ E` such that `G` is a
lattice of `F`, i.e., `G` is the integer span of an `ℝ`-basis of `F`.

Proof sketch (Mercier–Rombaldi): induction on `n`, distinguishing
`G ⊆ F₁` versus `G ⊄ F₁` where `F₁ = ker φ₁` and `φ₁` is the first
coordinate form. Already self-contained: no `let` bindings.
-/
theorem subq_A_9_e
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : Basis (Fin n) ℝ E)
    (G : AddSubgroup E)
    (_hG_le : (G : Set E) ⊆ (Submodule.span ℤ (Set.range b) : Submodule ℤ E))
    (_hG_ne : G ≠ ⊥) :
    ∃ (F : Submodule ℝ E) (k : ℕ) (c : Basis (Fin k) ℝ F),
      ∀ x : E, x ∈ G ↔
        ∃ z : Fin k → ℤ,
          x = ∑ i, (z i : ℝ) • ((c i : F) : E) := by
  sorry

/-! ## A.10.a — If `b ∈ S(Λ)` and `k ≥ 2`, then `b/k ∉ Λ` -/

/--
**A.10.a (Mercier–Rombaldi, P8).**

Let `Λ` be a lattice of `E` and `b ∈ S(Λ) = { x ∈ Λ : ‖x‖ = m(Λ) }` a
vector realizing the minimum nonzero norm
`m(Λ) := inf { ‖x‖ : x ∈ Λ, x ≠ 0 }`. For every integer `k ≥ 2`, the
vector `b / k` is not in `Λ`.

Concrete form: the abstract data `m(Λ)` and `S(Λ)` are spelled out as
explicit hypotheses on a free real variable `mΛ`:
* `mΛ_pos : 0 < mΛ` (the minimum is positive),
* `mΛ_min : ∀ x ∈ Λ, x ≠ 0 → mΛ ≤ ‖x‖` (defining property of `m(Λ)`),
* `b_mem : b ∈ Λ` and `b_norm : ‖b‖ = mΛ` (so `b ∈ S(Λ)`).

The conclusion is that `(1/k)·b ∉ Λ`. Reason: `‖b/k‖ = ‖b‖/k < m(Λ)`,
and `b/k ≠ 0`, contradicting minimality.
-/
theorem subq_A_10_a
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (basis : Basis (Fin n) ℝ E)
    (Λ : Submodule ℤ E)
    (_hΛ : Λ = Submodule.span ℤ (Set.range basis))
    (mΛ : ℝ) (_hmΛ_pos : 0 < mΛ)
    (_hmΛ_min : ∀ x ∈ Λ, x ≠ 0 → mΛ ≤ ‖x‖)
    (b : E) (_hb_mem : b ∈ Λ) (_hb_norm : ‖b‖ = mΛ)
    (k : ℤ) (_hk : 2 ≤ k) :
    ((1 : ℝ) / (k : ℝ)) • b ∉ (Λ : Set E) := by
  sorry

end AITP.P8Concrete
