import LeanCorpus.Common

namespace AITP.P5Concrete

/-!
# Problem 5 (Mercier–Rombaldi 2009): Perron–Frobenius theory — concrete form

Same eight selected sub-questions as `LeanCorpus.P5`, but with all custom predicates
(`Pn`, `Pgt`, `Sn`) inlined as explicit hypotheses on the matrix entries, so that a
prover seeing only the theorem statement (without the definitions) has access to the
full mathematical content.

Mapping:
* `Pn A`  ↦  `(hP : ∀ i j, 0 ≤ A i j)`
* `Pgt A` ↦  `(hP : ∀ i j, 0 < A i j)`
* `Sn A`  ↦  `(hP : ∀ i j, 0 ≤ A i j)` and `(hS : ∀ i, ∑ j, A i j = 1)`
-/

open scoped Matrix

section IPart

/-! ## Partie I — eigenvalues and eigenspaces of `P_{x,y}` -/

/-- The 2×2 matrix `P_{x,y} = ½ * [[1-x, 1+x], [1+y, 1-y]]` over `ℂ`. -/
noncomputable def Pxy (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • !![(1 - x : ℂ), (1 + x : ℂ); (1 + y : ℂ), (1 - y : ℂ)]

/--
**P5.I.1 (eigenvalues of `P_{x,y}`).**

Determine the eigenvalues of `P_{x,y}` and, for each eigenvalue, its associated eigenspace.

The eigenvalues of `P_{x,y}` are exactly `1` and `-(x+y)/2`. We state this as the equality
of `spectrum ℂ (Pxy x y)` with `{1, -(x+y)/2}`. The “eigenspace per eigenvalue” aspect is
encoded by exhibiting the canonical eigenvector `(1, 1)ᵀ` for the eigenvalue `1`.
-/
theorem subq_P5_I_1_eigenvalues (x y : ℝ) :
    spectrum ℂ (Pxy x y) = {1, -((x : ℂ) + y) / 2} ∧
      Module.End.HasEigenvalue (Matrix.toLin' (Pxy x y)) 1 := by
  sorry

/--
**P5.I.3 (discriminant of the characteristic polynomial of `A ∈ 𝒫_2^{>0}`).**

For `A = ![[a, b], [c, d]]`, express the discriminant of the characteristic polynomial
of `A` as `(a - d)^2 + 4 * b * c`.

The hypothesis `A ∈ 𝒫_2^{>0}` (strict positivity of entries) is irrelevant to the algebraic
identity but kept for faithfulness. Inlined as the four positivity assumptions on `a, b, c, d`.
-/
theorem subq_P5_I_3 (a b c d : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ).discr = (a - d) ^ 2 + 4 * b * c := by
  sorry

end IPart

section IIPartA

/-! ## Partie II.A — generalized eigenspaces and convergence of `A^k` -/

variable {n : ℕ}

/--
**P5.II.A.1.a (closed form of `C^k = (β·1 + B)^k` for `k ≥ l` with `B^l = 0`).**

Let `β ∈ ℂ` with `|β| < 1`, `B ∈ Mₙ(ℂ)` nilpotent with `B^l = 0`, and `C = β • 1 + B`.
For every integer `k ≥ l`, `C^k = ∑_{j=0}^{l-1} (k.choose j) β^{k-j} B^j`.
-/
theorem subq_P5_II_A_1_a
    (β : ℂ) (_hβ : ‖β‖ < 1)
    (B : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : 1 ≤ l) (hBl : B ^ l = 0)
    (k : ℕ) (hk : l ≤ k) :
    let C : Matrix (Fin n) (Fin n) ℂ := β • 1 + B
    C ^ k = ∑ j ∈ Finset.range l, (k.choose j : ℂ) • β ^ (k - j) • B ^ j := by
  sorry

/--
**P5.II.A.2.a.i (`F_α` is a vector subspace of `ℂⁿ`).**

Let `α` be an eigenvalue of `A` and `F_α = ⋃_{k ∈ ℕ} ker (A - α • 1)^k`. Show that
`F_α` is a vector subspace of `ℂⁿ`.
-/
theorem subq_P5_II_A_2_a_i_subspace
    (A : Matrix (Fin n) (Fin n) ℂ) (α : ℂ)
    (_hα : Module.End.HasEigenvalue (Matrix.toLin' A) α) :
    ((Module.End.genEigenspace (Matrix.toLin' A) α ⊤ : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ))
      = ⋃ k : ℕ, (LinearMap.ker ((Matrix.toLin' A - α • 1) ^ k) : Set (Fin n → ℂ)) := by
  sorry

/--
**P5.II.A.2.c (converse: if `Aᵏ → 0`, every eigenvalue has modulus `< 1`).**

If the sequence `(A^k)_{k ∈ ℕ}` tends to `0`, show that every eigenvalue of `A` has
modulus strictly less than `1`.
-/
theorem subq_P5_II_A_2_c
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Filter.Tendsto (fun k => A ^ k) Filter.atTop (nhds 0)) :
    ∀ α ∈ spectrum ℂ A, ‖α‖ < 1 := by
  sorry

end IIPartA

section IIPartB

/-! ## Partie II.B — non-compactness of `(A^k y)` with non-trivial Jordan block -/

variable {n : ℕ}

/--
**P5.II.B.2 (`(A^k y)` is contained in no compact subset).**

Assume `A` has eigenvalue `1` and there exist nonzero vectors `x, y` with `A x = x` and
`A y = y + x`. Show that the sequence `(A^k y)_{k ∈ ℕ}` is not contained in any compact
subset of `ℂⁿ`.
-/
theorem subq_P5_II_B_2
    (A : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) (hx : x ≠ 0) (_hy : y ≠ 0)
    (hAx : A *ᵥ x = x) (hAy : A *ᵥ y = y + x) :
    ¬ ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ k : ℕ, (A ^ k) *ᵥ y ∈ K := by
  sorry

end IIPartB

section IIIPart

/-! ## Partie III — characterization of `𝒮_n` -/

variable {n : ℕ}

/--
**P5.III.1 (characterization of `𝒮_n` via the all-ones vector).**

Let `A ∈ 𝒫_n` (i.e. all entries non-negative). Then `A ∈ 𝒮_n` (i.e. `A` is row-stochastic:
all entries non-negative and every row sums to `1`) iff `A *ᵥ w = w`, where `w` is the
all-ones vector.

Inlined: `Pn A` becomes the hypothesis `∀ i j, 0 ≤ A i j`; `Sn A` (on the right of the iff)
becomes the conjunction of `∀ i j, 0 ≤ A i j` and `∀ i, ∑ j, A i j = 1`.
-/
theorem subq_P5_III_1 (A : Matrix (Fin n) (Fin n) ℝ)
    (_hP : ∀ i j, 0 ≤ A i j) :
    ((∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = 1))
      ↔ A *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := by
  sorry

end IIIPart

section IVPartA

/-! ## Partie IV.A — `|v|` is an eigenvector for `ρ(A)` when `A ∈ 𝒫_n^{>0}` -/

variable {n : ℕ}

/--
**P5.IV.A.8.a (`x = (|v_i|)` is an eigenvector of `A` for `ρ(A)`).**

Let `A ∈ 𝒫_n^{>0}` (i.e. all entries strictly positive). Let `α` be an eigenvalue of `A`
with `|α| = ρ(A)`, `v` an associated (complex) eigenvector, and `x = (|v_1|, …, |v_n|)`.
Show that `x` is an eigenvector of `A` for the real eigenvalue `ρ(A)`.

Here we view `A : Matrix (Fin n) (Fin n) ℝ` as a complex matrix `A.map ((↑) : ℝ → ℂ)`
to define the spectrum, and we assert the equality `A *ᵥ x = (ρ A) • x` in `ℝⁿ`, where
`ρ A : ℝ` is the (real) spectral radius.

Inlined: `Pgt A` becomes `∀ i j, 0 < A i j`.
-/
theorem subq_P5_IV_A_8_a
    (A : Matrix (Fin n) (Fin n) ℝ) (_hA : ∀ i j, 0 < A i j)
    (α : ℂ) (hα : α ∈ spectrum ℂ (A.map ((↑) : ℝ → ℂ)))
    (v : Fin n → ℂ) (_hv : v ≠ 0)
    (_hAv : (A.map ((↑) : ℝ → ℂ)) *ᵥ v = α • v)
    (ρA : ℝ) (_hρ : ‖α‖ = ρA) :
    let x : Fin n → ℝ := fun i => ‖v i‖
    A *ᵥ x = ρA • x := by
  sorry

end IVPartA

end AITP.P5Concrete
