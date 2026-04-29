import LeanCorpus.Common

namespace AITP.P2Concrete

/-!
# Problem 2 (Mercier–Rombaldi 2006), concrete form
## Dallages de disques in the Euclidean plane

This file mirrors `LeanCorpus.P2` but presents each of the eight selected
sub-questions in *concrete* form: every theorem takes all needed data as
free variables (the area function `s`, the family `𝒜`, the dallage
hypotheses, the functions `N` and `d`, plus the relevant admitted
properties). No `Setup` structure is opaque; the énoncé content is
visible from the theorem signature alone.

The basic chapter geometry (`E`, `D`, `closedD`, `C`, `D₁`, `Q`, `Q0`)
is redefined locally so this file is self-contained.
-/

/-- The affine Euclidean plane `E := ℝ²` of the énoncé. -/
abbrev E : Type := ℝ × ℝ

/-- Open disk `D(M, a) = {P | d(M,P) < a}`. -/
def D (M : E) (a : ℝ) : Set E := Metric.ball M a

/-- Closed disk `closedD(M, a) = {P | d(M,P) ≤ a}`. -/
def closedD (M : E) (a : ℝ) : Set E := Metric.closedBall M a

/-- Circle `C(M, a) = {P | d(M,P) = a}`. -/
def C (M : E) (a : ℝ) : Set E := Metric.sphere M a

/-- Unit open disk `D(M) = D(M, 1)`. -/
def D₁ (M : E) : Set E := D M 1

/-- Closed square `Q(a) = {(x,y) | |x| ≤ a, |y| ≤ a}`. -/
def Q (a : ℝ) : Set E := {p : E | |p.1| ≤ a ∧ |p.2| ≤ a}

/-- Open square `Q⁰(a) = {(x,y) | |x| < a, |y| < a}`. -/
def Q0 (a : ℝ) : Set E := {p : E | |p.1| < a ∧ |p.2| < a}

/-! ## Selected sub-questions (concrete form) -/

/-- **I.1.** What is the area of a square of side `2a`? Answer: `4 a²`.

Concrete form: the area function `s` and its admitted properties are
free hypotheses; `Q 1 ↦ 4` and the affine-image rule for `s` are
sufficient to deduce `s (Q a) = 4 a²`. -/
theorem subq_I_1
    (s : Set E → ℝ)
    (𝒜 : Set (Set E))
    (s_affine_image : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E),
        s ((fun x => L x + b) '' X) = |L.det| * s X)
    (affine_image_mem : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E), ((fun x => L x + b) '' X) ∈ 𝒜)
    (Q_mem : ∀ a : ℝ, 0 ≤ a → Q a ∈ 𝒜)
    (s_Q_one : s (Q 1) = 4)
    (a : ℝ) (ha : 0 ≤ a) : s (Q a) = 4 * a^2 := by
  sorry

/-- **I.2.** For any point `M ∈ E`, the areas of `D(M, a)` and `closedD(M, a)`
both equal `π a²`.

Concrete form: hypotheses are the area function `s`, the family `𝒜`, the
admitted affine-image rule, the membership facts for disks and circles, the
zero-area-on-circles property, and the worked example `s (D₁ M) = π`. -/
theorem subq_I_2
    (s : Set E → ℝ)
    (𝒜 : Set (Set E))
    (s_affine_image : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E),
        s ((fun x => L x + b) '' X) = |L.det| * s X)
    (affine_image_mem : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E), ((fun x => L x + b) '' X) ∈ 𝒜)
    (D_mem : ∀ (M : E) (a : ℝ), 0 ≤ a → D M a ∈ 𝒜)
    (closedD_mem : ∀ (M : E) (a : ℝ), 0 ≤ a → closedD M a ∈ 𝒜)
    (s_subset_circle : ∀ {X : Set E} (M : E) (a : ℝ), X ⊆ C M a → s X = 0)
    (s_D₁ : ∀ M : E, s (D₁ M) = Real.pi)
    (M : E) (a : ℝ) (ha : 0 ≤ a) :
    s (D M a) = Real.pi * a^2 ∧ s (closedD M a) = Real.pi * a^2 := by
  sorry

/-- **I.5.** A unit open disk `D(M)` contained in `Q(a)` is in fact contained
in the open square `Q⁰(a)`.

Concrete form: this is purely geometric — no area data is required. -/
theorem subq_I_5 (M : E) (a : ℝ) (h : D₁ M ⊆ Q a) : D₁ M ⊆ Q0 a := by
  sorry

/-- **I.3.** For `X ∈ 𝒜` and a dallage `(D(M_i))_{i ∈ I}` of `X`, the
cardinality of `I` is bounded above by `s(X)/π`.

Concrete form: the dallage predicate is unrolled into the two defining
clauses (each `D₁ (M i)` is contained in `X`; the family is pairwise
disjoint), and the area axioms (disjoint additivity, monotonicity,
`s (D₁ M) = π`, plus disk membership in `𝒜`) are free hypotheses. -/
theorem subq_I_3
    (s : Set E → ℝ)
    (𝒜 : Set (Set E))
    (mono : ∀ {X Y : Set E}, X ∈ 𝒜 → Y ∈ 𝒜 → X ⊆ Y → s X ≤ s Y)
    (iUnion_mem : ∀ {ι : Type} [Fintype ι] (X : ι → Set E),
      (∀ i, X i ∈ 𝒜) → (⋃ i, X i) ∈ 𝒜)
    (s_iUnion_disjoint : ∀ {ι : Type} [Fintype ι] (X : ι → Set E),
      (∀ i, X i ∈ 𝒜) → Pairwise (fun i j => Disjoint (X i) (X j)) →
      s (⋃ i, X i) = ∑ i, s (X i))
    (D_mem : ∀ (M : E) (a : ℝ), 0 ≤ a → D M a ∈ 𝒜)
    (s_D₁ : ∀ M : E, s (D₁ M) = Real.pi)
    {X : Set E} (hX : X ∈ 𝒜)
    {ι : Type} [Fintype ι] (M : ι → E)
    (hd_subset : ∀ i, D₁ (M i) ⊆ X)
    (hd_disjoint : Pairwise (fun i j => Disjoint (D₁ (M i)) (D₁ (M j)))) :
    (Fintype.card ι : ℝ) ≤ s X / Real.pi := by
  sorry

/-- **II.1.** Upper bound for `d(a)` for `a > 0`. The expected bound is
`d(a) ≤ 4/π`, deduced from `N(a) ≤ s(Q a)/π = 4 a²/π`.

Concrete form: `N : ℝ → ℕ` and `d : ℝ → ℝ` are free, with their defining
relations expressed as hypotheses: `d a = N a / a²`, and `N a` is the
supremum of cardinalities of dallages of `Q a` (encoded as: every dallage
of `Q a` has cardinality `≤ N a`). The area data is also free. -/
theorem subq_II_1
    (s : Set E → ℝ)
    (𝒜 : Set (Set E))
    (mono : ∀ {X Y : Set E}, X ∈ 𝒜 → Y ∈ 𝒜 → X ⊆ Y → s X ≤ s Y)
    (iUnion_mem : ∀ {ι : Type} [Fintype ι] (X : ι → Set E),
      (∀ i, X i ∈ 𝒜) → (⋃ i, X i) ∈ 𝒜)
    (s_iUnion_disjoint : ∀ {ι : Type} [Fintype ι] (X : ι → Set E),
      (∀ i, X i ∈ 𝒜) → Pairwise (fun i j => Disjoint (X i) (X j)) →
      s (⋃ i, X i) = ∑ i, s (X i))
    (s_affine_image : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E),
        s ((fun x => L x + b) '' X) = |L.det| * s X)
    (affine_image_mem : ∀ {X : Set E}, X ∈ 𝒜 →
      ∀ (L : E →ₗ[ℝ] E) (b : E), ((fun x => L x + b) '' X) ∈ 𝒜)
    (D_mem : ∀ (M : E) (a : ℝ), 0 ≤ a → D M a ∈ 𝒜)
    (Q_mem : ∀ a : ℝ, 0 ≤ a → Q a ∈ 𝒜)
    (s_Q_one : s (Q 1) = 4)
    (s_D₁ : ∀ M : E, s (D₁ M) = Real.pi)
    (N : ℝ → ℕ)
    (d : ℝ → ℝ)
    (d_def : ∀ x : ℝ, d x = (N x : ℝ) / x^2)
    (N_dallage_le : ∀ (x : ℝ) {ι : Type} [Fintype ι] (M : ι → E),
      (∀ i, D₁ (M i) ⊆ Q x) →
      Pairwise (fun i j => Disjoint (D₁ (M i)) (D₁ (M j))) →
      Fintype.card ι ≤ N x)
    (N_witness : ∀ (x : ℝ), ∃ (ι : Type) (_ : Fintype ι) (M : ι → E),
      (∀ i, D₁ (M i) ⊆ Q x) ∧
      Pairwise (fun i j => Disjoint (D₁ (M i)) (D₁ (M j))) ∧
      Fintype.card ι = N x)
    (a : ℝ) (ha : 0 < a) : d a ≤ 4 / Real.pi := by
  sorry

/-- **I.6.** For every integer `n ≥ 1` and every real `a ≥ 0`,
`N(n a) ≥ n² N(a)`.

Concrete form: `N : ℝ → ℕ` is free, characterized by the same two
hypotheses as in `subq_II_1`: every dallage of `Q x` has cardinality
`≤ N x`, and there exists a dallage realising `N x`. -/
theorem subq_I_6
    (N : ℝ → ℕ)
    (N_dallage_le : ∀ (x : ℝ) {ι : Type} [Fintype ι] (M : ι → E),
      (∀ i, D₁ (M i) ⊆ Q x) →
      Pairwise (fun i j => Disjoint (D₁ (M i)) (D₁ (M j))) →
      Fintype.card ι ≤ N x)
    (N_witness : ∀ (x : ℝ), ∃ (ι : Type) (_ : Fintype ι) (M : ι → E),
      (∀ i, D₁ (M i) ⊆ Q x) ∧
      Pairwise (fun i j => Disjoint (D₁ (M i)) (D₁ (M j))) ∧
      Fintype.card ι = N x)
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    n^2 * N a ≤ N (n * a) := by
  sorry

/-- **III.1.** Let `Λ` be the additive subgroup of `ℂ` generated by `2`
and `2j`, where `j = exp(2iπ/3)`. The modulus of every nonzero element
of `Λ` is at least `2`.

Concrete form: this statement is already self-contained — no `Setup`
data is involved. -/
theorem subq_III_1 :
    ∀ z ∈ AddSubgroup.closure ({(2 : ℂ), 2 * Complex.exp (2 * Real.pi * Complex.I / 3)} : Set ℂ),
      z ≠ 0 → 2 ≤ ‖z‖ := by
  sorry

/-- **IV.3.a.** Let `μ(z₁, z₂, z₃)` denote the smallest of the three
distances `|z₁ - z₂|, |z₂ - z₃|, |z₃ - z₁|`. Given complex numbers
`z₁, z₂, z₃` with moduli `≤ 1` not all equal to `1`, there exist complex
numbers `t₁, t₂, t₃` with moduli `≤ 1` such that
`μ(t₁, t₂, t₃) > μ(z₁, z₂, z₃)`.

Concrete form: this statement is already self-contained. -/
theorem subq_IV_3_a (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ ≤ 1) (h₂ : ‖z₂‖ ≤ 1) (h₃ : ‖z₃‖ ≤ 1)
    (hne : ¬ (‖z₁‖ = 1 ∧ ‖z₂‖ = 1 ∧ ‖z₃‖ = 1)) :
    let μ : ℂ → ℂ → ℂ → ℝ := fun a b c => min (‖a - b‖) (min (‖b - c‖) (‖c - a‖))
    ∃ t₁ t₂ t₃ : ℂ, ‖t₁‖ ≤ 1 ∧ ‖t₂‖ ≤ 1 ∧ ‖t₃‖ ≤ 1 ∧
      μ z₁ z₂ z₃ < μ t₁ t₂ t₃ := by
  sorry

end AITP.P2Concrete
