/-
  P1_concrete — concrete (unrolled) reformulation of P1.lean.

  Each of the 7 theorems of `LeanCorpus.P1` is restated here taking all required
  data as *free* variables (functions, scalars, complex points), with the
  defining equations / regularity / periodicity / inverse properties given as
  explicit hypotheses.  No reference to a `Setup` (or `EllipseSetup`) structure
  is made.  This matches the calibration-style format that achieved 78% pass
  rate on Goedel; theorems can be extracted verbatim and remain
  self-contained.

  Cross-references with the original `P1.lean`:
    * subq_I_1_a       — I.1.a, g is a C^k-diffeomorphism ℝ → ℝ
    * subq_I_1_b       — I.1.b, g(t + 2π) = g(t) + g(2π)
    * subq_I_2_compare — I.2 closing remark, comparing m and p
    * subq_II_3_a      — II.3.a, existence of α ∈ W with ≥ 2 distinct M(α_i)
    * subq_III_2_a     — III.2.a, E(D, n, P) independence of P and n
    * subq_III_3_b     — III.3.b, E(D(s)) = b²
    * subq_III_4_a     — III.4.a, relation between b, sin φ, ‖OM‖, ‖O'M‖

  Theorems are stated; proofs are `sorry`. The point is type-checking.
-/
import LeanCorpus.Common

namespace AITP.P1Concrete

noncomputable section

/-! ### I.1.a — `g` is a `C^k`-diffeomorphism of ℝ. -/

/--
**Book I.1.a (medium).**
"Démontrer que $g$ est un $\mathcal{C}^k$-difféomorphisme de $\mathbb{R}$ sur $\mathbb{R}$."

English: Prove that `g` is a `C^k`-diffeomorphism from ℝ onto ℝ.

We express the diffeomorphism property as: there exists an inverse `h : ℝ → ℝ`
such that both `g` and `h` are `C^k`, and `h ∘ g = id` and `g ∘ h = id`.
-/
theorem subq_I_1_a
    (k : WithTop ℕ∞) (one_le_k : 1 ≤ k)
    (ρ : ℝ → ℝ) (ρ_pos : ∀ t, 0 < ρ t)
    (ρ_contDiff : ContDiff ℝ k ρ)
    (ρ_periodic : Function.Periodic ρ (2 * Real.pi))
    (ξ : ℝ → ℝ)
    (xi_eq_sqrt : ∀ t, ξ t = Real.sqrt (ρ t ^ 2 + (deriv ρ t) ^ 2))
    (g : ℝ → ℝ)
    (g_def : ∀ t, g t = ∫ u in (0 : ℝ)..t, ξ u) :
    ContDiff ℝ k g ∧
      ∃ h : ℝ → ℝ,
        ContDiff ℝ k h ∧
          Function.LeftInverse h g ∧
          Function.RightInverse h g := by
  sorry

/-! ### I.1.b — quasi-periodicity of `g`. -/

/--
**Book I.1.b (easy).**
"Prouver que $g(t + 2\pi) = g(t) + g(2\pi)$ pour tout nombre réel $t$."

English: For every real `t`, `g(t + 2π) = g(t) + g(2π)`.
-/
theorem subq_I_1_b
    (ρ : ℝ → ℝ) (ρ_periodic : Function.Periodic ρ (2 * Real.pi))
    (ξ : ℝ → ℝ)
    (xi_eq_sqrt : ∀ t, ξ t = Real.sqrt (ρ t ^ 2 + (deriv ρ t) ^ 2))
    (g : ℝ → ℝ)
    (g_def : ∀ t, g t = ∫ u in (0 : ℝ)..t, ξ u) :
    ∀ t : ℝ, g (t + 2 * Real.pi) = g t + g (2 * Real.pi) := by
  sorry

/-! ### I.2 — comparing `m` and `p`. -/

/--
**Book I.2 closing remark (easy).**
"Comparer $m$ et $p$."

English: Compare the rotation number `m` with the number of vertices `p`.

Statement: for any closed polygonal line `N_1, …, N_p, N_{p+1} = N_1` with all
`N_i = M(s_i)` and `s_i ≤ s_{i+1} ≤ s_i + L`, the rotation number
`m = (s_{p+1} − s_1) / L` satisfies `m ≤ p`.

Here we encode "polygonal line on `B` with the abscissa convention of I.2.a" as
a sequence `s : Fin (p+1) → ℝ` satisfying `s i ≤ s (i+1) ≤ s i + L`, with
`M (s 0) = M (s p)` (the "closed" condition `N_{p+1} = N_1`).
-/
theorem subq_I_2_compare
    (ρ : ℝ → ℝ)
    (ξ : ℝ → ℝ)
    (g : ℝ → ℝ)
    (g_def : ∀ t, g t = ∫ u in (0 : ℝ)..t, ξ u)
    (gInv : ℝ → ℝ)
    (gInv_leftInverse : Function.LeftInverse gInv g)
    (gInv_rightInverse : Function.RightInverse gInv g)
    (f : ℝ → ℂ)
    (f_def : ∀ t, f t = Complex.exp (t * Complex.I) * (ρ t : ℂ))
    (M : ℝ → ℂ) (M_def : M = f ∘ gInv)
    (L : ℝ) (L_def : L = g (2 * Real.pi))
    (p : ℕ) (hp : 1 ≤ p) (s : Fin (p + 1) → ℝ)
    (hstep : ∀ i : Fin p,
      s ⟨i, Nat.lt_succ_of_lt i.isLt⟩ ≤ s ⟨i + 1, Nat.succ_lt_succ i.isLt⟩ ∧
      s ⟨i + 1, Nat.succ_lt_succ i.isLt⟩ ≤ s ⟨i, Nat.lt_succ_of_lt i.isLt⟩ + L)
    (hclose : M (s ⟨0, Nat.succ_pos _⟩) = M (s ⟨p, Nat.lt_succ_self _⟩))
    (hL : 0 < L) :
    (s ⟨p, Nat.lt_succ_self _⟩ - s ⟨0, Nat.succ_pos _⟩) / L ≤ (p : ℝ) := by
  sorry

/-! ### II.3.a — existence of `α ∈ W` with ≥ 2 distinct image points. -/

/--
**Book II.3.a (easy).**
"Construire un élément $\alpha = (\alpha_1, \cdots, \alpha_p)$ de $W$ tel que
l'ensemble constitué par les points $M(\alpha_i)$, $1 \leq i \leq p$, possède au
moins deux éléments."

English: Construct an element `α = (α_1, …, α_p) ∈ W` such that the set
`{M(α_i) | 1 ≤ i ≤ p}` has at least two elements.

The set `W` of énoncé II.3 (for `p ≥ 3` and `1 ≤ m ≤ p−1`):
points `(s_1, …, s_p) ∈ ℝ^p` satisfying `0 ≤ s_{i+1} − s_i ≤ L` and
`(m−1)L ≤ s_p − s_1 ≤ mL`.  Membership in `W` is unfolded inline.
-/
theorem subq_II_3_a
    (M : ℝ → ℂ) (L : ℝ)
    (p m : ℕ) (hp : 3 ≤ p) (hm₁ : 1 ≤ m) (hm₂ : m ≤ p - 1) :
    ∃ α : Fin p → ℝ,
      ((∀ i : Fin p, ∀ hi : (i : ℕ) + 1 < p,
            0 ≤ α ⟨(i : ℕ) + 1, hi⟩ - α i ∧
            α ⟨(i : ℕ) + 1, hi⟩ - α i ≤ L) ∧
        (∀ hp : 0 < p,
            ((m : ℝ) - 1) * L ≤
              α ⟨p - 1, Nat.sub_lt hp Nat.one_pos⟩ - α ⟨0, hp⟩ ∧
            α ⟨p - 1, Nat.sub_lt hp Nat.one_pos⟩ - α ⟨0, hp⟩ ≤ (m : ℝ) * L)) ∧
      ∃ i j : Fin p, M (α i) ≠ M (α j) := by
  sorry

/-! ### III.2.a — `E(D, n̂, P)` does not depend on `P` or on `n̂`. -/

/--
**Book III.2.a (medium).**
"Démontrer que $\mathcal{E}(D, \vec{n}, P)$ ne dépend pas du choix du point $P$
de $D$ ni du choix du vecteur normal unitaire $\vec{n}$."

English: Prove that `E(D, n̂, P) = ⟨OP, n̂⟩ · ⟨O'P, n̂⟩` does not depend on the
choice of `P` on the line `D` nor on the choice of unit normal `n̂` to `D`.

We model an affine line as a base point `P : ℂ` and a direction vector `v : ℂ`
with `v ≠ 0`; "P on D" means `P = P₀ + λ·v` for some `λ`; "n̂ unit normal to D"
means `‖n̂‖ = 1` and `⟨v, n̂⟩ = 0`.

Statement: for any two points `P₁, P₂` on the line `P₀ + ℝ·v` and any two unit
normals `n̂₁, n̂₂`, the products `⟨O − P_i, n̂_j⟩ · ⟨O' − P_i, n̂_j⟩` agree.
The two foci `O` and `O'` of the ellipse are taken as free complex parameters.
-/
theorem subq_III_2_a
    (O O' : ℂ)
    (P₀ v : ℂ) (hv : v ≠ 0)
    (P₁ P₂ : ℂ) (hP₁ : ∃ μ₁ : ℝ, P₁ = P₀ + (μ₁ : ℂ) * v)
    (hP₂ : ∃ μ₂ : ℝ, P₂ = P₀ + (μ₂ : ℂ) * v)
    (n₁ n₂ : ℂ)
    (hn₁_unit : ‖n₁‖ = 1) (hn₂_unit : ‖n₂‖ = 1)
    (hn₁_perp : (v.re * n₁.re + v.im * n₁.im) = 0)
    (hn₂_perp : (v.re * n₂.re + v.im * n₂.im) = 0) :
    ((P₁ - O).re * n₁.re + (P₁ - O).im * n₁.im) *
        ((P₁ - O').re * n₁.re + (P₁ - O').im * n₁.im) =
      ((P₂ - O).re * n₂.re + (P₂ - O).im * n₂.im) *
        ((P₂ - O').re * n₂.re + (P₂ - O').im * n₂.im) := by
  sorry

/-! ### III.3.b — `E(D(s)) = b²`. -/

/--
**Book III.3.b (hard).**
"Démontrer l'égalité $\mathcal{E}(D(s)) = b^2$."

English: Prove that the energy of the tangent line `D(s)` to the ellipse `B` at
`M(s)` equals `b²`.

We package the energy via a fixed unit normal `n̂(s)` perpendicular to the
velocity `M'(s)` and base point `M(s)` itself:
  `E(D(s)) = ⟨O − M(s), n̂(s)⟩ · ⟨O' − M(s), n̂(s)⟩`
The equation `E(D(s)) = b²` is independent of the choice of `n̂(s)` by III.2.a.

The ellipse data is supplied as free parameters: semi-axes `a, b > 0` with
`b < a`, focal distance `c = √(a² − b²)`, foci `O = 0` and `O' = 2c`, the
radial parametrization `ρ(t) = b² / (a − c·cos t)`, and the arc-length
parametrization `M = f ∘ gInv`.

Here we existentially quantify over `n̂(s)` to avoid pinning down a sign convention.
-/
theorem subq_III_3_b
    (a b : ℝ) (hab : 0 < b ∧ b < a)
    (c : ℝ) (c_eq : c = Real.sqrt (a ^ 2 - b ^ 2))
    (O O' : ℂ) (hO : O = 0) (hO' : O' = (2 * c : ℝ))
    (ρ : ℝ → ℝ)
    (ρ_ellipse : ∀ t, ρ t = b ^ 2 / (a - c * Real.cos t))
    (ξ : ℝ → ℝ)
    (xi_eq_sqrt : ∀ t, ξ t = Real.sqrt (ρ t ^ 2 + (deriv ρ t) ^ 2))
    (g : ℝ → ℝ)
    (g_def : ∀ t, g t = ∫ u in (0 : ℝ)..t, ξ u)
    (gInv : ℝ → ℝ)
    (gInv_leftInverse : Function.LeftInverse gInv g)
    (gInv_rightInverse : Function.RightInverse gInv g)
    (f : ℝ → ℂ)
    (f_def : ∀ t, f t = Complex.exp (t * Complex.I) * (ρ t : ℂ))
    (M : ℝ → ℂ) (M_def : M = f ∘ gInv)
    (s : ℝ) :
    ∃ n : ℂ,
      ‖n‖ = 1 ∧
        ((deriv M s).re * n.re + (deriv M s).im * n.im) = 0 ∧
        ((O - M s).re * n.re + (O - M s).im * n.im) *
            ((O' - M s).re * n.re + (O' - M s).im * n.im) =
          b ^ 2 := by
  sorry

/-! ### III.4.a — `b² = ‖OM‖ · ‖O'M‖ · sin²φ`. -/

/--
**Book III.4.a (easy).**
"Déduire des résultats précédents une relation liant $b$, $\sin \phi(s)$,
$\|\overrightarrow{OM}(s)\|$ et $\|\overrightarrow{O'M}(s)\|$."

English: Deduce a relation between `b`, `sin φ(s)`, `‖OM(s)‖`, and `‖O'M(s)‖`.

By III.3.a (energy = OM·O'M·cosφ·cosφ' with φ' = π−φ) and III.3.b
(energy = b²), we get
  `‖OM(s)‖ · ‖O'M(s)‖ · sin²φ(s) = b²`.

The ellipse data `a, b, c`, the foci `O, O'`, the parametrization `M`, and the
angle function `φ : ℝ → ℝ` (with values in `[0, π]`) are supplied as free
parameters.
-/
theorem subq_III_4_a
    (a b : ℝ) (hab : 0 < b ∧ b < a)
    (c : ℝ) (c_eq : c = Real.sqrt (a ^ 2 - b ^ 2))
    (O O' : ℂ) (hO : O = 0) (hO' : O' = (2 * c : ℝ))
    (M : ℝ → ℂ)
    (phi : ℝ → ℝ) (phi_mem : ∀ s, phi s ∈ Set.Icc (0 : ℝ) Real.pi)
    (s : ℝ) :
    ‖O - M s‖ * ‖O' - M s‖ * (Real.sin (phi s)) ^ 2 = b ^ 2 := by
  sorry

end

end AITP.P1Concrete
