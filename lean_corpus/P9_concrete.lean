/-
  P9 — Concrete reformulation (Mercier & Rombaldi 2013, épreuve 1).

  This file restates the eight theorems of `LeanCorpus.P9` while inlining every
  custom auxiliary definition (`IndexAt`, `IndexOnIoo`, `fracPole`, `segmentFun`,
  `segmentIndex`, the `JordanArc` structure, `tau`, `rotationIndex`,
  `IsContLift`, `SameOrientation`) directly into the statements.  The goal is
  to give the prover access to fully expanded énoncés without having to unfold
  user-defined symbols.

  Auxiliary objects are inlined either as explicit lambdas (`fracPole`,
  `segmentFun`, `tau`, `rotationIndex`) or as `let`-bindings inside the
  theorem.  Predicates (`IndexAt`, `IsContLift`, `SameOrientation`) are
  expanded into their existential / conjunctive content.  The `JordanArc`
  structure is replaced by a list of free hypotheses on the underlying map
  `z : ℝ → ℂ` and the period `l : ℝ`.
-/
import LeanCorpus.Common

namespace AITP.P9Concrete

noncomputable section

open Filter Topology

/-! ### Q1 — I.A.1: index of `d / (X - c)^k`.

`IndexAt c f n` is inlined as the existential characterization on one-sided
limits in `EReal`. -/

/--
**Book I.A.1 (easy).** For `c ∈ ℝ`, `d ∈ ℝ \ {0}` and `k ≥ 1`, the algebraic
index of `x ↦ d / (x − c)^k` at `c` (read off from one-sided limits in `EReal`)
is:
  * `0`  if `k` is even;
  * `1`  if `k` is odd and `d > 0`;
  * `-1` if `k` is odd and `d < 0`.
-/
theorem subq_1 (c d : ℝ) (hd : d ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    let f : ℝ → ℝ := fun x => if x = c then 0 else d / (x - c) ^ k
    let n : ℤ := if Even k then 0 else if 0 < d then 1 else -1
    ∃ ℓminus ℓplus : EReal,
      Tendsto (fun x => (f x : EReal)) (𝓝[<] c) (𝓝 ℓminus) ∧
        Tendsto (fun x => (f x : EReal)) (𝓝[>] c) (𝓝 ℓplus) ∧
          ((n = 0 ∧ ℓminus = ℓplus) ∨
            (n = 1 ∧ ℓminus < ℓplus) ∨
            (n = -1 ∧ ℓminus > ℓplus)) := by
  sorry

/-! ### Q2 — I.A.2: linearity at a non-pole.

`IndexAt c f n` is inlined on both sides of the iff as the existential on
one-sided `EReal` limits. -/

/--
**Book I.A.2 (easy).** For `f, g, h : ℝ → ℝ` with `f x = g x + h x` for `x ≠ c`
and `h` continuous at `c`, the algebraic index of `f` at `c` equals that of `g`
at `c` for every integer `n`.
-/
theorem subq_2 (c : ℝ) (f g h : ℝ → ℝ)
    (hsum : ∀ x, x ≠ c → f x = g x + h x)
    (hh_cont : ContinuousAt h c)
    (n : ℤ) :
    (∃ ℓminus ℓplus : EReal,
        Tendsto (fun x => (f x : EReal)) (𝓝[<] c) (𝓝 ℓminus) ∧
          Tendsto (fun x => (f x : EReal)) (𝓝[>] c) (𝓝 ℓplus) ∧
            ((n = 0 ∧ ℓminus = ℓplus) ∨
              (n = 1 ∧ ℓminus < ℓplus) ∨
              (n = -1 ∧ ℓminus > ℓplus))) ↔
      (∃ ℓminus ℓplus : EReal,
        Tendsto (fun x => (g x : EReal)) (𝓝[<] c) (𝓝 ℓminus) ∧
          Tendsto (fun x => (g x : EReal)) (𝓝[>] c) (𝓝 ℓplus) ∧
            ((n = 0 ∧ ℓminus = ℓplus) ∨
              (n = 1 ∧ ℓminus < ℓplus) ∨
              (n = -1 ∧ ℓminus > ℓplus))) := by
  sorry

/-! ### Q4 — I.B.4: segment not meeting the real axis.

`segmentFun α β` is inlined; `segmentIndex` is replaced by the explicit
characterization "no real pole on `(0, 1)` ⇒ all integer-valued `IndexAt`
witnesses on `(0, 1)` vanish". -/

/--
**Book I.B.4 (easy).** If the segment `[α, β] ⊂ ℂ` does not intersect the real
axis (i.e. `α.im + x · (β − α).im ≠ 0` for all `x ∈ [0, 1]`), then for every
real `x ∈ (0, 1)` and every integer `n`, the rational function

  `Φ_{α,β}(x) = (α.re + x · (β − α).re) / (α.im + x · (β − α).im)`

cannot have algebraic index `n ≠ 0` at `x` (in fact, it is continuous there).
Hence the segment-index `I_{[α, β]} = (1/2) · I_0^1 Φ_{α,β}` vanishes.

We state the conclusion in the strong form: `Φ_{α,β}` is continuous at every
`x ∈ (0, 1)` (so a fortiori it has no pole there, and the segment-index
sums to `0`).
-/
theorem subq_4 (α β : ℂ) (hα : α.im ≠ 0) (hβ : β.im ≠ 0) (hαβ : α ≠ β)
    (hno_meet : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → α.im + x * (β - α).im ≠ 0) :
    let Φ : ℝ → ℝ :=
      fun x => (α.re + x * (β - α).re) / (α.im + x * (β - α).im)
    ∀ x : ℝ, 0 < x → x < 1 → ContinuousAt Φ x := by
  sorry

/-! ### Q7 — II.C.7: additivity of `I_a^b` across a point.

The opaque `IndexOnIoo` is bundled here as an arbitrary function
`Iioo : EReal → EReal → ℤ` satisfying the defining property: it sums
`IndexAt`-witnesses over real poles in the open interval.  Under that
property, additivity holds iff `f` is continuous at `c`.

This avoids committing to the internal `Classical.choice`-based definition. -/

/--
**Book II.C.7 (easy).** Let `Iioo : EReal → EReal → (ℝ → ℝ) → ℤ` be any
function satisfying the defining property of the open-interval algebraic
index: for every `a < b` in `EReal` and every `f : ℝ → ℝ`, there exist
`poles : Finset ℝ` lying inside `(a, b)` and an integer-valued labelling
`idx : ℝ → ℤ` such that `IndexAt c f (idx c)` for `c ∈ poles`,
`Iioo a b f = ∑_{c ∈ poles} idx c`, and these poles are exactly the
discontinuities of `f` inside `(a, b)`.

Then for `a < c < b` in `EReal` and `f : ℝ → ℝ`, additivity
`Iioo a b f = Iioo a c f + Iioo c b f` holds iff `f` is continuous at `c`.
-/
theorem subq_7 (a b : EReal) (c : ℝ) (hac : a < (c : EReal)) (hcb : (c : EReal) < b)
    (f : ℝ → ℝ)
    (Iioo : EReal → EReal → (ℝ → ℝ) → ℤ)
    (hIioo : ∀ a' b' : EReal, ∀ g : ℝ → ℝ,
      ∃ poles : Finset ℝ, ∃ idx : ℝ → ℤ,
        (∀ c' ∈ poles, a' < (c' : EReal) ∧ (c' : EReal) < b') ∧
          (∀ c' ∈ poles,
            ∃ ℓminus ℓplus : EReal,
              Tendsto (fun x => (g x : EReal)) (𝓝[<] c') (𝓝 ℓminus) ∧
                Tendsto (fun x => (g x : EReal)) (𝓝[>] c') (𝓝 ℓplus) ∧
                  ((idx c' = 0 ∧ ℓminus = ℓplus) ∨
                    (idx c' = 1 ∧ ℓminus < ℓplus) ∨
                    (idx c' = -1 ∧ ℓminus > ℓplus))) ∧
          Iioo a' b' g = ∑ c' ∈ poles, idx c') :
    (ContinuousAt f c) ↔
      Iioo a b f = Iioo a (c : EReal) f + Iioo (c : EReal) b f := by
  sorry

/-! ### Q12 — II.E.12: the matrix product `ᵗP · M`.

`matM` and `matP` are inlined as explicit `Matrix` lambdas via `let`. -/

/--
**Book II.E.12 (medium).** Let `n ≥ 1` and let `a : Fin (n + 2) → ℝ`,
`b : Fin n → ℝ` satisfy the recurrence
`a_k + a_{k+2} = a_{k+1} · b_{k+1}` for `0 ≤ k ≤ n − 1` and `a_{n+1} = 0`.
Define the tridiagonal matrix `M = (m_{ij}) ∈ M_n(ℝ)` with
`m_{ii} = b_i`, `m_{ij} = -1` for `|i − j| = 1`, and `0` otherwise; and the
lower-triangular matrix `P = (p_{ij}) ∈ M_n(ℝ)` with `p_{ij} = a_{i+1}` for
`j ≤ i` and `0` otherwise.

Then the entries of `ᵗP · M` are: `a_{i+1}` on the diagonal, `−a_i` on the
first super-diagonal, and `0` elsewhere.
-/
theorem subq_12 (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (n + 2) → ℝ) (b : Fin n → ℝ)
    (hrec : ∀ k : ℕ, k ≤ n - 1 → ∀ hk1 : k + 1 < n + 2, ∀ hk2 : k + 2 < n + 2,
      ∀ hk1' : k + 1 < n,
      a ⟨k, by omega⟩ + a ⟨k + 2, hk2⟩ =
        a ⟨k + 1, hk1⟩ * b ⟨k + 1, hk1'⟩)
    (ha_top : a ⟨n + 1, by omega⟩ = 0) :
    let M : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        if i = j then b i
        else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1
        else 0
    let P : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        if (j : ℕ) ≤ (i : ℕ) then a ⟨(i : ℕ) + 1, by omega⟩
        else 0
    ∀ i j : Fin n,
      (P.transpose * M) i j =
        if i = j then a ⟨(i : ℕ) + 1, by omega⟩
        else if (i : ℕ) + 1 = j then - a ⟨(i : ℕ), by omega⟩
        else 0 := by
  sorry

/-! ### Q16 — III.16: existence and uniqueness of the continuous lift `α_z`.

No auxiliary definition needed; the énoncé already lives in elementary
Mathlib vocabulary. -/

/--
**Book III.16 (medium).** Let `K ⊂ ℂ` be compact and star-shaped at `0`,
`F : ℂ → ℂ` be continuous on `K` with `‖F z‖ = 1` for `z ∈ K`, and let
`θ ∈ ℝ` be an argument of `F 0`.  Then for every `z ∈ K` there is a unique
continuous `α : ℝ → ℝ` on `[0, 1]` with `α 0 = θ` and
`F (t · z) = exp(i · α t)` for all `t ∈ [0, 1]`.
-/
theorem subq_16 (K : Set ℂ) (hK_compact : IsCompact K) (hK_zero : (0 : ℂ) ∈ K)
    (hK_star : ∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ((t : ℂ) * z) ∈ K)
    (F : ℂ → ℂ) (hF_cont : ContinuousOn F K)
    (hF_unit : ∀ z ∈ K, ‖F z‖ = 1)
    (θ : ℝ) (hθ : F 0 = Complex.exp (θ * Complex.I))
    (z : ℂ) (hz : z ∈ K) :
    ∃! α : ℝ → ℝ,
      ContinuousOn α (Set.Icc (0 : ℝ) 1) ∧
        α 0 = θ ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            F ((t : ℂ) * z) = Complex.exp (α t * Complex.I) := by
  sorry

/-! ### Q20 — IV.F.20: rotation index is an integer.

The `JordanArc` structure is unbundled into the free hypotheses on
`z : ℝ → ℂ` and the period `l : ℝ`.  The unit tangent `τ`, the rotation
index, and the continuous-lift predicate are all inlined. -/

/--
**Book IV.F.20 (easy).** Let `z : ℝ → ℂ` be a `C^k` Jordan arc (`k ≥ 1`):
regular (`z'(t) ≠ 0`), `l`-periodic with `l > 0` minimal, and simple on
`[0, l)`.  Let `α : ℝ → ℝ` be a continuous lift of the unit tangent
`τ(t) = z'(t) / ‖z'(t)‖` on `[0, l]` — i.e. `α` is continuous on `[0, l]`
and `τ t = exp(i · α t)` for every `t ∈ [0, l]`.

Then the rotation index `I_{z, α} = (α l − α 0) / (2π)` is an integer.
-/
theorem subq_20
    (kₐ : WithTop ℕ∞) (one_le_k : 1 ≤ kₐ)
    (z : ℝ → ℂ) (z_contDiff : ContDiff ℝ kₐ z)
    (z_regular : ∀ t : ℝ, deriv z t ≠ 0)
    (l : ℝ) (l_pos : 0 < l)
    (z_periodic : Function.Periodic z l)
    (l_minimal : ∀ T : ℝ, 0 < T → T < l → ¬ Function.Periodic z T)
    (z_simple : Set.InjOn z (Set.Ico 0 l))
    (α : ℝ → ℝ)
    (hα_cont : ContinuousOn α (Set.Icc 0 l))
    (hα_lift : ∀ t ∈ Set.Icc (0 : ℝ) l,
      deriv z t / (‖deriv z t‖ : ℂ) = Complex.exp (α t * Complex.I)) :
    ∃ k : ℤ, (α l - α 0) / (2 * Real.pi) = (k : ℝ) := by
  sorry

/-! ### Q22 — IV.F.22: rotation index depends only on the oriented support.

The two `JordanArc` records are unbundled into independent free hypotheses;
the `SameOrientation` predicate is inlined as the existence of an
increasing `C^1` reparametrization. -/

/--
**Book IV.F.22 (hard).** Let `z, w : ℝ → ℂ` both be `C^1` Jordan arcs
(regular, periodic with minimal positive periods `l_z`, `l_w`, simple on
`[0, l_·)`) with the same support and the same orientation, witnessed by
an increasing `C^1` diffeomorphism `φ : ℝ → ℝ` with `z = w ∘ φ`.

Then for any continuous lifts `α_z` of `τ_z = z' / ‖z'‖` on `[0, l_z]` and
`α_w` of `τ_w = w' / ‖w'‖` on `[0, l_w]`, the rotation indices coincide:
  `(α_z l_z − α_z 0) / (2π) = (α_w l_w − α_w 0) / (2π)`.
-/
theorem subq_22
    (k_z : WithTop ℕ∞) (one_le_k_z : 1 ≤ k_z)
    (z : ℝ → ℂ) (z_contDiff : ContDiff ℝ k_z z)
    (z_regular : ∀ t : ℝ, deriv z t ≠ 0)
    (l_z : ℝ) (l_z_pos : 0 < l_z)
    (z_periodic : Function.Periodic z l_z)
    (l_z_minimal : ∀ T : ℝ, 0 < T → T < l_z → ¬ Function.Periodic z T)
    (z_simple : Set.InjOn z (Set.Ico 0 l_z))
    (k_w : WithTop ℕ∞) (one_le_k_w : 1 ≤ k_w)
    (w : ℝ → ℂ) (w_contDiff : ContDiff ℝ k_w w)
    (w_regular : ∀ t : ℝ, deriv w t ≠ 0)
    (l_w : ℝ) (l_w_pos : 0 < l_w)
    (w_periodic : Function.Periodic w l_w)
    (l_w_minimal : ∀ T : ℝ, 0 < T → T < l_w → ¬ Function.Periodic w T)
    (w_simple : Set.InjOn w (Set.Ico 0 l_w))
    (φ ψ : ℝ → ℝ)
    (hφ_smooth : ContDiff ℝ 1 φ) (hψ_smooth : ContDiff ℝ 1 ψ)
    (hφψ_left : Function.LeftInverse ψ φ) (hφψ_right : Function.RightInverse ψ φ)
    (hφ_mono : StrictMono φ)
    (hzw_phi : ∀ t : ℝ, z t = w (φ t))
    (hsupp : z '' Set.univ = w '' Set.univ)
    (α_z α_w : ℝ → ℝ)
    (hα_z_cont : ContinuousOn α_z (Set.Icc 0 l_z))
    (hα_z_lift : ∀ t ∈ Set.Icc (0 : ℝ) l_z,
      deriv z t / (‖deriv z t‖ : ℂ) = Complex.exp (α_z t * Complex.I))
    (hα_w_cont : ContinuousOn α_w (Set.Icc 0 l_w))
    (hα_w_lift : ∀ t ∈ Set.Icc (0 : ℝ) l_w,
      deriv w t / (‖deriv w t‖ : ℂ) = Complex.exp (α_w t * Complex.I)) :
    (α_z l_z - α_z 0) / (2 * Real.pi) = (α_w l_w - α_w 0) / (2 * Real.pi) := by
  sorry

end

end AITP.P9Concrete
