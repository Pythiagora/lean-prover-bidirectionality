import Mathlib

open BigOperators

/-
P9 sub-question 22 (Mercier–Rombaldi 2013): rotation-index invariance under
reparametrisation.

Faithful Transcription of the corrigé (page 351–352).

Corrigé proof structure (three named moves):
  Move 1 — Substitution of variables: chain rule on `z = w ∘ φ` with `φ' > 0`
           gives `e^(i α_z(t)) = e^(i α_w(φ t))` on `[0, l_z]`.
  Move 2 — Lift uniqueness mod 2π: `(α_z(t) − α_w(φ t))/(2π)` is integer-valued
           and continuous on `[0, l_z]`, hence constant by connectedness.
  Move 3 — Endpoint difference: `α_z(l_z) − α_z(0) = α_w(φ l_z) − α_w(φ 0)`,
           which equals `α_w(l_w) − α_w(0)` by Q21 (period-shift invariance).

This is the corpus's hardest theorem (ceiling test). Both Goedel (0/64) and
Kimina (1/64 truncated false-positive) failed.

Mathlib v4.30.0-rc2.

The proof is admitted at the structural level documented below. The blocking
gap is twofold and is recorded in the accompanying .md.
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
  -- ============================================================
  -- Move 1 (corrigé "Substitution of variables").
  -- The chain rule on `z = w ∘ φ` with `φ' > 0` (from `StrictMono φ` and
  -- existence of a smooth inverse `ψ`) gives, formally,
  --   `deriv z t = deriv w (φ t) * (φ' t : ℂ)`,
  --   `‖deriv z t‖ = ‖deriv w (φ t)‖ * φ' t`,
  --   `deriv z t / ‖deriv z t‖ = deriv w (φ t) / ‖deriv w (φ t)‖`.
  -- Combined with the lift hypotheses on `[0, l_z]` (for `α_z`) and
  -- the lift hypothesis at `φ t` (for `α_w`, IF `φ t ∈ [0, l_w]`),
  -- this would give `Complex.exp (α_z t · I) = Complex.exp (α_w (φ t) · I)`
  -- for `t ∈ [0, l_z]`.
  --
  -- Mathlib API needed and present (sketch):
  --   * `HasDerivAt.comp` (chain rule, available)
  --   * `ContDiff.differentiable` (available)
  --   * `strictMono_of_hasDerivAt_pos` and converse via the inverse `ψ`
  --     (gives `φ' t ≠ 0`; with monotonicity, `φ' t > 0`).
  --   * `Complex.norm_real`, `Complex.ofReal_norm` (for `‖φ' t‖ = φ' t`)
  --
  -- Mathlib API needed and **partial**:
  --   No direct lemma `α_w (φ t)` makes sense as a lift unless `φ t ∈ [0, l_w]`,
  --   which is **not** in the hypotheses.
  --
  -- Documenting the gap at this level: see Move 3 for the load-bearing gap.
  -- We do not state Move 1 as a `have` because `α_w (φ t)` is meaningful only
  -- under additional information not given by the énoncé.
  --
  -- ============================================================
  -- Move 2 (corrigé "Lift uniqueness mod 2π").
  -- Granting Move 1, define `k : ℝ → ℝ`,
  --   `k t = (α_z t - α_w (φ t)) / (2 * π)`.
  -- Then `k` is continuous on `[0, l_z]` (composition of continuous functions)
  -- and integer-valued (from `e^(2πi · k t) = 1`, via
  -- `Complex.exp_eq_exp_iff_exists_int`). Connectedness of `[0, l_z]`
  -- (`isPreconnected_Icc`) plus `IsPreconnected.constant` for the integer-valued
  -- map then gives `k 0 = k l_z`, hence
  --   `α_z l_z - α_z 0 = α_w (φ l_z) - α_w (φ 0)`.
  --
  -- Mathlib API present:
  --   * `Complex.exp_eq_exp_iff_exists_int`
  --   * `IsPreconnected.constant` on `[0, l_z]`
  --   * `isPreconnected_Icc`
  --   * `Continuous.continuousOn`, `ContinuousOn.comp`
  --
  -- This move is fully reachable in Mathlib, conditional on Move 1 producing
  -- the equality `e^(i α_z t) = e^(i α_w (φ t))` on `[0, l_z]`. As Move 1 is
  -- itself blocked by the `φ t ∈ [0, l_w]` issue, we cannot instantiate Move 2.
  --
  -- ============================================================
  -- Move 3 (corrigé "Endpoint difference"), the **load-bearing gap**.
  -- The corrigé concludes:
  --   `α_z l_z - α_z 0 = α_w (φ l_z) - α_w (φ 0)              [from Move 2]`
  --                    `= α_w b - α_w a              [b = φ l_z, a = φ 0]`
  --                    `= α_w l_w - α_w 0          [by Q21]`.
  --
  -- The last step uses **Q21**: the rotation index does not depend on which
  -- length-`l_w` interval is chosen, i.e. for any continuous lift `β` on
  -- `[a, a + l_w]`, `(β(a + l_w) - β(a))/(2π) = (α_w(l_w) - α_w(0))/(2π)`.
  --
  -- Q21 is **not** a hypothesis here. Worse: the statement provides `α_w` only
  -- as a function `ℝ → ℝ` constrained to be a lift on `[0, l_w]`. Outside
  -- `[0, l_w]`, `α_w` is unconstrained junk. There is no canonical extension
  -- of `α_w` to `[a, b]` — it would need to be **constructed** using the
  -- lifting theorem, which is itself the content of Q16.
  --
  -- Even granting an extension `α̃_w : ℝ → ℝ` with `α̃_w | [0, l_w] = α_w` and
  -- `α̃_w` lifting `τ_w` everywhere, the equality `α̃_w(b) - α̃_w(a) = α_w l_w
  -- - α_w 0` for `b - a = l_w` requires Q21 (period-shift invariance), which
  -- itself uses periodicity of `τ_w` and a non-trivial argument over a
  -- partition by periods.
  --
  -- **Blocking diagnosis**:
  --   * `φ 0` and `φ l_z` are arbitrary reals; without `φ 0 = 0` or another
  --     normalisation, the lift values `α_w (φ 0)` and `α_w (φ l_z)` are
  --     not constrained by the hypotheses.
  --   * Q21 (period-shift invariance) is mathematically content-rich and is
  --     itself a separate sub-question of the corrigé.
  --   * Mathlib has no API for "rotation index of a regular periodic curve as
  --     a topological invariant of the image". The `Real.Angle` /
  --     `Complex.arg` machinery handles instantaneous arguments, not
  --     `(α(l) - α(0))/(2π)` integrals over period-intervals.
  sorry
