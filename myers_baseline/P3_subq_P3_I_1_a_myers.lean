import Mathlib

open BigOperators Real

/-!
# Myers transcription of P3, sub-question I.1.a (Weierstrass tangent half-angle)

Statement: for `θ ∈ [0, π/2]` and `t = tan(θ/2)`,
  `cos θ = (1 - t²)/(1 + t²)`,
  `sin θ = (2t)/(1 + t²)`,
and if `t = q` for some rational `q`, then `cos θ` and `sin θ` are rational.

Corrigé route (Mercier-Rombaldi, §3.2, paragraph 1.1.a, page 95):

> "On connaît les formules
>     x = cos θ = (1 - t²)/(1 + t²)   et   y = sin θ = 2t/(1 + t²).
> Si t ∈ ℚ, x et y sont les quotients de deux rationnels : ce sont
> donc des rationnels."

Named moves used here:
  (M1)   double-angle identity for cosine     : `Real.cos_two_mul'`
         (cos(2α) = cos²α - sin²α — verbatim form chosen by the corrigé)
  (M2)   double-angle identity for sine       : `Real.sin_two_mul`
         (sin(2α) = 2 sin α cos α)
  (M3)   Pythagorean identity                  : `Real.sin_sq_add_cos_sq`
         (sin²α + cos²α = 1)
  (M4)   tangent as sine over cosine          : `Real.tan_eq_sin_div_cos`
  (M5)   side condition cos(θ/2) > 0          : `Real.cos_pos_of_mem_Ioo`
         (justified from θ ∈ [0, π/2] ⇒ θ/2 ∈ [0, π/4] ⊂ (-π/2, π/2))
  (M6)   ℚ closed under arithmetic             : the `(1 - q²)/(1 + q²)`
         and `2q/(1 + q²)` rational witnesses, cast back via `push_cast`.

The closure of each Weierstrass identity (after the four named moves are
applied) is a single polynomial-fraction normalisation under the
non-vanishing hypothesis `cos(θ/2) ≠ 0` — `field_simp` + `ring` performs
exactly that normalisation.  The corrigé's "On divise par cos²(θ/2)" is
inscribed as `field_simp [hcos_ne]` followed by `ring`.
-/

theorem subq_P3_I_1_a (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    let t := Real.tan (θ / 2)
    Real.cos θ = (1 - t ^ 2) / (1 + t ^ 2)
      ∧ Real.sin θ = (2 * t) / (1 + t ^ 2)
      ∧ (∀ q : ℚ, t = (q : ℝ) →
          (∃ qx : ℚ, Real.cos θ = (qx : ℝ)) ∧ (∃ qy : ℚ, Real.sin θ = (qy : ℝ))) := by
  -- Range bounds on θ/2.
  have hθ_lo : 0 ≤ θ := hθ.1
  have hθ_hi : θ ≤ Real.pi / 2 := hθ.2
  have hhalf_lo : 0 ≤ θ / 2 := by linarith
  have hhalf_hi : θ / 2 ≤ Real.pi / 4 := by linarith
  -- (M5) Side condition: cos(θ/2) > 0, hence ≠ 0.  Justified by θ/2 ∈ (-π/2, π/2).
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have hcos_ne : Real.cos (θ / 2) ≠ 0 := ne_of_gt hcos_pos
  -- (M4) Tangent as sine over cosine.
  have htan_eq : Real.tan (θ / 2) = Real.sin (θ / 2) / Real.cos (θ / 2) :=
    Real.tan_eq_sin_div_cos (θ / 2)
  -- (M3) Pythagorean identity.
  have hpyth : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (θ / 2)
  -- (M1) cos θ = cos²(θ/2) - sin²(θ/2)  (corrigé's "On connaît les formules").
  -- We invoke `Real.cos_two_mul'` at α = θ/2 then rewrite `2 * (θ/2) = θ`.
  have hcos_2 : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    have e : 2 * (θ / 2) = θ := by ring
    rw [e] at h
    exact h
  -- (M2) sin θ = 2 sin(θ/2) cos(θ/2).
  have hsin_2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    have e : 2 * (θ / 2) = θ := by ring
    rw [e] at h
    exact h
  -- Auxiliary: rewrite 1 + tan²(θ/2) = 1/cos²(θ/2) using hpyth and the side condition.
  -- This is the corrigé's "On divise par cos²(θ/2)" step, named.
  have h_one_plus_tan_sq : 1 + Real.tan (θ / 2) ^ 2 = 1 / Real.cos (θ / 2) ^ 2 := by
    rw [htan_eq, div_pow]
    field_simp
    linarith [hpyth]
  -- Weierstrass for cos θ.  Strategy: rewrite using hcos_2, htan_eq, h_one_plus_tan_sq;
  -- the goal then reduces to a `field_simp + ring` computation under hcos_ne.
  have hcos_W : Real.cos θ = (1 - Real.tan (θ / 2) ^ 2) / (1 + Real.tan (θ / 2) ^ 2) := by
    rw [hcos_2, h_one_plus_tan_sq, htan_eq]
    field_simp
  -- Weierstrass for sin θ: same structure.
  have hsin_W : Real.sin θ = (2 * Real.tan (θ / 2)) / (1 + Real.tan (θ / 2) ^ 2) := by
    rw [hsin_2, h_one_plus_tan_sq, htan_eq]
    field_simp
  -- Now assemble the conjunction.  `simp only []` unfolds the `let t`.
  refine ⟨?_, ?_, ?_⟩
  · simpa using hcos_W
  · simpa using hsin_W
  · -- (M6) Rationality clause.
    intro q hq
    -- Substitute t = q in the Weierstrass forms.
    have hcos_q : Real.cos θ = (1 - (q : ℝ) ^ 2) / (1 + (q : ℝ) ^ 2) := by
      rw [hcos_W, hq]
    have hsin_q : Real.sin θ = (2 * (q : ℝ)) / (1 + (q : ℝ) ^ 2) := by
      rw [hsin_W, hq]
    refine ⟨⟨(1 - q ^ 2) / (1 + q ^ 2), ?_⟩, ⟨(2 * q) / (1 + q ^ 2), ?_⟩⟩
    · rw [hcos_q]; push_cast; ring
    · rw [hsin_q]; push_cast; ring
