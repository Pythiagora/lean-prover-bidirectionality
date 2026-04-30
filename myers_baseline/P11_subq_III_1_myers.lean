import Mathlib

open BigOperators Filter Topology

/-
P11.subq_III_1 — Myers (faithful corrigé transcription).

Corrigé (Mercier–Rombaldi 2006, p. 20, III.1):

  "En notant M = sup_{t ∈ ]p, q[} |g'(t)| et en utilisant le théorème
   des accroissements finis, on a pour tous x, y dans ]p, q[ :
        |g(x) − g(y)| = |x − y| |g'(ξ)| ≤ M |x − y| → 0 quand (x,y) → (q,q).
   On déduit alors du critère de Cauchy que la fonction g admet une
   limite finie en q."

Two named moves:
  1. (MVT / accroissements finis) g is M-Lipschitz on ]p, q[.
  2. (Cauchy criterion) The image filter (𝓝[<] q).map g is Cauchy on ℝ;
     ℝ is complete, hence g admits a finite limit at q⁻.

Mathlib transcription:
  Move 1: `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` on the convex
          set `Set.Ioo p q`, from `HasDerivAt → HasDerivWithinAt`.
  Move 2: `LipschitzOnWith.uniformContinuousOn`,
          `Cauchy.map_of_le` (Cauchy filter pushed through a uniformly
                              continuous-on map),
          and `cauchy_map_iff_exists_tendsto` (in a complete uniform space,
                                               Cauchy(map f l) ↔ ∃ x, Tendsto f l (𝓝 x)).
  The neighbourhood filter `𝓝[<] q` is shown to be Cauchy via
          `cauchy_nhds.mono`, and the principal containment
          `𝓝[<] q ≤ 𝓟 (Ioo p q)` uses `nhdsWithin_Ioo_eq_nhdsLT`
          + `nhdsWithin` ≤ principal of its set (`inf_le_right`).
-/

theorem subq_III_1
    (p q : ℝ) (hpq : p < q)
    (g : ℝ → ℝ) (g' : ℝ → ℝ)
    (g_deriv : ∀ t ∈ Set.Ioo p q, HasDerivAt g (g' t) t)
    (M : ℝ) (g'_bdd : ∀ t ∈ Set.Ioo p q, |g' t| ≤ M) :
    ∃ ℓ : ℝ, Filter.Tendsto g (nhdsWithin q (Set.Iio q)) (nhds ℓ) := by
  -- Move 0 (preliminary): M ≥ 0, since |g'| ≤ M at any interior point.
  have hM_nn : 0 ≤ M := by
    have hmid : (p + q) / 2 ∈ Set.Ioo p q := by
      refine ⟨?_, ?_⟩ <;> linarith
    have := g'_bdd _ hmid
    have habs : 0 ≤ |g' ((p + q) / 2)| := abs_nonneg _
    linarith
  -- Move 1 (corrigé: théorème des accroissements finis):
  --   g is M-Lipschitz on the convex open interval (p, q).
  have h_conv : Convex ℝ (Set.Ioo p q) := convex_Ioo p q
  have h_dwa : ∀ t ∈ Set.Ioo p q,
      HasDerivWithinAt g (g' t) (Set.Ioo p q) t := fun t ht =>
    (g_deriv t ht).hasDerivWithinAt
  have h_bdd_nn : ∀ t ∈ Set.Ioo p q, ‖g' t‖₊ ≤ M.toNNReal := by
    intro t ht
    have h1 : |g' t| ≤ M := g'_bdd t ht
    -- ‖x‖₊ ≤ M.toNNReal ↔ ‖x‖ ≤ M (when 0 ≤ M)
    rw [← NNReal.coe_le_coe]
    simp [Real.coe_toNNReal _ hM_nn, Real.norm_eq_abs, h1]
  have h_lip : LipschitzOnWith M.toNNReal g (Set.Ioo p q) :=
    h_conv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le h_dwa h_bdd_nn
  -- Move 2 (corrigé: critère de Cauchy):
  --   g uniformly continuous on (p, q), pushes Cauchy filters to Cauchy filters,
  --   hence (𝓝[<] q).map g is Cauchy in ℝ; completeness gives the limit.
  have h_uc : UniformContinuousOn g (Set.Ioo p q) := h_lip.uniformContinuousOn
  -- The filter 𝓝[<] q is Cauchy (it refines the Cauchy filter 𝓝 q).
  have h_cauchy_nhds : Cauchy (𝓝[<] q) :=
    cauchy_nhds.mono nhdsWithin_le_nhds
  -- 𝓝[<] q is contained in the principal filter of (p, q).
  have h_le_principal : 𝓝[<] q ≤ Filter.principal (Set.Ioo p q) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hpq]
    -- 𝓝[s] x = 𝓝 x ⊓ 𝓟 s, so 𝓝[s] x ≤ 𝓟 s by inf_le_right.
    exact inf_le_right
  -- Push Cauchyness through g via uniform continuity on (p, q).
  have h_cauchy_map : Cauchy (Filter.map g (𝓝[<] q)) :=
    h_cauchy_nhds.map_of_le h_uc h_le_principal
  -- In complete ℝ, Cauchy of (map g _) is equivalent to existence of a limit.
  exact (cauchy_map_iff_exists_tendsto).mp h_cauchy_map
