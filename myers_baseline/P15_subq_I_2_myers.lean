import Mathlib

open BigOperators

/-
  Myers-style transcription of Mercier–Rombaldi P15, sub-question I.2.

  Énoncé: Δ : 𝒫 → 𝒫 défini par ΔP = P(X+1) − P(X) sur ℂ[X].
  Démontrer que ker Δ = ℂ (les polynômes constants) et que Δ n'est pas injective.

  Corrigé moves (page 011, §I.2):
    M1. Pour tout polynôme constant P, on a ΔP = 0 (donc Δ non injective).
    M2. Si P = Σ αₖ eₖ non constant dans ker Δ, alors ΔP = Σ_{k≥1} αₖ Δeₖ = 0
        ; or (Δeₖ)_{k≥1} est libre (échelonnée en degrés, cf. I.1), donc αₖ = 0
        pour k ≥ 1, donc P est constant.
    M3. Conclusion : ker Δ = ℂ.

  Move M2 is, in essence, the fact that Δ strictly drops the degree on non-constant
  polynomials: the (n−1)-coefficient of P.comp(X+1) − P equals n · leadingCoeff P,
  hence non-zero in characteristic zero, hence ΔP ≠ 0. This is the structural
  content of the staircase lemma at I.1.

  The Lean script encodes M2 as a coefficient-level identity rather than going
  through evaluation at infinitely many integer points (which would be route (b),
  the lower-abstraction infinite-roots argument).
-/

theorem subq_I_2
    (Δ : Polynomial ℂ → Polynomial ℂ)
    (hΔ : ∀ P : Polynomial ℂ, Δ P = P.comp (Polynomial.X + Polynomial.C 1) - P) :
    (∀ P : Polynomial ℂ, Δ P = 0 ↔ ∃ c : ℂ, P = Polynomial.C c)
      ∧ ¬ Function.Injective Δ := by
  refine ⟨?_, ?_⟩
  · -- Conjunct 1 : ker Δ = constants.
    intro P
    rw [hΔ]
    constructor
    · -- (⇒) If P.comp(X+1) − P = 0, then P is constant.
      -- Move M2 (corrigé): degree-drop forces P constant.
      intro h_eq
      -- From P.comp(X+1) - P = 0 we obtain P.comp(X+1) = P (the polynomial is
      -- fixed by the shift by 1).
      have h_comp_eq : P.comp (Polynomial.X + Polynomial.C 1) = P := sub_eq_zero.mp h_eq
      -- Move M2 (corrigé): degree drop forces P constant. We show natDegree P = 0
      -- by reading off the (n-1)-coefficient: if n := natDegree P ≥ 1, then in
      -- P.comp(X+1) the (n-1)-coefficient picks up an extra n · leadingCoeff P
      -- term (binomial expansion of (X+1)^n) which must vanish if P.comp(X+1) = P.
      -- Over ℂ (char 0) this forces leadingCoeff P = 0, contradicting n ≥ 1.
      refine ⟨P.coeff 0, ?_⟩
      apply Polynomial.eq_C_of_natDegree_eq_zero
      by_contra h_pos
      have hn_pos : 0 < P.natDegree := Nat.pos_of_ne_zero h_pos
      -- Compute (n-1)-coefficient of P.comp(X+1) using as_sum_range and
      -- coeff_X_add_one_pow.
      have h_expand : P.comp (Polynomial.X + Polynomial.C 1)
          = ∑ k ∈ Finset.range (P.natDegree + 1),
              Polynomial.C (P.coeff k) * (Polynomial.X + 1) ^ k := by
        conv_lhs => rw [P.as_sum_range]
        rw [show ((Polynomial.X : Polynomial ℂ) + Polynomial.C 1) = (Polynomial.X + 1) from by
          simp [map_one]]
        simp [Polynomial.sum_comp]
      -- Now read off the (n-1)-coefficient on both sides of h_comp_eq.
      have h_coeff_lhs : (P.comp (Polynomial.X + Polynomial.C 1)).coeff (P.natDegree - 1)
          = P.coeff (P.natDegree - 1) + (P.natDegree : ℂ) * P.coeff P.natDegree := by
        rw [h_expand, Polynomial.finset_sum_coeff]
        -- For each k, coeff (n-1) of C(P.coeff k) * (X+1)^k = P.coeff k * choose(k, n-1).
        have hsum : ∀ k ∈ Finset.range (P.natDegree + 1),
            (Polynomial.C (P.coeff k) * (Polynomial.X + 1) ^ k).coeff (P.natDegree - 1)
              = P.coeff k * (k.choose (P.natDegree - 1) : ℂ) := by
          intro k _
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
        rw [Finset.sum_congr rfl hsum]
        -- Only k = n-1 and k = n contribute.
        have hn1_mem : P.natDegree - 1 ∈ Finset.range (P.natDegree + 1) :=
          Finset.mem_range.mpr (by omega)
        have hn_mem : P.natDegree ∈ Finset.range (P.natDegree + 1) :=
          Finset.mem_range.mpr (by omega)
        have hne : P.natDegree - 1 ≠ P.natDegree := by omega
        rw [Finset.sum_eq_add_of_mem (P.natDegree - 1) P.natDegree hn1_mem hn_mem hne ?_]
        · -- choose (n-1) (n-1) = 1, choose n (n-1) = n (via Nat.choose_succ_self n).
          have h1 : (P.natDegree - 1).choose (P.natDegree - 1) = 1 := Nat.choose_self _
          have h2 : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
            -- choose n (n-1) = choose n 1 = n via the symmetry choose n k = choose n (n-k).
            have h_symm := Nat.choose_symm (show P.natDegree - 1 ≤ P.natDegree by omega)
            have h_sub : P.natDegree - (P.natDegree - 1) = 1 := by omega
            rw [h_sub] at h_symm
            rw [← h_symm, Nat.choose_one_right]
          rw [h1, h2]
          push_cast
          ring
        · -- All other indices k ∈ range (n+1), k ≠ n-1, k ≠ n have choose k (n-1) = 0.
          intro k hk_mem hk_ne
          have hk_le_n : k ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
          obtain ⟨hk_ne1, hk_ne2⟩ := hk_ne
          have h_lt : k < P.natDegree - 1 := by omega
          rw [Nat.choose_eq_zero_of_lt h_lt]
          simp
      -- The right-hand side coefficient is just P.coeff (n-1).
      have h_coeff_eq : P.coeff (P.natDegree - 1) + (P.natDegree : ℂ) * P.coeff P.natDegree
          = P.coeff (P.natDegree - 1) := by
        rw [← h_coeff_lhs, h_comp_eq]
      have h_lead_eq : (P.natDegree : ℂ) * P.coeff P.natDegree = 0 := by
        linear_combination h_coeff_eq
      -- P.coeff P.natDegree = leadingCoeff P, non-zero since natDegree P ≥ 1
      -- (which implies P ≠ 0).
      have hP_ne : P ≠ 0 := by
        intro hP0
        rw [hP0, Polynomial.natDegree_zero] at hn_pos
        exact absurd hn_pos (lt_irrefl 0)
      have h_lead_ne : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
      -- And (P.natDegree : ℂ) ≠ 0 since P.natDegree ≥ 1 and ℂ has char 0.
      have h_n_ne : (P.natDegree : ℂ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp hn_pos
      exact h_lead_ne (mul_left_cancel₀ h_n_ne (by simpa using h_lead_eq))
    · -- (⇐) If P = C c, then ΔP = 0.
      -- Move M1 (corrigé, forward direction): trivial via comp_C.
      rintro ⟨c, hc⟩
      subst hc
      simp [Polynomial.C_comp]
  · -- Conjunct 2 : Δ is not injective.
    -- Move M1 (corrigé): two distinct constants C 0 and C 1 both have Δ = 0.
    intro h_inj
    have h0 : Δ (Polynomial.C (0 : ℂ)) = 0 := by
      rw [hΔ]; simp
    have h1 : Δ (Polynomial.C (1 : ℂ)) = 0 := by
      rw [hΔ]; simp
    have h_eq : Polynomial.C (0 : ℂ) = Polynomial.C (1 : ℂ) :=
      h_inj (h0.trans h1.symm)
    -- C 0 ≠ C 1 since they have distinct 0-coefficients.
    set_option linter.unnecessarySimpa false in
    have h_zero_one : (0 : ℂ) = 1 := by
      have h_coeff := congrArg (fun p => Polynomial.coeff p 0) h_eq
      simpa using h_coeff
    exact zero_ne_one h_zero_one
