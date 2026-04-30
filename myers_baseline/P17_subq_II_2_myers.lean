import Mathlib

open BigOperators

/-!
Myers-style transcription of Mercier–Rombaldi P17, sub-question II.2.

Corrigé (page_025.tex, item 2):
  f(x) ∈ ℚ ⇔ 1 − |2x − 1| ∈ ℚ ∩ [0,1]
        ⇔ |2x − 1| ∈ ℚ
        ⇔ 2x − 1 ∈ ℚ
        ⇔ x ∈ ℚ.

Operationally (énoncé, page_006.tex), the tent map splits as
  f(x) = 2x          if x ∈ [0, 1/2]
  f(x) = 2 − 2x      if x ∈ ]1/2, 1].

Three named moves:
  1. case-split on x ≤ 1/2 vs x > 1/2;
  2. compute f x explicitly per case via abs_of_nonpos / abs_of_nonneg;
  3. transport rationality through the affine map (witness 2*q or
     (q+1)/2 in forward direction, q/2 or 1 − q/2 in backward).
-/

theorem subq_II_2
    (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - |2 * x - 1|)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∃ q : ℚ, x = (q : ℝ)) ↔ (∃ q : ℚ, f x = (q : ℝ)) := by
  -- Unpack the interval hypothesis.
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · -- Forward direction: x rational ⇒ f x rational.
    rintro ⟨q, hq⟩
    -- Move 1: case-split on x ≤ 1/2 vs x > 1/2.
    rcases le_or_gt x (1/2 : ℝ) with hxle | hxgt
    · -- Case x ≤ 1/2: 2x − 1 ≤ 0, hence f x = 2x.
      -- Move 2: compute |2x − 1| = 1 − 2x.
      have h_nonpos : 2 * x - 1 ≤ 0 := by linarith
      have h_abs : |2 * x - 1| = -(2 * x - 1) := abs_of_nonpos h_nonpos
      have h_fx : f x = 2 * x := by
        rw [hf x, h_abs]; ring
      -- Move 3: witness 2*q is rational and equals f x.
      refine ⟨2 * q, ?_⟩
      rw [h_fx, hq]
      push_cast
      ring
    · -- Case x > 1/2: 2x − 1 > 0, hence f x = 2 − 2x.
      have h_nonneg : 0 ≤ 2 * x - 1 := by linarith
      have h_abs : |2 * x - 1| = 2 * x - 1 := abs_of_nonneg h_nonneg
      have h_fx : f x = 2 - 2 * x := by
        rw [hf x, h_abs]; ring
      refine ⟨2 - 2 * q, ?_⟩
      rw [h_fx, hq]
      push_cast
      ring
  · -- Backward direction: f x rational ⇒ x rational.
    rintro ⟨q, hq⟩
    -- Move 1: same case-split on x ≤ 1/2 vs x > 1/2.
    rcases le_or_gt x (1/2 : ℝ) with hxle | hxgt
    · -- Case x ≤ 1/2: f x = 2x, so x = q/2.
      have h_nonpos : 2 * x - 1 ≤ 0 := by linarith
      have h_abs : |2 * x - 1| = -(2 * x - 1) := abs_of_nonpos h_nonpos
      have h_fx : f x = 2 * x := by
        rw [hf x, h_abs]; ring
      -- From f x = 2x and f x = q, deduce x = q/2.
      have h_2x : 2 * x = (q : ℝ) := by rw [← h_fx]; exact hq
      have h_x_eq : x = (q : ℝ) / 2 := by linarith
      refine ⟨q / 2, ?_⟩
      rw [h_x_eq]
      push_cast
      ring
    · -- Case x > 1/2: f x = 2 − 2x, so x = 1 − q/2.
      have h_nonneg : 0 ≤ 2 * x - 1 := by linarith
      have h_abs : |2 * x - 1| = 2 * x - 1 := abs_of_nonneg h_nonneg
      have h_fx : f x = 2 - 2 * x := by
        rw [hf x, h_abs]; ring
      have h_2x : 2 - 2 * x = (q : ℝ) := by rw [← h_fx]; exact hq
      have h_x_eq : x = 1 - (q : ℝ) / 2 := by linarith
      refine ⟨1 - q / 2, ?_⟩
      rw [h_x_eq]
      push_cast
      ring
