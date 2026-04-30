import Mathlib

open BigOperators

theorem subq_4 (α β : ℂ) (hα : α.im ≠ 0) (hβ : β.im ≠ 0) (hαβ : α ≠ β)
    (hno_meet : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → α.im + x * (β - α).im ≠ 0) :
    let Φ : ℝ → ℝ :=
      fun x => (α.re + x * (β - α).re) / (α.im + x * (β - α).im)
    ∀ x : ℝ, 0 < x → x < 1 → ContinuousAt Φ x := by
  intro Φ x hx_lo hx_hi
  -- Move 1 (corrigé): the numerator `α.re + x · (β − α).re` is linear in `x`,
  -- hence continuous. Built explicitly from `continuous_const`, `continuous_id`,
  -- and the algebra of continuous functions (`.add`, `.mul`).
  have h_num_cont : ContinuousAt (fun x : ℝ => α.re + x * (β - α).re) x := by
    exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
  -- Move 2 (corrigé): the denominator `α.im + x · (β − α).im` is linear in `x`,
  -- hence continuous. Same explicit chain as Move 1.
  have h_den_cont : ContinuousAt (fun x : ℝ => α.im + x * (β - α).im) x := by
    exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
  -- Move 3 (corrigé): the denominator does not vanish at `x` because
  -- `0 < x < 1 ⊂ [0, 1]` and `hno_meet` rules out vanishing on `[0, 1]`.
  have h_den_ne : α.im + x * (β - α).im ≠ 0 :=
    hno_meet x hx_lo.le hx_hi.le
  -- Move 4 (corrigé): the quotient of two functions continuous at `x`,
  -- with non-vanishing denominator, is continuous at `x`: `ContinuousAt.div`.
  exact h_num_cont.div h_den_cont h_den_ne
