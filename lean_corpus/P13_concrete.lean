/-
  P13 — Concrete reformulation (Mercier–Rombaldi 2008, épreuve 2).

  Mercier–Rombaldi 2008 épreuve 2 studies the sequence $(u_n)_{n \ge 1}$ where
  $u_n$ is the unique non-negative real root of the polynomial
  $f_n(x) = x^n + x^{n-1} + \cdots + x - 1$.  Parts I and II derive properties
  of $(u_n)$ and an explicit series expansion $(T_p)$.  Part III establishes
  the Lagrange reversion formula.  Part IV uses the formula for an alternative
  proof of $(T_p)$.

  Cross-references:
    * subq_I_1     — I.1, existence and uniqueness of `u_n ∈ [0,1]`
    * subq_I_2     — I.2, strict decrease of `(u_n)`
    * subq_I_3     — I.3, identity `u_n^{n+1} - 2 u_n + 1 = 0`
    * subq_I_4_a   — I.4.a, `u_2 = (√5 - 1)/2`
    * subq_I_4_b   — I.4.b, `u_n → 1/2`
    * subq_I_5     — I.5, `n · ε_n → 0` where `ε_n = u_n - 1/2`
    * subq_II_4_a  — II.4.a, `v_p / (1 + v_p)^{p+1} = 1/2^{p+1}` for `v_p = 2 u_p - 1`
    * subq_III_3_a — III.3.a, existence of the continuous extension `σ`

  All theorems take their data as free variables (no `Setup` structure); proofs
  are `sorry`. The file is intended as a calibration target for automated
  provers and to be type-checked verbatim.
-/
import LeanCorpus.Common

namespace AITP.P13Concrete

noncomputable section

/-! ### I.1 — existence and uniqueness of `u_n ∈ [0, 1]`. -/

/--
**Book I.1 (easy).**
"Démontrer, pour tout entier $n \geq 1$, l'existence d'une unique solution
réelle $\geq 0$ de l'équation : $x^n + x^{n-1} + \cdots + x - 1 = 0$.  Cette
solution est notée $u_n$.  Démontrer que l'on a $0 \leq u_n \leq 1$."

English: For every integer $n \geq 1$, the equation
$f_n(x) = x^n + x^{n-1} + \cdots + x - 1 = 0$ has a unique non-negative real
solution $u_n$, and $u_n \in [0, 1]$.

Lean note: $f_n(x) = \sum_{k = 0}^{n-1} x^{k+1} - 1 = \sum_{k = 1}^{n} x^k - 1$.
The hypothesis on `f` is given by an explicit `Finset.sum` formula.
-/
theorem subq_I_1
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃! u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ f n u = 0 := by
  sorry


/-! ### I.2 — `(u_n)` is strictly decreasing. -/

/--
**Book I.2 (easy).**
"Démontrer que la suite $(u_n)_{n \geq 1}$ est strictement décroissante."

English: The sequence $(u_n)_{n \geq 1}$ is strictly decreasing.

Lean note: The sequence `u : ℕ → ℝ` is supplied as a free variable together
with the defining property: for every `n ≥ 1`, `u n ∈ [0, 1]` and
`f_n(u n) = 0`.
-/
theorem subq_I_2
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0) :
    ∀ n : ℕ, 1 ≤ n → u (n + 1) < u n := by
  sorry


/-! ### I.3 — identity `u_n^{n+1} - 2 u_n + 1 = 0`. -/

/--
**Book I.3 (easy).**
"Démontrer que pour tout $n \geq 1$, on a : $u_n^{n+1} - 2 u_n + 1 = 0$."

English: For every $n \geq 1$, $u_n^{n+1} - 2 u_n + 1 = 0$.

Lean note: Algebraic consequence of `(x - 1) f_n(x) = x^{n+1} - 2 x + 1` and
`f_n(u_n) = 0`.
-/
theorem subq_I_3
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0) :
    ∀ n : ℕ, 1 ≤ n → (u n) ^ (n + 1) - 2 * u n + 1 = 0 := by
  sorry


/-! ### I.4.a — `u_2 = (√5 - 1) / 2`. -/

/--
**Book I.4.a (easy).** "Calculer $u_2$."

English: Compute $u_2$.  We have $u_2 = (\sqrt 5 - 1)/2$.

Lean note: $u_2$ is the non-negative root of $x^2 + x - 1 = 0$.
-/
theorem subq_I_4_a
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0) :
    u 2 = (Real.sqrt 5 - 1) / 2 := by
  sorry


/-! ### I.4.b — `(u_n) → 1/2`. -/

/--
**Book I.4.b (medium).**
"Démontrer que la suite $(u_n)_{n \geq 1}$ converge vers $\dfrac{1}{2}$."

English: The sequence $(u_n)_{n \geq 1}$ converges to $1/2$.

Lean note: Stated as a `Filter.Tendsto` claim along `Filter.atTop`.
-/
theorem subq_I_4_b
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0) :
    Filter.Tendsto u Filter.atTop (nhds (1 / 2 : ℝ)) := by
  sorry


/-! ### I.5 — `n · ε_n → 0`. -/

/--
**Book I.5 (medium).**
"Pour $n \geq 1$, on pose $\varepsilon_n = u_n - \dfrac{1}{2}$.  Démontrer que
$n \varepsilon_n$ tend vers $0$ lorsque $n$ tend vers $+\infty$."

English: For $n \geq 1$, set $\varepsilon_n = u_n - 1/2$.  Then
$n \varepsilon_n \to 0$ as $n \to +\infty$.

Lean note: Direct consequence of $u_n - 1/2 = (u_n^{n+1})/2$ from I.3 plus
$0 \le u_n \le 1$ and the bound from I.8 ($u_n \le 1/2 + 1/(2n)$ would give
$n \varepsilon_n \le 1/2$, but the stronger statement $n \varepsilon_n \to 0$
follows from $u_n^{n+1} \to 0$ once $u_n < 1 - \delta$ ultimately).
-/
theorem subq_I_5
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * (u n - 1 / 2)) Filter.atTop
      (nhds (0 : ℝ)) := by
  sorry


/-! ### II.4.a — `v_p / (1 + v_p)^{p+1} = 1 / 2^{p+1}`. -/

/--
**Book II.4.a (easy).**
"Pour $p \geq 1$, on pose $v_p = 2 u_p - 1$.  Démontrer que l'on a :
$\dfrac{v_p}{(1 + v_p)^{p+1}} = \dfrac{1}{2^{p+1}}$."

English: For $p \geq 1$, set $v_p = 2 u_p - 1$.  Then
$v_p / (1 + v_p)^{p+1} = 1 / 2^{p+1}$.

Lean note: Algebraic rearrangement of I.3 using $1 + v_p = 2 u_p$.  Note that
$1 + v_p > 0$ since $0 \le u_p \le 1$ gives $u_p \ge 1/2$ for $p \geq 1$ via
Mercier–Rombaldi (also I.4.b lower bound) — but for the formal statement we
only need the algebraic identity, and we add `1 + v_p ≠ 0` as derived hypothesis
from the standard fact $u_p > 0$ for $p \geq 1$ (consequence of $f_p(0) = -1 < 0$
and continuity).
-/
theorem subq_II_4_a
    (f : ℕ → ℝ → ℝ)
    (f_def : ∀ n x, f n x = (∑ k ∈ Finset.range n, x ^ (k + 1)) - 1)
    (u : ℕ → ℝ)
    (u_root : ∀ n, 1 ≤ n → 0 ≤ u n ∧ u n ≤ 1 ∧ f n (u n) = 0)
    (u_pos : ∀ n, 1 ≤ n → 0 < u n) :
    ∀ p : ℕ, 1 ≤ p →
      (2 * u p - 1) / (1 + (2 * u p - 1)) ^ (p + 1) = 1 / 2 ^ (p + 1) := by
  sorry


/-! ### III.3.a — continuous extension `σ` at `0`. -/

/--
**Book III.3.a (easy).**
"Soit $g : \mathbb{R} \to \mathbb{R}$ une fonction de classe $\mathcal{C}^\infty$
telle que $g(0) = 0$ et $g'(0) \neq 0$.  Justifier que l'on peut définir une
fonction $\sigma$ dans un voisinage de $0$ dans $\mathbb{R}$ par :
$\sigma(s) = \dfrac{s}{g(s)}$ si $s \neq 0$, et $\sigma(0) = \dfrac{1}{g'(0)}$."

English: Let $g : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with $g(0) = 0$ and
$g'(0) \neq 0$.  Define $\sigma$ near $0$ by $\sigma(s) = s/g(s)$ for $s \neq 0$
and $\sigma(0) = 1/g'(0)$.  Then $\sigma$ is continuous at $0$.

Lean note: We assert continuity at $0$ of the piecewise-defined function `σ`.
-/
theorem subq_III_3_a
    (g : ℝ → ℝ)
    (g_smooth : ContDiff ℝ ⊤ g)
    (g_zero : g 0 = 0)
    (g_deriv_ne : deriv g 0 ≠ 0) :
    let σ : ℝ → ℝ := fun s => if s = 0 then 1 / deriv g 0 else s / g s
    ContinuousAt σ 0 := by
  sorry


end

end AITP.P13Concrete
