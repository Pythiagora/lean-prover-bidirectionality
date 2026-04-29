/-
  P12 — Concrete reformulation (Mercier–Rombaldi 2007, épreuve 2).

  The problem builds an everywhere-differentiable strictly increasing
  $\mathbb{R} \to \mathbb{R}$ function whose derivative vanishes on a dense set,
  via cube-roots, the auxiliary sequence
    $a_n = n^{1/3} \cos(n^{1/3})$
  and Baire-style arguments.

  Each theorem takes all required data as *free* variables. The cube-root
  function `f` is consistently introduced via its defining algebraic property
  `f(x)^3 = x` (énoncé: "$f(x)^3 = x$ pour tout $x \in \mathbb{R}$").
  Statements that would require the *generalized* derivative `f'(0) = +∞` (not
  available in Mathlib's `HasDerivAt` API) were filtered upstream and are
  absent from this concrete file.

  Selected sub-questions (8 of 25 formalizable):
    * subq_I_B_1_d   — I.B.1.d  (medium): cube-root Hölder bound
    * subq_I_B_1_e   — I.B.1.e  (medium): uniform continuity of cube-root
    * subq_I_B_2_a   — I.B.2.a  (easy):    quadratic inequality
    * subq_I_C_3     — I.C.3    (medium):  density of $\{a_n\}$ in $\mathbb{R}$
    * subq_I_C_4     — I.C.4    (medium):  convergence of two scalar series
    * subq_III_A_2   — III.A.2  (easy):    Baire — countable ∩ open denses dense
    * subq_III_A_3   — III.A.3  (medium):  Baire — remove a countable subset
    * subq_III_B_1_c — III.B.1.c (medium): integral bound on bump majorant
-/
import LeanCorpus.Common

namespace AITP.P12Concrete

noncomputable section

/-! ### I.B.1.d — Cube-root Hölder-type bound. -/

/--
**Book I.B.1.d (medium).**
"Démontrer que pour tous $x, y \in \mathbb{R}$, on a
$|f(x) - f(y)| \le 2 \left| f\!\left(\dfrac{x - y}{2}\right) \right|$."

English: For every real $x, y$, $|f(x) - f(y)| \le 2 |f((x-y)/2)|$, where
$f$ is the real cube-root function.

Lean rendering: $f$ is supplied as a free function with the algebraic
characterization `f(x)^3 = x` for every $x$ (énoncé verbatim). Continuity
of $f$ is included since the énoncé treats $f$ as the standard cube-root.
-/
theorem subq_I_B_1_d
    (f : ℝ → ℝ) (f_cube : ∀ x : ℝ, f x ^ 3 = x)
    (f_cont : Continuous f) :
    ∀ x y : ℝ, |f x - f y| ≤ 2 * |f ((x - y) / 2)| := by
  sorry

/-! ### I.B.1.e — Uniform continuity of the cube-root. -/

/--
**Book I.B.1.e (medium).**
"Démontrer que la fonction $f$ est uniformément continue sur $\mathbb{R}$."

English: The real cube-root function $f$ is uniformly continuous on $\mathbb{R}$.

The cube-root is supplied via its defining property `f(x)^3 = x` and the
hypothesis that it is continuous (which is part of the standard énoncé
identification "f(x) = x^{1/3}" — see the preamble of part I).
-/
theorem subq_I_B_1_e
    (f : ℝ → ℝ) (f_cube : ∀ x : ℝ, f x ^ 3 = x)
    (f_cont : Continuous f) :
    UniformContinuous f := by
  sorry

/-! ### I.B.2.a — Quadratic lower bound. -/

/--
**Book I.B.2.a (easy).**
"Démontrer que pour tous $x, y \in \mathbb{R}$, on a
$x^2 + xy + y^2 \ge \dfrac{3}{4} x^2$."

English: For every real $x, y$, $x^2 + xy + y^2 \ge \tfrac{3}{4} x^2$.

The inequality is genuine (not closable by `ring_nf`/`norm_num`/`omega`/
`decide`/`simp`/`trivial` alone): it requires the auxiliary square
$(x/2 + y)^2 \ge 0$. Equivalent form $x^2 + xy + y^2 - \tfrac{3}{4} x^2
= (x/2 + y)^2 \ge 0$.
-/
theorem subq_I_B_2_a (x y : ℝ) :
    x ^ 2 + x * y + y ^ 2 ≥ (3 / 4 : ℝ) * x ^ 2 := by
  sorry

/-! ### I.C.3 — Density of `{a_n | n ∈ ℕ}` in ℝ. -/

/--
**Book I.C.3 (medium).**
"Démontrer que l'ensemble $\{a_n \mid n \in \mathbb{N}\}$ est dense dans
$\mathbb{R}$."

English: For $a_n = n^{1/3} \cos(n^{1/3})$, the set $\{a_n \mid n \in
\mathbb{N}\}$ is dense in $\mathbb{R}$.

Lean rendering: the cube-root $f$ is again supplied via `f(x)^3 = x`. The
sequence $a_n$ is then $f(n) \cdot \cos(f(n))$. Density is expressed as
`Dense (Set.range a)`.
-/
theorem subq_I_C_3
    (f : ℝ → ℝ) (f_cube : ∀ x : ℝ, f x ^ 3 = x)
    (f_cont : Continuous f)
    (a : ℕ → ℝ) (a_def : ∀ n : ℕ, a n = f n * Real.cos (f n)) :
    Dense (Set.range a) := by
  sorry

/-! ### I.C.4 — Convergence of `∑ λ_n` and `∑ λ_n f(a_n)`. -/

/--
**Book I.C.4 (medium).**
"Pour tout entier $n \ge 0$, on pose $\lambda_n = \dfrac{1}{n^2 + 1}$.
Démontrer que les séries de terme général $\lambda_n$ et $\lambda_n f(a_n)$
sont convergentes."

English: For $\lambda_n = 1/(n^2 + 1)$ and $a_n = n^{1/3} \cos(n^{1/3})$,
both series $\sum_n \lambda_n$ and $\sum_n \lambda_n f(a_n)$ converge.

Convergence in Mathlib is rendered via `Summable`; this is the standard
formulation for series of real numbers.
-/
theorem subq_I_C_4
    (f : ℝ → ℝ) (f_cube : ∀ x : ℝ, f x ^ 3 = x)
    (f_cont : Continuous f)
    (a : ℕ → ℝ) (a_def : ∀ n : ℕ, a n = f n * Real.cos (f n))
    (lam : ℕ → ℝ) (lam_def : ∀ n : ℕ, lam n = 1 / ((n : ℝ) ^ 2 + 1)) :
    Summable lam ∧ Summable (fun n => lam n * f (a n)) := by
  sorry

/-! ### III.A.2 — Countable intersection of dense open sets is dense. -/

/--
**Book III.A.2 (easy).**
"Démontrer que l'ensemble $B = \displaystyle\bigcap_{n \in \mathbb{N}} V_n$
est dense dans $\mathbb{R}$."

English: A countable intersection of open dense subsets of $\mathbb{R}$ is
dense in $\mathbb{R}$ (Baire category for $\mathbb{R}$).

This is the textbook statement of the Baire category theorem applied to the
complete metric space $\mathbb{R}$.
-/
theorem subq_III_A_2
    (V : ℕ → Set ℝ)
    (hV_open : ∀ n, IsOpen (V n))
    (hV_dense : ∀ n, Dense (V n)) :
    Dense (⋂ n : ℕ, V n) := by
  sorry

/-! ### III.A.3 — Removing a countable subset preserves density of `B`. -/

/--
**Book III.A.3 (medium).**
"Soit $(x_n)_{n \in \mathbb{N}}$ une suite de points de $B$. En considérant
les ensembles ouverts $V_n \setminus \{x_n\}$, démontrer que l'ensemble
$B' = B \setminus \{x_n \mid n \in \mathbb{N}\}$ est dense dans $\mathbb{R}$."

English: Let $V_n$ be open dense in $\mathbb{R}$, $B = \bigcap_n V_n$, and
$(x_n)$ a sequence of points of $B$. Then $B \setminus \{x_n \mid n \in
\mathbb{N}\}$ is dense in $\mathbb{R}$.

The hint `V_n \setminus \{x_n\}` is recorded in the docstring; the
statement itself bypasses the hint and gives the conclusion directly.
-/
theorem subq_III_A_3
    (V : ℕ → Set ℝ)
    (hV_open : ∀ n, IsOpen (V n))
    (hV_dense : ∀ n, Dense (V n))
    (x : ℕ → ℝ)
    (hx_mem : ∀ n, x n ∈ ⋂ k : ℕ, V k) :
    Dense ((⋂ n : ℕ, V n) \ Set.range x) := by
  sorry

/-! ### III.B.1.c — Integral bound on a continuous bump majorant. -/

/--
**Book III.B.1.c (medium).**
"Démontrer l'inégalité $\displaystyle\int_a^b g(t)\, dt \le \varepsilon$."

English: Let $a < b$, $\varepsilon > 0$, $(\alpha_k)$ a positive sequence
with $2 \sum_k \alpha_k \le \varepsilon$, $(c_k) \subset [a, b]$. Set
$I_k = (c_k - \alpha_k, c_k + \alpha_k)$. Let $n \in \mathbb{N}$ and let
$g : [a, b] \to [0, 1]$ be continuous with $g(x) = 0$ outside
$\bigcup_{k \le n} I_k$. Then $\int_a^b g(t)\, dt \le \varepsilon$.

The bound uses only the structural data: the support of `g` is contained
in a union of `n + 1` intervals of total length $\le 2 \sum_k \alpha_k
\le \varepsilon$, and `g ≤ 1` on that support.
-/
theorem subq_III_B_1_c
    (a b : ℝ) (hab : a < b) (ε : ℝ) (hε : 0 < ε)
    (α : ℕ → ℝ) (hα_pos : ∀ k, 0 < α k)
    (hα_sum : Summable α) (hα_bound : 2 * ∑' k, α k ≤ ε)
    (c : ℕ → ℝ) (hc_mem : ∀ k, c k ∈ Set.Icc a b)
    (n : ℕ)
    (g : ℝ → ℝ) (g_cont : Continuous g)
    (g_range : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1)
    (g_supp : ∀ x ∈ Set.Icc a b,
      (∀ k, k ≤ n → x ∉ Set.Ioo (c k - α k) (c k + α k)) → g x = 0) :
    ∫ t in a..b, g t ≤ ε := by
  sorry

end

end AITP.P12Concrete
