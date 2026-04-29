/-
  P16_concrete — Concrete reformulation of Problem 16
  (Mercier–Rombaldi 2011, épreuve 2).

  Theme: the spaces `BC⁰(ℝ, ℝ)` (continuous bounded) and
  `BC¹(ℝ, ℝ)` (`C¹` with both `φ` and `φ'` bounded) as Banach spaces, and the
  differential operator `L_f : φ ↦ φ' + f ∘ φ`.  The book studies invertibility
  of `L_f` and the Theorem: `L_f` is a homeomorphism iff `f` is.

  Each theorem below takes all required data — `f`, candidate maps, integral
  operators, etc. — as free variables.  No `Setup` structure is used.

  Encoding choices (see task spec, point 4):
    * `BC⁰` is encoded as a function `φ : ℝ → ℝ` with `Continuous φ` and
      `∃ M, ∀ x, |φ x| ≤ M`.  We do *not* use `BoundedContinuousFunction`
      directly to keep statements faithful to the énoncé.
    * `BC¹` is encoded as `(φ : ℝ → ℝ)` with `ContDiff ℝ 1 φ` plus
      `∃ M, ∀ x, |φ x| + |deriv φ x| ≤ M`.
    * The non-linear operators `N_f`, `L_f` are kept inline via
      `(N : (ℝ → ℝ) → (ℝ → ℝ)) (hN : ∀ φ x, N φ x = f (φ x))` etc.
    * Homeomorphism on `ℝ` is encoded as `Continuous f ∧ Function.Bijective f`
      (which by I.3.c is equivalent to having a continuous two-sided inverse).
-/
import LeanCorpus.Common

namespace AITP.P16Concrete

noncomputable section

/-! ### I.1.a — `f ∘ y` is continuous and bounded. -/

/--
**Book I.1.a (easy).**
"Soit $y \in \mathcal{BC}^0(\mathbb{R}, \mathbb{R})$. Montrer que $f \circ y$ est
continue et bornée. On donne ainsi un sens à $\mathcal{N}_f$ comme application
de $\mathcal{BC}^0(\mathbb{R}, \mathbb{R})$ dans lui-même."

English: For `f : ℝ → ℝ` continuous and `y : ℝ → ℝ` continuous and bounded,
the composite `f ∘ y` is continuous and bounded. This justifies
`N_f : BC⁰ → BC⁰`.

Lean: `BC⁰` is unfolded as a function with `Continuous` and an explicit
boundedness witness `∃ M, ∀ x, |φ x| ≤ M`.
-/
theorem subq_I_1_a
    (f : ℝ → ℝ) (hf : Continuous f)
    (y : ℝ → ℝ) (hy_cont : Continuous y)
    (hy_bd : ∃ M : ℝ, ∀ x, |y x| ≤ M) :
    Continuous (f ∘ y) ∧ ∃ M : ℝ, ∀ x, |(f ∘ y) x| ≤ M := by
  sorry

/-! ### I.2.a — the integral operator `T_g`. -/

/--
**Book I.2.a (medium).**
"Soit $b \in \mathbb{R}^{+,*}$ et $g \in \mathcal{BC}^0(\mathbb{R}, \mathbb{R})$.
Montrer que la formule
$T_g(x) = e^{-bx} \int_{-\infty}^x e^{bs} g(s)\, ds$
permet de définir une fonction $T_g \in \mathcal{BC}^1(\mathbb{R}, \mathbb{R})$,
solution sur $\mathbb{R}$ d'une équation différentielle linéaire que l'on
écrira."

English: For `b > 0` and `g ∈ BC⁰`, the formula `T_g(x) = e^{-bx} ∫_{-∞}^x
e^{bs} g(s) ds` defines a `BC¹` function which solves the linear ODE
`y' + b y = g`.

Lean: improper integral `∫_{-∞}^x` is encoded via `IntegrableOn` on `Iic x`
plus the integral `∫ s in Set.Iic x, ...`.  We assert: `T_g` is `C¹`, both
`T_g` and `(T_g)'` are bounded, and `(T_g)' + b · T_g = g`.
-/
theorem subq_I_2_a
    (b : ℝ) (hb : 0 < b)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_bd : ∃ M : ℝ, ∀ x, |g x| ≤ M)
    (T : ℝ → ℝ)
    (hT : ∀ x, T x =
      Real.exp (-b * x) * ∫ s in Set.Iic x, Real.exp (b * s) * g s) :
    ContDiff ℝ 1 T ∧
      (∃ M : ℝ, ∀ x, |T x| + |deriv T x| ≤ M) ∧
      (∀ x, deriv T x + b * T x = g x) := by
  sorry

/-! ### I.3.c — continuous bijection of ℝ ⇔ homeomorphism. -/

/--
**Book I.3.c (easy).**
"Conclure : $f : \mathbb{R} \to \mathbb{R}$ est continue et bijective si et
seulement si $f$ est un homéomorphisme de $\mathbb{R}$ sur lui-même."

English: A map `f : ℝ → ℝ` is continuous and bijective iff it is a
homeomorphism of `ℝ` onto itself, i.e. iff `f` is continuous, bijective, and
its set-theoretic inverse is also continuous.

Lean: `Function.invFun f` is the (Mathlib) set-theoretic inverse; for `f`
bijective we have `Function.LeftInverse (Function.invFun f) f` and
`Function.RightInverse (Function.invFun f) f`.
-/
theorem subq_I_3_c
    (f : ℝ → ℝ) :
    (Continuous f ∧ Function.Bijective f) ↔
      (Continuous f ∧ ∃ g : ℝ → ℝ,
        Continuous g ∧ Function.LeftInverse g f ∧ Function.RightInverse g f) := by
  sorry

/-! ### II.2.b — linear case `a > 0`: unique bounded solution. -/

/--
**Book II.2.b (medium).**
"Démontrer que si $a > 0$ alors $(\mathcal{E}_L)\ y' + a y = h$ possède une et
une seule solution bornée sur $\mathbb{R}$."

English: For `a > 0` and `h ∈ BC⁰`, the linear ODE `y' + a y = h` admits
exactly one bounded `C¹` solution on `ℝ`.

Lean: the bounded solution exists (as `T_h(x) = e^{-ax} ∫_{-∞}^x e^{as} h(s) ds`
from I.2) and is unique among bounded `C¹` solutions.
-/
theorem subq_II_2_b
    (a : ℝ) (ha : 0 < a)
    (h : ℝ → ℝ) (hh_cont : Continuous h) (hh_bd : ∃ M, ∀ x, |h x| ≤ M) :
    ∃! y : ℝ → ℝ,
      ContDiff ℝ 1 y ∧
      (∃ M : ℝ, ∀ x, |y x| ≤ M) ∧
      (∀ x, deriv y x + a * y x = h x) := by
  sorry

/-! ### IV.1 — derivative characterisation of property `(H)`. -/

/--
**Book IV.1 (medium).**
"Dans cette question seulement, on suppose que $f$ est dérivable sur
$\mathbb{R}$ ; donner une condition nécessaire et suffisante pour que $f$
satisfasse la propriété $(H)$ : il existe $m, M > 0$ tels que pour tout
$(x, y) \in \mathbb{R}^2$ avec $x \neq y$,
$m \leq \dfrac{f(y) - f(x)}{y - x} \leq M$."

English: For `f : ℝ → ℝ` differentiable, property `(H)` (existence of
`m, M > 0` with `m ≤ (f(y) - f(x)) / (y - x) ≤ M` for all `x ≠ y`) is
equivalent to `f'` being bounded on ℝ between two positive constants
`m, M > 0`.

Lean: equivalence between the secant-slope two-sided bound and the
derivative two-sided bound (with the same constants `m, M`).
-/
theorem subq_IV_1
    (f : ℝ → ℝ) (hf_diff : Differentiable ℝ f) :
    (∃ m M : ℝ, 0 < m ∧ 0 < M ∧
        ∀ x y : ℝ, x ≠ y → m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M) ↔
      (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x : ℝ, m ≤ deriv f x ∧ deriv f x ≤ M) := by
  sorry

/-! ### IV.3 — `F_k = f - k·id` is Lipschitz with ratio `(M-m)/2`. -/

/--
**Book IV.3 (medium).**
"On pose $k = \dfrac{m + M}{2}$ et on introduit $F_k : x \mapsto f(x) - kx$.
Démontrer que $F_k$ est lipschitzienne d'un rapport $L$ que l'on déterminera."

English: For `f` satisfying property `(H)` with constants `m, M > 0`, set
`k = (m + M) / 2` and `F_k(x) = f(x) - k x`.  Then `F_k` is Lipschitz with
ratio `L = (M - m) / 2`.

Lean: we state the Lipschitz inequality directly, with `L = (M - m) / 2`.
The hypothesis on `f` is property `(H)` in secant-slope form.
-/
theorem subq_IV_3
    (f : ℝ → ℝ)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hH : ∀ x y : ℝ, x ≠ y →
      m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M)
    (k : ℝ) (hk : k = (m + M) / 2)
    (F : ℝ → ℝ) (hF : ∀ x, F x = f x - k * x) :
    ∀ x y : ℝ, |F y - F x| ≤ ((M - m) / 2) * |y - x| := by
  sorry

/-! ### IV.8 — Banach fixed-point: `L_f` is a bijection. -/

/--
**Book IV.8 (hard).**
"Soit $h \in \mathcal{BC}^0(\mathbb{R}, \mathbb{R})$. Démontrer que
$\varphi \mapsto G(h, \varphi)$ a un unique point fixe dans
$\mathcal{BC}^0(\mathbb{R}, \mathbb{R})$. En déduire que l'opérateur
$\mathcal{L}_f : \mathcal{BC}^1(\mathbb{R}, \mathbb{R}) \to
\mathcal{BC}^0(\mathbb{R}, \mathbb{R})$ est une bijection."

English: Under property `(H)`, for every `h ∈ BC⁰`, the map
`φ ↦ G(h, φ)(x) = e^{-kx} ∫_{-∞}^x e^{ks}(-F_k(φ(s)) + h(s)) ds` is a
contraction on `BC⁰` (with ratio `r = (M - m)/(M + m) < 1`); its unique
fixed point is the unique `BC¹` preimage of `h` under `L_f`.  Therefore
`L_f : BC¹ → BC⁰` is bijective.

Lean: we encode `BC¹` via `ContDiff ℝ 1` plus boundedness of `φ` and `deriv
φ`.  Surjectivity and injectivity are stated separately on the level of
`L_f φ = φ' + f ∘ φ`.
-/
theorem subq_IV_8
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hH : ∀ x y : ℝ, x ≠ y →
      m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M) :
    ∀ h : ℝ → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      ∃! φ : ℝ → ℝ,
        ContDiff ℝ 1 φ ∧
        (∃ C : ℝ, ∀ x, |φ x| + |deriv φ x| ≤ C) ∧
        (∀ x, deriv φ x + f (φ x) = h x) := by
  sorry

/-! ### V.1 — `f(x) = 2x + sin²(x)` satisfies property `(H)`. -/

/--
**Book V.1 (medium).**
"On considère l'équation $(\mathcal{F})\ \varphi' + (2\varphi + \sin^2(\varphi))
= h$ où $h \in \mathcal{BC}^0(\mathbb{R}, \mathbb{R})$. Vérifier que les
résultats de la partie IV s'appliquent (i.e. que $f(x) = 2x + \sin^2(x)$
satisfait la propriété $(H)$)."

English: The function `f(x) = 2x + sin²(x)` is differentiable on `ℝ` with
`f'(x) = 2 + sin(2x) = 2 + 2 sin(x) cos(x)`, satisfying `1 ≤ f'(x) ≤ 3`.
Hence by IV.1 (and the mean-value theorem) `f` satisfies property `(H)` with
`m = 1, M = 3`.

Lean: we assert directly the secant-slope two-sided bound with `m = 1`,
`M = 3`.
-/
theorem subq_V_1
    (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x + Real.sin x ^ 2) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ x y : ℝ, x ≠ y →
        m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M := by
  sorry

end

end AITP.P16Concrete
