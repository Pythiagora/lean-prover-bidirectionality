/-
Problem 3 — Pythagorean triples and Diophantine equations in the integer rings
$\mathbb{Z}$, $\mathbb{Z}[i]$, $\mathbb{Z}[i\sqrt{2}]$, $\mathbb{Z}[j]$
(Mercier–Rombaldi 2007, Annales de l'agrégation interne).

Concrete (fully self-contained) form: each theorem takes all required data as free
variables. No `Setup` structure is used — and indeed, the original `P3.lean` already
phrased every statement this way (Mathlib-native types: `ℤ`, `ℕ`, `ℝ`, `ℂ`,
`Zsqrtd`). This file is therefore a verbatim restatement under the namespace
`AITP.P3Concrete`, kept in sync with `P3.lean` so downstream tooling can target either
namespace uniformly.

Cross-reference (same as `P3.lean`):
* `subq_P3_I_1_a`     — I.1.a, half-angle parametrization + rationality preservation
* `subq_P3_I_2_b`     — I.2.b, pairwise coprimality of `2uv`, `u²+v²`, `u²-v²`
* `subq_P3_I_3_a`     — I.3.a, global vs. pairwise coprimality
* `subq_P3_II_1`      — II.1, $\mathbb{Z}[i\sqrt{2}]$ is a commutative integral subring
                          of $\mathbb{C}$
* `subq_P3_III_5`     — III.5, $x^4 - y^4 = z^2$ has no nonzero integer solution
* `subq_P3_IV_1_a`    — IV.1.a, parametric equations of the tangent to $C : x^3 - y^3 = 2$
* `subq_P3_IV_1_c`    — IV.1.c, inflection points of $C$ (stubbed; see notes)
* `subq_P3_IV_2`      — IV.2, integer points of $C$ in the band $0 \le x \le 4$
-/
import LeanCorpus.Common

namespace AITP.P3Concrete

/-! ### I.1.a — half-angle parametrization (easy) -/

/--
**Book I.1.a (easy).**
"Soit $M = (x, y)$ un point de $\mathbb{R}^2$ avec $x^2 + y^2 = 1$, $x \geq 0$, $y \geq 0$,
et $\theta \in [0, \pi/2]$ tel que $x = \cos\theta$, $y = \sin\theta$. On pose
$t = \tan(\theta/2)$. Exprimer $x$ et $y$ en fonction de $t$. En déduire que, si $t$ est un
nombre rationnel, $x$ et $y$ sont aussi des nombres rationnels."

English: For $\theta \in [0, \pi/2]$, with $x = \cos\theta$, $y = \sin\theta$ and
$t = \tan(\theta/2)$, we have $x = (1 - t^2)/(1 + t^2)$ and $y = 2t/(1 + t^2)$;
furthermore, if $t \in \mathbb{Q}$, then $x \in \mathbb{Q}$ and $y \in \mathbb{Q}$.
-/
theorem subq_P3_I_1_a (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    let t := Real.tan (θ / 2)
    Real.cos θ = (1 - t ^ 2) / (1 + t ^ 2)
      ∧ Real.sin θ = (2 * t) / (1 + t ^ 2)
      ∧ (∀ q : ℚ, t = (q : ℝ) →
          (∃ qx : ℚ, Real.cos θ = (qx : ℝ)) ∧ (∃ qy : ℚ, Real.sin θ = (qy : ℝ))) := by
  sorry


/-! ### I.2.b — pairwise coprimality, distinct parities case (medium) -/

/--
**Book I.2.b (medium).**
"Soient $u, v$ des entiers $> 0$, premiers entre eux. Supposons que $u$ et $v$ aient des
parités différentes. Démontrer que les nombres $2uv$, $u^2 + v^2$, $u^2 - v^2$ sont
premiers entre eux deux à deux."

English: For positive integers $u, v$ that are coprime and of distinct parities, the
three integers $2uv$, $u^2 + v^2$, $u^2 - v^2$ are pairwise coprime.

The book uses $u > v$ implicitly (so that $u^2 - v^2 > 0$); we keep $u, v$ generic
positive integers as in the énoncé.
-/
theorem subq_P3_I_2_b (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : Nat.Coprime u v) (hpar : u % 2 ≠ v % 2) :
    Nat.Coprime (2 * u * v) (u ^ 2 + v ^ 2)
      ∧ Nat.Coprime (2 * u * v) (u ^ 2 - v ^ 2)
      ∧ Nat.Coprime (u ^ 2 + v ^ 2) (u ^ 2 - v ^ 2) := by
  sorry


/-! ### I.3.a — global versus pairwise coprimality (easy) -/

/--
**Book I.3.a (easy).**
"Soient $a, b, c$ des entiers $> 0$ avec $a^2 + b^2 = c^2$. Démontrer que si les nombres
$a, b, c$ sont premiers entre eux dans leur ensemble, ils sont premiers entre eux deux
à deux."

English: For positive integers $a, b, c$ with $a^2 + b^2 = c^2$, if $\gcd(a, b, c) = 1$,
then $a, b, c$ are pairwise coprime.
-/
theorem subq_P3_I_3_a (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2) (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := by
  sorry


/-! ### II.1 — $\mathbb{Z}[i\sqrt{2}]$ is a commutative integral subring of $\mathbb{C}$ (easy) -/

/--
**Book II.1 (easy).**
"Démontrer que $\mathbb{Z}[i\sqrt{2}]$ est un sous-anneau de $\mathbb{C}$, commutatif et
intègre."

English: $\mathbb{Z}[i\sqrt{2}]$ is a commutative integral subring of $\mathbb{C}$.

Lean rendering: we use Mathlib's `Zsqrtd (-2)` (with `re + im * √(-2) = re + im * i√2`),
state that it is a commutative integral domain, and produce the corresponding subring of
$\mathbb{C}$ as the image of an injective ring homomorphism. The book's original phrasing
(set of complex numbers $a + ib\sqrt{2}$) is faithfully captured because `Zsqrtd (-2)` is
isomorphic to $\mathbb{Z}[i\sqrt{2}] \subseteq \mathbb{C}$ via the obvious map.
-/
theorem subq_P3_II_1 :
    -- `Zsqrtd (-2)` is a commutative ring and an integral domain
    (∀ x y : Zsqrtd (-2 : ℤ), x * y = y * x)
      ∧ (∀ x y : Zsqrtd (-2 : ℤ), x * y = 0 → x = 0 ∨ y = 0)
      -- and it embeds into `ℂ` as a subring (image is a subring of `ℂ`)
      ∧ ∃ φ : Zsqrtd (-2 : ℤ) →+* ℂ, Function.Injective φ := by
  sorry


/-! ### III.5 — $x^4 - y^4 = z^2$ has no nonzero integer solution (hard) -/

/--
**Book III.5 (hard).**
"Démontrer que l'équation $x^4 - y^4 = z^2$ n'a pas de solution en nombres entiers tous
$\neq 0$."

English: There is no triple $(x, y, z)$ of nonzero integers satisfying $x^4 - y^4 = z^2$.
-/
theorem subq_P3_III_5 :
    ¬ ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 - y ^ 4 = z ^ 2 := by
  sorry


/-! ### IV.1.a — parametric equations of the tangent to $C : x^3 - y^3 = 2$ (easy) -/

/--
**Book IV.1.a (easy).**
"Soit $M_0 = (x_0, y_0)$ un point de $C$. Écrire des équations paramétriques de la
tangente $T_0$ à $C$ au point $M_0$."

English: For $M_0 = (x_0, y_0) \in C$ (i.e. $x_0^3 - y_0^3 = 2$), the parametric
equations of the tangent line $T_0$ at $M_0$ may be taken as
$x(t) = x_0 + y_0^2 \, t$, $y(t) = y_0 + x_0^2 \, t$.

Faithful rendering: the curve $C = \{(x,y) \mid x^3 - y^3 = 2\}$ is the zero set of
$F(x, y) = x^3 - y^3 - 2$; its gradient at $M_0$ is $(3 x_0^2, -3 y_0^2)$.
The tangent line at $M_0$ is the affine line through $M_0$ orthogonal to the gradient,
i.e. with direction $(y_0^2, x_0^2)$. We assert exactly this.
-/
theorem subq_P3_IV_1_a (x₀ y₀ : ℝ) (hM : x₀ ^ 3 - y₀ ^ 3 = 2) :
    -- the parametric line `t ↦ (x₀ + y₀² t, y₀ + x₀² t)` passes through `M₀` at `t = 0`
    (((x₀ + y₀ ^ 2 * (0 : ℝ)), (y₀ + x₀ ^ 2 * (0 : ℝ))) = (x₀, y₀))
      -- and its direction `(y₀², x₀²)` lies in the kernel of the gradient of `F`
      -- at `M₀`, i.e., `3 x₀² · y₀² + (-3 y₀²) · x₀² = 0`.
      ∧ 3 * x₀ ^ 2 * y₀ ^ 2 + (-3 * y₀ ^ 2) * x₀ ^ 2 = 0 := by
  sorry


/-! ### IV.1.c — inflection points of $C$ (medium, **stubbed**) -/

/--
**Book IV.1.c (medium).** "Déterminer les points d'inflexion de la courbe $C$."

English: Determine the inflection points of the curve $C : x^3 - y^3 = 2$.

**Stubbed.** This is a "determine" question with a constructive answer (compute $f''$ for
$y = \pm (x^3 - 2)^{1/3}$, locate zeros). Mathlib does not provide a ready-made notion of
"inflection point of an implicit planar curve", and faithfully formalising the énoncé
would require building an ad hoc definition of inflection point of a graph and computing
its zeros. Per the spec ("If a sub-question requires an exotic Mathlib API not present"),
we leave a `True` placeholder.
-/
theorem subq_P3_IV_1_c : True := trivial


/-! ### IV.2 — integer points of $C$ in the band $0 \le x \le 4$ (easy) -/

/--
**Book IV.2 (easy).**
"Déterminer les points à coordonnées entières de $C$ situés dans la bande
$0 \leq x \leq 4$."

English: Determine the integer-coordinate points of $C : x^3 - y^3 = 2$ in the band
$0 \leq x \leq 4$.

The unique answer is $(1, -1)$: indeed for $x \in \{0, 1, 2, 3, 4\}$, $x^3 - 2 \in
\{-2, -1, 6, 25, 62\}$, and only $-1$ is a perfect cube ($-1 = (-1)^3$).

The JSON note "$(3, \pm 5)$" in `selected_corpus.json` is incorrect: $3^3 - 5^3 = -98 \ne
2$ and $3^3 - (-5)^3 = 152 \ne 2$. The unique solution in this band is $(1, -1)$.
-/
theorem subq_P3_IV_2 (x y : ℤ) (hx_lo : 0 ≤ x) (hx_hi : x ≤ 4) :
    x ^ 3 - y ^ 3 = 2 ↔ x = 1 ∧ y = -1 := by
  sorry

end AITP.P3Concrete
