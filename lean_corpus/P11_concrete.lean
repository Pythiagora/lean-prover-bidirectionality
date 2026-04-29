/-
  P11_concrete — concrete (unrolled) reformulation of selected sub-questions
  from Problem 11 (Mercier–Rombaldi 2006, épreuve 2).

  The chapter studies non-linear ODEs $x' = f(t, x)$, with techniques based on
  barriers, funnels and anti-funnels, and applications to existence of
  periodic solutions.  Each theorem here takes all required data as *free*
  variables: no `Setup` structure is used and no `def`/`structure`/`class`
  declarations appear.  Definitions of `(E)`, `f`, etc. are inlined as
  hypotheses on the data.

  Selected sub-questions (mix of difficulty, biased towards I.* and II.*):
    * subq_I_1        — I.1 (easy):    rewrite the system as $x' = f(t,x)$
    * subq_I_3_a      — I.3.a (easy):  conserved quantity for $q > 0$
    * subq_I_3_b      — I.3.b (easy):  the constant $p$ is nonnegative
    * subq_II_1       — II.1 (easy):   $h(a)=0$ and $h' \le K h$ ⇒ $h \le 0$
    * subq_II_3_a     — II.3.a (easy): $\alpha(t)=1/(\lambda-t)$ is a lower
                                        barrier of $x'=x^2+\sin^2(tx)$
    * subq_III_1      — III.1 (easy):  bounded derivative ⇒ finite limit
                                        at the right endpoint
    * subq_III_5_a    — III.5.a (easy): time-reversal change of variables
    * subq_IV_2_a     — IV.2.a (easy):  $T$-periodic time-shift of solutions

  Theorems are stated; proofs are `sorry`. The point is type-checking.
-/
import LeanCorpus.Common

namespace AITP.P11Concrete

noncomputable section

/-! ### I.1 — rewriting the planar system as $x' = f(t,x)$. -/

/--
**Book I.1 (easy).**
"Démontrer que $u$ est solution d'une équation différentielle du type $(E)$
en précisant bien quelle est l'application $f$."

English: For $u : \mathbb{R} \to \mathbb{R}^2$ differentiable with
$u_1' = u_2$ and $u_2' = -u_1 - q u_1^3$, $u$ is a solution of $(E)$
with $f : \mathbb{R} \times \mathbb{R}^2 \to \mathbb{R}^2$ given by
$f(t, (x_1, x_2)) = (x_2, -x_1 - q x_1^3)$.

Lean encoding: $u$ is given as a pair of components $u_1, u_2 : \mathbb{R}
\to \mathbb{R}$, each differentiable, with the prescribed derivative
relations.  The conclusion asserts the explicit derivative identity:
$(u_1'(t), u_2'(t)) = f(t, (u_1(t), u_2(t)))$.
-/
theorem subq_I_1
    (q : ℝ) (hq : 0 ≤ q)
    (u₁ u₂ : ℝ → ℝ)
    (hu₁ : ∀ t, HasDerivAt u₁ (u₂ t) t)
    (hu₂ : ∀ t, HasDerivAt u₂ (-u₁ t - q * (u₁ t) ^ 3) t) :
    let f : ℝ → ℝ × ℝ → ℝ × ℝ :=
      fun _ x => (x.2, -x.1 - q * x.1 ^ 3)
    ∀ t : ℝ,
      HasDerivAt (fun s => (u₁ s, u₂ s)) (f t (u₁ t, u₂ t)) t := by
  sorry

/-! ### I.3.a — conserved quantity for $q > 0$. -/

/--
**Book I.3.a (easy).**
"Supposons $q > 0$. Démontrer qu'il existe un réel $p$ tel que l'image
de $u$ soit incluse dans la courbe
$C_p = \{(x_1, x_2) \mid x_1^2 + (q/2) x_1^4 + x_2^2 = p\}$."

English: For $q > 0$ and $u = (u_1, u_2)$ solving the system of I.1,
there exists $p \in \mathbb{R}$ such that $u_1(t)^2 + (q/2) u_1(t)^4
+ u_2(t)^2 = p$ for all $t$.

Lean encoding: existence of a constant value `p` matched by the
explicit polynomial expression at every `t`.
-/
theorem subq_I_3_a
    (q : ℝ) (hq : 0 < q)
    (u₁ u₂ : ℝ → ℝ)
    (hu₁ : ∀ t, HasDerivAt u₁ (u₂ t) t)
    (hu₂ : ∀ t, HasDerivAt u₂ (-u₁ t - q * (u₁ t) ^ 3) t) :
    ∃ p : ℝ, ∀ t : ℝ,
      (u₁ t) ^ 2 + (q / 2) * (u₁ t) ^ 4 + (u₂ t) ^ 2 = p := by
  sorry

/-! ### I.3.b — the constant $p$ is nonnegative. -/

/--
**Book I.3.b (easy).**
"Démontrer que $p \ge 0$. Que dire si $p = 0$ ?"

English: For $q > 0$, the constant `p` of I.3.a satisfies $p \ge 0$,
and if $p = 0$ then $u$ is identically zero.

Lean encoding: assume the conserved-quantity identity holds with
some `p`; conclude $0 \le p$ and the case $p = 0$ implies
$u_1 \equiv 0$ and $u_2 \equiv 0$.
-/
theorem subq_I_3_b
    (q : ℝ) (hq : 0 < q)
    (u₁ u₂ : ℝ → ℝ)
    (p : ℝ)
    (hp : ∀ t : ℝ,
      (u₁ t) ^ 2 + (q / 2) * (u₁ t) ^ 4 + (u₂ t) ^ 2 = p) :
    0 ≤ p ∧ (p = 0 → ∀ t : ℝ, u₁ t = 0 ∧ u₂ t = 0) := by
  sorry

/-! ### II.1 — Grönwall-style lemma. -/

/--
**Book II.1 (easy).**
"Soient $a, b, K$ des nombres réels avec $a < b$, et $h : [a, b] \to
\mathbb{R}$ une fonction dérivable satisfaisant $h(a) = 0$ et
$h' \le K h$. Démontrer que $h \le 0$."

English: If $h : [a, b] \to \mathbb{R}$ is differentiable on $[a, b]$,
with $h(a) = 0$ and $h'(t) \le K \cdot h(t)$ on $[a, b]$, then
$h(t) \le 0$ for all $t \in [a, b]$.

Lean encoding: differentiability on the closed interval is captured
via `HasDerivAt h (h' t) t` for every `t ∈ [a, b]`, with `h' : ℝ → ℝ`
the (free-variable) derivative.
-/
theorem subq_II_1
    (a b K : ℝ) (hab : a < b)
    (h : ℝ → ℝ) (h' : ℝ → ℝ)
    (h_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt h (h' t) t)
    (h_init : h a = 0)
    (h_ineq : ∀ t ∈ Set.Icc a b, h' t ≤ K * h t) :
    ∀ t ∈ Set.Icc a b, h t ≤ 0 := by
  sorry

/-! ### II.3.a — explicit lower barrier for $x' = x^2 + \sin^2(tx)$. -/

/--
**Book II.3.a (easy).**
"Prenons $U = \mathbb{R}^2$ et $f(t, x) = x^2 + \sin^2(tx)$. Vérifier
que, pour $\lambda \in \mathbb{R}$, l'application $\alpha$ de
$]-\infty, \lambda[$ dans $\mathbb{R}$ définie par $\alpha(t) =
1/(\lambda - t)$ est une barrière inférieure de $(E)$."

English: For $\lambda \in \mathbb{R}$ and
$\alpha : (-\infty, \lambda) \to \mathbb{R}$, $\alpha(t) =
1/(\lambda - t)$, $\alpha$ is differentiable with
$\alpha'(t) = 1/(\lambda - t)^2$, and
$\alpha'(t) \le f(t, \alpha(t))$ where $f(t, x) = x^2 + \sin^2(tx)$.

Lean encoding: the lower-barrier inequality is split as a `HasDerivAt`
claim (computing $\alpha'$) and the inequality
$1/(\lambda - t)^2 \le (1/(\lambda - t))^2 + \sin^2(t/(\lambda - t))$,
which holds because the right-hand side equals the left plus a
nonnegative $\sin^2$ term.
-/
theorem subq_II_3_a
    (lam : ℝ) (t : ℝ) (ht : t < lam) :
    let α : ℝ → ℝ := fun s => 1 / (lam - s)
    let f : ℝ → ℝ → ℝ := fun s x => x ^ 2 + Real.sin (s * x) ^ 2
    HasDerivAt α (1 / (lam - t) ^ 2) t ∧
      (1 / (lam - t) ^ 2) ≤ f t (α t) := by
  sorry

/-! ### III.1 — bounded derivative ⇒ finite limit at right endpoint. -/

/--
**Book III.1 (easy).**
"Soient $p < q$ et $g : ]p, q[ \to \mathbb{R}$ une fonction dérivable
dont la dérivée est bornée. Démontrer que $g$ admet une limite finie
en $q$."

English: A differentiable function $g : (p, q) \to \mathbb{R}$ with
bounded derivative admits a finite limit at $q$.

Lean encoding: $g$ is differentiable at every point of the open
interval (via `HasDerivAt`), and `g' : ℝ → ℝ` denotes its derivative;
boundedness is `|g'(t)| ≤ M`; the conclusion uses
`Filter.Tendsto … (𝓝[<] q) (𝓝 ℓ)` for some real limit $\ell$.
-/
theorem subq_III_1
    (p q : ℝ) (hpq : p < q)
    (g : ℝ → ℝ) (g' : ℝ → ℝ)
    (g_deriv : ∀ t ∈ Set.Ioo p q, HasDerivAt g (g' t) t)
    (M : ℝ) (g'_bdd : ∀ t ∈ Set.Ioo p q, |g' t| ≤ M) :
    ∃ ℓ : ℝ, Filter.Tendsto g (nhdsWithin q (Set.Iio q)) (nhds ℓ) := by
  sorry

/-! ### III.5.a — time-reversal change of variables. -/

/--
**Book III.5.a (easy).**
"Soit $\widehat{u}(\tau) = u(-\tau)$ ; montrer que $u$ est solution
de $(E)$ sur $J$ ssi $\widehat{u}$ est solution sur $\widehat{J} = -J$
de $x'(\tau) = \widehat{f}(\tau, x)$ avec $\widehat{f}(\tau, x) =
-f(-\tau, x)$."

English: $u : \mathbb{R} \to \mathbb{R}$ satisfies $u'(t) = f(t, u(t))$
for all $t$ iff the time-reversed function $\widehat{u}(\tau) = u(-\tau)$
satisfies $\widehat{u}'(\tau) = -f(-\tau, \widehat{u}(\tau))$ for all
$\tau$.

Lean encoding: we restrict to globally-defined solutions ($J = \mathbb{R}$)
to avoid encoding the change-of-interval $\widehat{J} = -J$.
The biconditional links the two `HasDerivAt`-statements.
-/
theorem subq_III_5_a
    (f : ℝ → ℝ → ℝ) (u : ℝ → ℝ) :
    (∀ t : ℝ, HasDerivAt u (f t (u t)) t) ↔
      (∀ τ : ℝ, HasDerivAt (fun s => u (-s))
        (-f (-τ) (u (-τ))) τ) := by
  sorry

/-! ### IV.2.a — $T$-periodic time-shift of solutions. -/

/--
**Book IV.2.a (easy).**
"Soit $u : J \to \,]c, d[$ une solution maximale de $(E)$ avec $f$
$T$-périodique en $t$. Démontrer que $v(\tau) = u(\tau + T)$ définie
sur $J_T = J - T$ est encore une solution maximale de $(E)$."

English: If $f(t + T, x) = f(t, x)$ for all $t, x$, and
$u : \mathbb{R} \to \mathbb{R}$ satisfies $u'(t) = f(t, u(t))$ for
all $t$, then $v(\tau) := u(\tau + T)$ also satisfies
$v'(\tau) = f(\tau, v(\tau))$ for all $\tau$.

Lean encoding: we restrict to globally-defined solutions to avoid
encoding the maximal interval shift $J_T = J - T$; maximality is
preserved automatically when the domain is all of $\mathbb{R}$.
The $T$-periodicity in $t$ is the hypothesis
$\forall t x, f (t + T) x = f t x$.
-/
theorem subq_IV_2_a
    (T : ℝ) (f : ℝ → ℝ → ℝ)
    (f_periodic : ∀ t x : ℝ, f (t + T) x = f t x)
    (u : ℝ → ℝ)
    (hu : ∀ t : ℝ, HasDerivAt u (f t (u t)) t) :
    ∀ τ : ℝ,
      HasDerivAt (fun s => u (s + T))
        (f τ (u (τ + T))) τ := by
  sorry

end

end AITP.P11Concrete
