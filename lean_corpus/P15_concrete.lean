/-
Problem 15 — Guichard equation $f(z+1) - f(z) = g(z)$ on polynomials and
entire functions; Bernoulli polynomials, contour integrals, Baire on Banach
(Mercier–Rombaldi 2010, épreuve 2).

Concrete (fully self-contained) form: each theorem takes all required data
as free variables. No `Setup` structure. The discrete difference operator
$\Delta P(z) = P(z+1) - P(z)$ is supplied inline as a free function
together with its defining equation `hΔ`.

For Bernoulli polynomials we use Mathlib's `Polynomial.bernoulli n : ℚ[X]`
(see `Mathlib/NumberTheory/BernoulliPolynomials.lean`), which matches the
book convention $B_0 = 1$, $B_1 = X - 1/2$, etc.

Selected sub-questions (8 of 50 formalizable):
* `subq_I_1_a`     — I.1.(a),  Δ : 𝒫 → 𝒫 is locally nilpotent (easy).
* `subq_I_2`       — I.2,      ker Δ = constants on 𝒫 (easy).
* `subq_I_4_a`     — I.4.(a),  $\sum_{n=0}^{N} n^p = f(N+1)$ (easy).
* `subq_I_5_a`     — I.5.(a),  sup norm on $[0,1]$ is a norm on 𝒫 (easy).
* `subq_I_6_a`     — I.6.(a),  vector subspace with non-empty interior is
                                everything (medium, Baire-on-Banach core).
* `subq_II_1_b`    — II.1.(b), Cauchy bound $|a_n| \le M(f,r)/r^n$ (easy).
* `subq_II_5_a`    — II.5.(a), $|I| \le 2\pi\rho M(f,\rho)$ (easy).
* `subq_III_A_3_a` — III.A.3.(a), $\int_0^1 B_n(t)\,dt = 0$ for $n \ge 1$
                                  (easy, uses `Polynomial.bernoulli`).
-/
import LeanCorpus.Common

namespace AITP.P15Concrete

noncomputable section

/-! ### I.1.(a) — Δ is locally nilpotent on `Polynomial ℂ` (easy). -/

/--
**Book I.1.(a) (easy).**
"Démontrer que $\Delta : \mathcal{P} \to \mathcal{P}$ est une application linéaire
localement nilpotente, c'est-à-dire (en notant $\Delta^n = \Delta \circ \cdots \circ \Delta$
($n$ fois) et $\Delta^0 = Id$) : $\forall P \in \mathcal{P}, \ \exists n \in \mathbb{N}$
tel que $\Delta^n P = 0$."

English: The discrete difference operator $\Delta P(z) = P(z+1) - P(z)$ on the space
of polynomials with complex coefficients is a (locally) nilpotent linear endomorphism:
for every $P$ there exists $n$ with $\Delta^n P = 0$.

Lean note: $\Delta$ is supplied as a free linear-on-polynomials function via the
hypothesis `hΔ` recording its action on every polynomial. We prove pointwise
nilpotency: there exists `n` such that iterated application yields the zero
polynomial.
-/
theorem subq_I_1_a
    (Δ : Polynomial ℂ → Polynomial ℂ)
    (hΔ : ∀ P : Polynomial ℂ, Δ P = P.comp (Polynomial.X + Polynomial.C 1) - P)
    (P : Polynomial ℂ) :
    ∃ n : ℕ, (Δ^[n]) P = 0 := by
  sorry

/-! ### I.2 — kernel of Δ on `Polynomial ℂ` is the constants (easy). -/

/--
**Book I.2 (easy).**
"Démontrer que $\Delta : \mathcal{P} \to \mathcal{P}$ n'est pas injective et décrire
son noyau."

English: $\Delta : \mathcal{P} \to \mathcal{P}$ is not injective; its kernel is
exactly the subspace of constant polynomials. We package this as: for every
polynomial $P$, $\Delta P = 0$ iff $P$ is a constant polynomial (i.e. there exists
$c \in \mathbb{C}$ with $P = C\,c$). Non-injectivity follows since $\Delta(C 1) = 0$
and $C 1 \neq 0$.
-/
theorem subq_I_2
    (Δ : Polynomial ℂ → Polynomial ℂ)
    (hΔ : ∀ P : Polynomial ℂ, Δ P = P.comp (Polynomial.X + Polynomial.C 1) - P) :
    (∀ P : Polynomial ℂ, Δ P = 0 ↔ ∃ c : ℂ, P = Polynomial.C c)
      ∧ ¬ Function.Injective Δ := by
  sorry

/-! ### I.4.(a) — power-sum formula via solution of the Guichard equation. -/

/--
**Book I.4.(a) (easy).**
"Soit $p$ un entier fixé ; on écrit $z^p = f(z+1) - f(z)$ avec $f \in \mathcal{P}$ et
$f(0) = 0$. Démontrer que : $\forall N \in \mathbb{N}, \ \sum_{n=0}^{N} n^p = f(N+1)$."

English: Fix $p \in \mathbb{N}$ and let $f$ be a polynomial in $\mathcal{P}$ with
$f(0) = 0$ solving the discrete equation $f(z+1) - f(z) = z^p$. Then for every
natural number $N$, $\sum_{n=0}^{N} n^p = f(N+1)$.

Lean note: the Guichard equation is supplied as a hypothesis on the
evaluation of `f` at every complex point.
-/
theorem subq_I_4_a
    (p : ℕ) (f : Polynomial ℂ) (hf0 : f.eval 0 = 0)
    (hf_eq : ∀ z : ℂ, f.eval (z + 1) - f.eval z = z ^ p) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ((n : ℂ) ^ p) = f.eval ((N : ℂ) + 1) := by
  sorry

/-! ### I.5.(a) — sup-on-`[0,1]` is a norm on `Polynomial ℂ` (easy). -/

/--
**Book I.5.(a) (easy).**
"Pour $P \in \mathcal{P}$, on pose $\|P\| = \displaystyle\sup_{x \in [0,1]} |P(x)|$.
Démontrer que l'on définit ainsi une norme sur $\mathcal{P}$."

English: For $P \in \mathcal{P}$, the quantity $N(P) = \sup_{x \in [0,1]} |P(x)|$
defines a norm on $\mathcal{P}$. We prove the four norm axioms (non-negativity,
zero iff $P = 0$, absolute homogeneity, and triangle inequality), where the
supremum is taken over the real interval $[0,1]$ via `iSup` over the subtype.

Lean note: we use `‖P.eval (x : ℂ)‖` for the absolute value, restrict $x$ to the
real interval $[0,1]$ via the subtype `Set.Icc (0 : ℝ) 1`, and form the
supremum in `ℝ` (this supremum exists since the function is bounded on the
compact $[0,1]$).
-/
theorem subq_I_5_a :
    let N : Polynomial ℂ → ℝ := fun P =>
      ⨆ x : Set.Icc (0 : ℝ) 1, ‖P.eval ((x.1 : ℂ))‖
    (∀ P : Polynomial ℂ, 0 ≤ N P)
      ∧ (∀ P : Polynomial ℂ, N P = 0 ↔ P = 0)
      ∧ (∀ (c : ℂ) (P : Polynomial ℂ), N (Polynomial.C c * P) = ‖c‖ * N P)
      ∧ (∀ P Q : Polynomial ℂ, N (P + Q) ≤ N P + N Q) := by
  sorry

/-! ### I.6.(a) — vector subspace of a Banach with non-empty interior is everything. -/

/--
**Book I.6.(a) (medium).**
"Soit $Y$ un sous-espace vectoriel de $X$ ; montrer que $\mathring{Y} \neq \emptyset
\Rightarrow Y = X$."

English: Let $X$ be a complex Banach space and $Y$ a (complex) vector subspace of
$X$. If the interior of $Y$ is non-empty, then $Y = X$.

Lean note: $X$ is realized as a normed space over `ℂ` that is also a complete
metric space; $Y$ is a `Submodule ℂ X`; "non-empty interior" is `(interior
(Y : Set X)).Nonempty`; "Y = X" is `(Y : Set X) = Set.univ`.
-/
theorem subq_I_6_a
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Y : Submodule ℂ X)
    (hY : (interior (Y : Set X)).Nonempty) :
    (Y : Set X) = Set.univ := by
  sorry

/-! ### II.1.(b) — Cauchy bound on the coefficients of an entire function. -/

/--
**Book II.1.(b) (easy).**
"On pose $M(f, r) = \displaystyle\sup_{|z|=r} |f(z)|$. Démontrer que :
$\forall r > 0, \ \forall n \in \mathbb{N}, \ |a_n| \leq \frac{M(f,r)}{r^n}$."

English: Let $f \in \mathcal{E}$ be an entire function with power-series
expansion $f(z) = \sum_{n} a_n z^n$ valid on all of $\mathbb{C}$, and let
$M(f,r) = \sup_{|z|=r} |f(z)|$. Then for every $r > 0$ and every $n \in \mathbb{N}$,
$|a_n| \le M(f,r) / r^n$ (Cauchy estimate).

Lean note: $f$ is supplied as `Differentiable ℂ f` together with the power-series
identity `hf_series`. The sup over the circle of radius `r` is `⨆ z ∈ sphere 0 r, ‖f z‖`
(the sphere is compact so this iSup exists in `ℝ`).
-/
theorem subq_II_1_b
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℕ → ℂ)
    (hf_series : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z))
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ‖a n‖ ≤ (⨆ z : Metric.sphere (0 : ℂ) r, ‖f z.1‖) / r ^ n := by
  sorry

/-! ### II.5.(a) — coarse contour-integral bound on a circle. -/

/--
**Book II.5.(a) (easy).**
"On rappelle que pour $\rho > 0$ et $f$ définie et continue sur le cercle de centre
$0$ et de rayon $\rho$, l'intégrale curviligne
$I = \int_{|w|=\rho} f(w) dw = \int_0^{2\pi} f(\rho e^{it}) i \rho e^{it} dt$.
Démontrer que $|I| \leq 2\pi \rho M(f, \rho)$."

English: For $\rho > 0$ and $f : \mathbb{C} \to \mathbb{C}$ continuous on the
circle $\{|w| = \rho\}$, the contour integral $I = \oint_{|w|=\rho} f(w)\,dw$
satisfies $|I| \le 2\pi\,\rho\,M(f,\rho)$ where $M(f,\rho) = \sup_{|z|=\rho} |f(z)|$.

Lean note: we use Mathlib's `circleIntegral` (in `Mathlib/MeasureTheory/Integral
/CircleIntegral.lean`). Continuity of `f` on the sphere ensures the iSup is
attained and bounds `‖f z‖` for `z ∈ sphere 0 ρ`.
-/
theorem subq_II_5_a
    (f : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf_cont : ContinuousOn f (Metric.sphere (0 : ℂ) ρ)) :
    ‖circleIntegral f 0 ρ‖
      ≤ 2 * Real.pi * ρ * (⨆ z : Metric.sphere (0 : ℂ) ρ, ‖f z.1‖) := by
  sorry

/-! ### III.A.3.(a) — vanishing integral of `B_n` on `[0,1]` for `n ≥ 1`. -/

/--
**Book III.A.3.(a) (easy).**
"Démontrer que : $\forall n \geq 1, \ \int_0^1 B_n(t) dt = 0$."

English: For every integer $n \ge 1$, $\int_0^1 B_n(t)\,dt = 0$, where $B_n$ is
the $n$-th Bernoulli polynomial as defined in §III.A
(via $B_n(z) = \frac{n!}{2i\pi}\oint_{|w|=1} \frac{e^{zw}}{e^w - 1} \frac{dw}{w^n}$).

Lean note: we use Mathlib's `Polynomial.bernoulli n : ℚ[X]` (in
`Mathlib/NumberTheory/BernoulliPolynomials.lean`), pushed to a real-coefficient
polynomial via `Polynomial.map (algebraMap ℚ ℝ)` so that we can evaluate at
real points and take a real interval integral.
-/
theorem subq_III_A_3_a (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1,
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval t = 0 := by
  sorry

end

end AITP.P15Concrete
