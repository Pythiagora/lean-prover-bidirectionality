/-
  P17 — Concrete reformulation (Mercier–Rombaldi 2012, épreuve 2).

  The problem studies cluster values $V(u)$ of bounded sequences in a finite-
  dimensional real normed space $E$, slow-evolution sequences (Part I), iterates
  of the tent map $f(x) = 1 - |2x-1|$ on $[0,1]$ (Part II), the "force"
  $F(x,u) = \lim_{\varepsilon \to 0^+} \liminf_m H_m(x,u,\varepsilon)$ where
  $H_m$ is a frequency of $\varepsilon$-visits (Part III), and the algorithmic
  NVA construction (Part IV; not formalised — too combinatorial / sparse Mathlib
  coverage).

  Each theorem below takes all required data — sequences, scalars, the tent map
  $f$, etc. — as free variables, with defining equations / boundedness /
  continuity assumptions stated explicitly.  No `Setup` structure is used.

  Cross-reference (matching `P17_subquestions.json`):
    * subq_I_A_3_a   — I.A.3.a, $V(u)$ is closed
    * subq_I_A_4_b   — I.A.4.b, bounded sequence converges iff $V(u)$ singleton
    * subq_I_B_1     — I.B.1, convergent discrete sequence is eventually constant
    * subq_I_C_2_a   — I.C.2.a, the sequence $m_N = \inf T_N(u)$ converges
    * subq_I_D_2     — I.D.2, $V(u)$ disconnected ⇒ partition into two compacts
    * subq_II_2      — II.2, tent map preserves rationality
    * subq_II_4_a    — II.4.a, $f^n(x) = a_n x + b_n$ for some $a_n, b_n \in \mathbb{Z}$
    * subq_III_3     — III.3, $0 \leq F(x, u) \leq 1$
-/
import LeanCorpus.Common

namespace AITP.P17Concrete

noncomputable section

/-! ### I.A.3.a — `V(u)` is closed. -/

/--
**Book I.A.3.a (easy).**
"Vérifier que l'ensemble $V(u)$ est un fermé de $E$."

English: The set $V(u)$ of cluster values of a sequence $u$ is a closed subset
of $E$.

Lean note: $V(u)$ is rendered as the set of cluster points of `u` along
`atTop`, i.e. `{ℓ | MapClusterPt ℓ Filter.atTop u}`, which equals
`⋂_N closure (T_N(u))`.  Closedness is the simplest of the basic topological
properties of $V(u)$.
-/
theorem subq_I_A_3_a
    {d : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin d)) :
    IsClosed { ℓ : EuclideanSpace ℝ (Fin d) | MapClusterPt ℓ Filter.atTop u } := by
  sorry

/-! ### I.A.4.b — bounded sequence converges iff `V(u)` is a singleton. -/

/--
**Book I.A.4.b (medium).**
"En déduire qu'une suite bornée $u$ est convergente si et seulement si $V(u)$
est un singleton."

English: A bounded sequence $u$ in $E$ is convergent if and only if its set of
cluster values $V(u)$ is a singleton.

Lean note: convergence is `Filter.Tendsto u Filter.atTop (𝓝 ℓ)` for some `ℓ`;
$V(u) = \{ℓ\}$ is encoded as `{x | MapClusterPt x atTop u} = {ℓ}`.  Boundedness
of the range is essential: in finite dimension this gives Bolzano–Weierstrass.
-/
theorem subq_I_A_4_b
    {d : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin d))
    (hb : Bornology.IsBounded (Set.range u)) :
    (∃ ℓ : EuclideanSpace ℝ (Fin d), Filter.Tendsto u Filter.atTop (nhds ℓ)) ↔
      ∃ ℓ : EuclideanSpace ℝ (Fin d),
        { x : EuclideanSpace ℝ (Fin d) | MapClusterPt x Filter.atTop u } = {ℓ} := by
  sorry

/-! ### I.B.1 — discrete convergent sequence is eventually constant. -/

/--
**Book I.B.1 (easy).**
"Démontrer qu'une suite discrète convergente est stationnaire."

English: A convergent sequence whose image is a discrete subset of $E$ is
eventually constant.

Lean note: "discrete image" is rendered as the existence of a positive radius
`r` such that any two distinct values of the sequence are at distance ≥ `r`.
"Stationary from some rank" means there is `N` and `c` with `u n = c` for all
`n ≥ N` (here `c = ℓ`, the limit).
-/
theorem subq_I_B_1
    {d : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin d)) (ℓ : EuclideanSpace ℝ (Fin d))
    (hu : Filter.Tendsto u Filter.atTop (nhds ℓ))
    (hdisc : ∃ r : ℝ, 0 < r ∧
      ∀ m n : ℕ, u m ≠ u n → r ≤ ‖u m - u n‖) :
    ∃ N : ℕ, ∀ n ≥ N, u n = ℓ := by
  sorry

/-! ### I.C.2.a — convergence of `m_N = inf T_N(u)`. -/

/--
**Book I.C.2.a (easy).**
"Démontrer que la suite $(m_N)_{N \in \mathbb{N}}$ est convergente.  Sa limite
est appelée limite inférieure de la suite $(u_n)$ et notée $\liminf u_n$."

English: For a bounded real sequence $u$, the sequence $m_N = \inf_{n \geq N}
u_n$ is monotone non-decreasing and bounded above, hence convergent.  Its
limit is, by definition, $\liminf_{n \to +\infty} u_n$.

Lean note: we introduce `m : ℕ → ℝ` with `m N = sInf (T_N(u))` where
`T_N(u) = u '' {n | N ≤ n}`, and assert that `m` converges; we do **not**
identify the limit with Mathlib's `Filter.liminf`, which would be a separate
(true, but non-trivial) statement.
-/
theorem subq_I_C_2_a
    (u : ℕ → ℝ) (hb : Bornology.IsBounded (Set.range u))
    (m : ℕ → ℝ)
    (hm : ∀ N, m N = sInf (u '' {n | N ≤ n})) :
    ∃ L : ℝ, Filter.Tendsto m Filter.atTop (nhds L) := by
  sorry

/-! ### I.D.2 — disconnected `V(u)` partitions into two non-empty compacts. -/

/--
**Book I.D.2 (medium).**
"On suppose que $V(u)$ n'est pas connexe.  Démontrer qu'il existe deux compacts
non vides $K_1$ et $K_2$ vérifiant $K_1 \cap K_2 = \varnothing$ et
$K_1 \cup K_2 = V(u)$."

English: If the set $V(u)$ of cluster values of a bounded sequence $u$ is not
connected, then there exist two non-empty disjoint compact sets $K_1, K_2$
whose union is $V(u)$.

Lean note: the hypothesis "$u$ bounded" makes $V(u)$ compact (I.A.3.b), and a
disconnected compact set in a normed space splits into two non-empty disjoint
compact pieces.  We state this as a pure topology lemma about compact sets.
-/
theorem subq_I_D_2
    {d : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin d))
    (hb : Bornology.IsBounded (Set.range u))
    (hVnc :
      ¬ IsConnected
        { x : EuclideanSpace ℝ (Fin d) | MapClusterPt x Filter.atTop u }) :
    ∃ K₁ K₂ : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K₁ ∧ IsCompact K₂ ∧ K₁.Nonempty ∧ K₂.Nonempty ∧
        Disjoint K₁ K₂ ∧
        K₁ ∪ K₂ =
          { x : EuclideanSpace ℝ (Fin d) | MapClusterPt x Filter.atTop u } := by
  sorry

/-! ### II.2 — tent map preserves rationality on `[0,1]`. -/

/--
**Book II.2 (easy).**
"Soit $f : [0,1] \to [0,1]$ définie par $f(x) = 1 - |2x - 1|$.  Démontrer que,
pour tout $x \in [0,1]$, on a l'équivalence $x \in \mathbb{Q}
\Leftrightarrow f(x) \in \mathbb{Q}$."

English: For every $x \in [0, 1]$, the value $1 - |2x - 1|$ is rational if and
only if $x$ is rational.

Lean note: "$x \in \mathbb{Q}$" is rendered as `∃ q : ℚ, x = (q : ℝ)`; the tent
map is supplied as a free function `f : ℝ → ℝ` with the defining equation as
hypothesis (only its values on `[0,1]` matter).
-/
theorem subq_II_2
    (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - |2 * x - 1|)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∃ q : ℚ, x = (q : ℝ)) ↔ (∃ q : ℚ, f x = (q : ℝ)) := by
  sorry

/-! ### II.4.a — iterates of the tent map are affine with integer coefficients. -/

/--
**Book II.4.a (medium).**
"Soit $x \in [0,1]$.  Démontrer que pour tout entier naturel $n$, il existe
deux entiers relatifs $a_n$ et $b_n$ dépendant de $x$ vérifiant $f^n(x) =
a_n x + b_n$."

English: For every $x \in [0, 1]$ and every $n \in \mathbb{N}$, the iterate
$f^n(x)$ of the tent map $f(t) = 1 - |2t - 1|$ admits a representation
$f^n(x) = a_n \cdot x + b_n$ with $a_n, b_n \in \mathbb{Z}$ depending on $x$
and $n$.  (By convention $f^0 = \mathrm{id}$, so $a_0 = 1$, $b_0 = 0$.)

Lean note: the tent map is a free function `f : ℝ → ℝ` with its defining
equation as hypothesis; iterates use Mathlib's `Function.iterate`, written
`f^[n]`.  Both $a_n$ and $b_n$ are existentially quantified.
-/
theorem subq_II_4_a
    (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - |2 * x - 1|)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∃ a b : ℤ, f^[n] x = (a : ℝ) * x + (b : ℝ) := by
  sorry

/-! ### III.3 — bounds on the force `F(x, u)`. -/

/--
**Book III.3 (easy).**
"Démontrer que $0 \leq F(x, u) \leq 1$."

English: For every real sequence $u$ and every $x \in \mathbb{R}$, the force
$F(x, u) = \lim_{\varepsilon \to 0^+} H(x, u, \varepsilon)$, where
$H(x, u, \varepsilon) = \liminf_{m \to +\infty} H_m(x, u, \varepsilon)$ and
$H_m(x, u, \varepsilon) = \mathrm{card}\{n \in [\![0, m-1]\!] \mid |x - u_n| <
\varepsilon\} / m$, satisfies $0 \leq F(x, u) \leq 1$.

Lean note: we expose the building blocks of the definition.  `H_m` is a free
function with the defining equation as hypothesis; `H = liminf H_m`; `F` is
the right limit of `H` as `ε → 0^+`.  The conclusion is `F ∈ [0, 1]`.
-/
theorem subq_III_3
    (u : ℕ → ℝ) (x : ℝ)
    (Hm : ℕ → ℝ → ℝ)
    (hHm : ∀ m ε, 0 < m → 0 < ε →
      Hm m ε =
        ((Finset.range m).filter (fun n => |x - u n| < ε)).card / (m : ℝ))
    (H : ℝ → ℝ)
    (hH : ∀ ε, 0 < ε → H ε = Filter.liminf (fun m => Hm m ε) Filter.atTop)
    (F : ℝ)
    (hF : Filter.Tendsto H (nhdsWithin 0 (Set.Ioi 0)) (nhds F)) :
    0 ≤ F ∧ F ≤ 1 := by
  sorry

end

end AITP.P17Concrete
