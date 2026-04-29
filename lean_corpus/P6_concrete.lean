import LeanCorpus.Common

/-!
# Problem 6 (Mercier–Rombaldi 2010) — Concrete (helper-inlined) version

This is a reformulation of `LeanCorpus.P6` in which every custom helper used in a
theorem signature is either inlined directly into the statement or replaced by an
explicit hypothesis. The original `P6.lean` relied on:

* `shift : Module.End K (ℕ → E)` — replaced by an explicit shift endomorphism
  `shiftEnd : Module.End K (ℕ → E)` constructed inline.
* `Ann u : Submodule K K[X]` — replaced by the predicate `(Polynomial.aeval shiftEnd P) u = 0`.
* `IsLinearRecurrent K u` — replaced by an existential at the head of each statement.
* `hankel u m`, `hankelDet u m` — replaced by the explicit
  `Matrix.of (fun (i j : Fin (m+1)) => u (i.val + j.val))` and its determinant.
* `phiBilin F hF m hm hdeg` — replaced by the explicit value
  `((P * Q) %ₘ F).coeff (m - 1)`.

The `fib` recursive definition is kept as a top-level `def` since recursive
definitions cannot be cleanly inlined as `let`. Goedel can see its body because
the file is self-contained.
-/

namespace AITP.P6Concrete

open Polynomial Module

universe u v

/-- Suite de Fibonacci usuelle (`u_0 = 0`, `u_1 = 1`, `u_{n+2} = u_{n+1} + u_n`).
Kept as a top-level `def` because recursive definitions cannot be inlined as `let`. -/
def fib : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-! ## I.1 — Calcul de `[P(σ)(u)]_n` -/

/-- **Sous-question I.1.** Pour `u : ℕ → E` et `P = ∑ k, p_k X^k ∈ K[X]`,
on a `[P(σ)(u)]_n = ∑ k, p_k · u_{n+k}`, où `σ` est le décalage `σ(u)_n = u_{n+1}`. -/
theorem subq_I_1 {K : Type u} [Field K] {E : Type v} [AddCommGroup E] [Module K E]
    (u : ℕ → E) (P : K[X]) (n : ℕ) :
    let shiftEnd : Module.End K (ℕ → E) :=
      { toFun := fun u => fun n => u (n + 1),
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
    (Polynomial.aeval shiftEnd P) u n =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • u (n + k) := by
  sorry

/-! ## I.2.a — Récurrence linéaire ⇔ annulateur non trivial -/

/-- **Sous-question I.2.a.** Une suite est linéaire récurrente si et seulement si son
annulateur est non trivial.

Une suite `u` est linéaire récurrente s'il existe `r ≥ 0` et des scalaires
`q_0, …, q_r` avec `q_0 ≠ 0` tels que pour tout `n`,
`∑ k, q_k • u (n + (r - k)) = 0`. L'annulateur de `u` est l'idéal des polynômes
`P` tels que `(P(σ))(u) = 0`, où `σ` est le décalage. -/
theorem subq_I_2_a {K : Type u} [Field K] {E : Type v} [AddCommGroup E] [Module K E]
    (u : ℕ → E) :
    let shiftEnd : Module.End K (ℕ → E) :=
      { toFun := fun u => fun n => u (n + 1),
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
    (∃ (r : ℕ) (q : Fin (r + 1) → K), q 0 ≠ 0 ∧
        ∀ n : ℕ, ∑ k : Fin (r + 1), q k • u (n + (r - k.val)) = 0) ↔
    (∃ P : K[X], P ≠ 0 ∧ (Polynomial.aeval shiftEnd P) u = 0) := by
  sorry

/-! ## I.3.a — Polynôme minimal de `(2^n + 3^n)` -/

/-- **Sous-question I.3.a, partie 1.** La suite `(2^n + 3^n)_{n ∈ ℕ}` à valeurs dans `ℝ`
est linéaire récurrente. -/
theorem subq_I_3_a_recurrent :
    ∃ (r : ℕ) (q : Fin (r + 1) → ℝ), q 0 ≠ 0 ∧
      ∀ n : ℕ, ∑ k : Fin (r + 1),
        q k • ((2 : ℝ) ^ (n + (r - k.val)) + (3 : ℝ) ^ (n + (r - k.val))) = 0 := by
  sorry

/-- **Sous-question I.3.a, partie 2.** Le polynôme minimal de la suite `(2^n + 3^n)`
est `X² − 5X + 6` : il annule la suite et est de degré minimal parmi les polynômes
non nuls qui l'annulent. -/
theorem subq_I_3_a_minpoly :
    let u : ℕ → ℝ := fun n => (2 : ℝ) ^ n + (3 : ℝ) ^ n
    let π : ℝ[X] := Polynomial.X ^ 2 - Polynomial.C 5 * Polynomial.X + Polynomial.C 6
    let shiftEnd : Module.End ℝ (ℕ → ℝ) :=
      { toFun := fun u => fun n => u (n + 1),
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl }
    (Polynomial.aeval shiftEnd π) u = 0 ∧
    ∀ P : ℝ[X], (Polynomial.aeval shiftEnd P) u = 0 → P ≠ 0 → π.degree ≤ P.degree := by
  sorry

/-! ## I.3.b — Récurrence linéaire de `(n!)`

Note : l'énoncé original de I.3.b demande de prouver que `(n!)` *est* linéaire
récurrente. La conclusion mathématique attendue est négative ; on conserve
néanmoins l'énoncé verbatim. -/

/-- **Sous-question I.3.b.** *Énoncé verbatim* : la suite `(n!)_{n ∈ ℕ}` à valeurs
dans `ℝ` est linéaire récurrente. -/
theorem subq_I_3_b :
    ∃ (r : ℕ) (q : Fin (r + 1) → ℝ), q 0 ≠ 0 ∧
      ∀ n : ℕ, ∑ k : Fin (r + 1),
        q k • ((n + (r - k.val)).factorial : ℝ) = 0 := by
  sorry

/-! ## II.1.a — Calcul de `D_m(u)` pour la suite de Fibonacci -/

/-- **Sous-question II.1.a.** Pour la suite de Fibonacci `fib`, on a
`D_0(fib) = 0`, `D_1(fib) = -1`, et `D_m(fib) = 0` pour `m ≥ 2`,
où `D_m(u) = det H_m(u)` est le déterminant de la matrice de Hankel
`H_m(u)_{i,j} = u_{i+j}` (indices 0-basés, `(i,j) ∈ Fin (m+1)²`). -/
theorem subq_II_1_a (m : ℕ) :
    Matrix.det (Matrix.of (fun (i j : Fin (m + 1)) => fib (i.val + j.val))) =
      if m = 1 then -1 else 0 := by
  sorry

/-! ## II.3.a — Rang de `H_s(u)` -/

/-- **Sous-question II.3.a.** Soit `u : ℕ → K` telle qu'il existe `s ≥ 1` avec
`D_{s-1}(u) ≠ 0` et `D_m(u) = 0` pour tout `m ≥ s`. Alors le rang de `H_s(u)` est `s`,
où `H_m(u)_{i,j} = u_{i+j}` et `D_m(u) = det H_m(u)`. -/
theorem subq_II_3_a {K : Type u} [Field K] (u : ℕ → K) (s : ℕ) (hs : 1 ≤ s)
    (h_pred :
      Matrix.det (Matrix.of (fun (i j : Fin ((s - 1) + 1)) => u (i.val + j.val))) ≠ 0)
    (h_zero : ∀ m, s ≤ m →
      Matrix.det (Matrix.of (fun (i j : Fin (m + 1)) => u (i.val + j.val))) = 0) :
    (Matrix.of (fun (i j : Fin (s + 1)) => u (i.val + j.val))).rank = s := by
  sorry

/-! ## III.1.a — `Φ` est bilinéaire et symétrique -/

/-- **Sous-question III.1.a, bilinéarité.** L'application
`Φ(P, Q) = coeff(PQ mod F, m − 1)` est bilinéaire en `P` (à `Q` fixé)
et en `Q` (à `P` fixé). -/
theorem subq_III_1_a_bilin {K : Type u} [Field K] (F : K[X]) (_hF : F.Monic) (m : ℕ)
    (_hm : 1 ≤ m) (_hdeg : F.natDegree = m) :
    -- linéarité en P (Q fixé)
    (∀ Q P₁ P₂ : K[X],
      (((P₁ + P₂) * Q) %ₘ F).coeff (m - 1) =
        ((P₁ * Q) %ₘ F).coeff (m - 1) + ((P₂ * Q) %ₘ F).coeff (m - 1)) ∧
    (∀ Q : K[X], ∀ (c : K) (P : K[X]),
      ((c • P * Q) %ₘ F).coeff (m - 1) = c * ((P * Q) %ₘ F).coeff (m - 1)) ∧
    -- linéarité en Q (P fixé)
    (∀ P Q₁ Q₂ : K[X],
      ((P * (Q₁ + Q₂)) %ₘ F).coeff (m - 1) =
        ((P * Q₁) %ₘ F).coeff (m - 1) + ((P * Q₂) %ₘ F).coeff (m - 1)) ∧
    (∀ P : K[X], ∀ (c : K) (Q : K[X]),
      ((P * (c • Q)) %ₘ F).coeff (m - 1) = c * ((P * Q) %ₘ F).coeff (m - 1)) := by
  sorry

/-- **Sous-question III.1.a, symétrie.** L'application
`Φ(P, Q) = coeff(PQ mod F, m − 1)` est symétrique. -/
theorem subq_III_1_a_symm {K : Type u} [Field K] (F : K[X]) (_hF : F.Monic) (m : ℕ)
    (_hm : 1 ≤ m) (_hdeg : F.natDegree = m) (P Q : K[X]) :
    ((P * Q) %ₘ F).coeff (m - 1) = ((Q * P) %ₘ F).coeff (m - 1) := by
  rw [mul_comm]

/-! ## III.6 — Lemme de Schwartz–Zippel -/

/-- **Sous-question III.6.** Lemme de Schwartz–Zippel : pour tout polynôme non nul
`R ∈ K[X_1, …, X_n]` de degré total `d` et tout sous-ensemble fini non vide `S ⊆ K`,
le nombre de zéros de `R` dans `S^n` est majoré par `d · |S|^{n-1}`. -/
theorem subq_III_6 {K : Type u} [Field K] [DecidableEq K] {n : ℕ}
    (R : MvPolynomial (Fin n) K) (_hR : R ≠ 0)
    (S : Finset K) (_hS : S.Nonempty) :
    (((Fintype.piFinset (fun _ : Fin n => S)).filter
      (fun s => MvPolynomial.eval s R = 0)).card : ℕ) ≤
        R.totalDegree * S.card ^ (n - 1) := by
  sorry

end AITP.P6Concrete
