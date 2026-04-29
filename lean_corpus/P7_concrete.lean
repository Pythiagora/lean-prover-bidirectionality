/-
  Chapter 7 — Année 2011, épreuve 1.
  Mercier & Rombaldi, *Annales de l'agrégation interne 2005–2013*, Chapter 7.

  Topic: graph Laplacian eigenvalues and the chromatic number.

  This file is the **concrete** counterpart of `P7.lean`: every theorem statement is
  self-contained — all custom helpers from `P7.lean` (`normLapMatrix`, `phi1`, `G1`,
  `cyclicShift`, `J`) are inlined as `let` bindings or expressed via concrete Mathlib
  operations. The point is that a model receiving only the theorem signature can read
  off the full definition of every matrix involved without consulting external
  definitions.

  The book's normalized Laplacian
    L_{ii} = 1   (when d_i ≥ 1),
    L_{ij} = -1 / sqrt(d_i d_j) if i ~ j,
    L_{ij} = 0 otherwise
  is inlined either via explicit matrix entries (when the graph is a small concrete
  example) or as
    `fun i j => if i = j then (if G.degree i = 0 then 0 else 1)
                else if G.Adj i j then - 1 / Real.sqrt (G.degree i * G.degree j)
                else 0`
  (when the graph is generic).
-/
import LeanCorpus.Common

namespace AITP.P7Concrete

open Finset Matrix Complex SimpleGraph

noncomputable section

/-! ## A.1 — Exemple 1 : le graphe linéaire `G_1` -/

/--
**Book A.1 (easy).**
"Déterminer les valeurs propres et une base orthonormale de vecteurs propres pour la matrice `L`
correspondant au graphe `G_1` défini dans le préliminaire."
English: For the graph `G_1` (the path on 3 vertices with center 0), the spectrum of the
normalized Laplacian is `{0, 1, 2}`.

The graph `G_1` is the path `1 — 0 — 2`. Vertex `0` has degree `2`, vertices `1` and `2` have
degree `1`. Hence the normalized Laplacian is the explicit `3 × 3` matrix
  `L_00 = 1, L_11 = 1, L_22 = 1`
  `L_01 = L_10 = -1/√2`,  `L_02 = L_20 = -1/√2`,
  `L_12 = L_21 = 0`.
We inline `L` directly with these entries.
-/
theorem subq_A_1 :
    let L : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      if i = j then 1
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
        then - 1 / Real.sqrt 2
      else 0
    spectrum ℝ L = ({0, 1, 2} : Set ℝ) := by
  sorry

/-! ## A.2.a — Le graphe complet : décomposition matricielle -/

/--
**Book A.2.a (easy).**
"Écrire la matrice `L` du graphe `K_n` comme combinaison linéaire de la matrice identité `I_n`
et de la matrice `J`."
English: For `n ≥ 2`, the normalized Laplacian of the complete graph `K_n` decomposes as
`L = (n / (n-1)) • I_n - (1 / (n-1)) • J_n`, where `J_n` is the all-ones matrix.

On `K_n`, every vertex has degree `n - 1`, so `L_{ii} = 1` and `L_{ij} = -1/(n-1)` for `i ≠ j`.
We inline `L` directly with these entries (no detour through `G.degree`), and the all-ones
matrix `J` as `fun _ _ => 1`.
-/
theorem subq_A_2_a (n : ℕ) (hn : 2 ≤ n) :
    let L : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if i = j then 1 else - 1 / ((n : ℝ) - 1)
    let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
    L = ((n : ℝ) / (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)
        - (1 / ((n : ℝ) - 1)) • J := by
  sorry

/-! ## A.3.a.i — Cyclic shift matrix : `C^{n+1} = I_{n+1}` -/

/--
**Book A.3.a (i) — easy.**
"Calculer `C^n`."
English: The `(n+1)`-th power of the cyclic shift matrix on `Fin (n+1)` is the identity:
`C^{n+1} = I_{n+1}`. Here `C_{i,j} = 1` iff `j = i - 1` (where subtraction is in `Fin (n+1)`),
and `0` otherwise.

The cyclic shift matrix is inlined as a `let`-binding.
-/
theorem subq_A_3_a_i (n : ℕ) :
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      fun i j => if j = i - 1 then 1 else 0
    C ^ (n + 1) = 1 := by
  sorry

/-! ## A.3.a.ii — Spectrum and complex eigenspaces of `C` -/

/--
**Book A.3.a (ii) — medium.**
"En déduire le spectre et les sous-espaces propres complexes de `C`."
English: For `ω = exp(2 i π / (n+1))`, the spectrum of the cyclic shift on `Fin (n+1)` is
`{ω^k : 0 ≤ k ≤ n}`.

The cyclic shift matrix is inlined as a `let`-binding.
-/
theorem subq_A_3_a_ii (n : ℕ) :
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      fun i j => if j = i - 1 then 1 else 0
    spectrum ℂ C =
      (Set.range fun k : Fin (n + 1) =>
        Complex.exp (2 * Real.pi * I * (k : ℂ) / ((n + 1 : ℕ) : ℂ))) := by
  sorry

/-! ## B.1.a (i) — Quadratic form of the Laplacian on vertices -/

/--
**Book B.1.a (first equality) — easy.**
"Démontrer que pour tout `x ∈ ℝ^n`,
`⟨L x, x⟩ = (1/2) ∑_{i=1}^n ∑_{j ~ i} (x(i)/√d_i - x(j)/√d_j)²`."
English: For every vector `x : V → ℝ`, the quadratic form `⟨L x, x⟩` equals
`(1/2) ∑_i ∑_{j ~ i} (x(i)/√d_i - x(j)/√d_j)²`.

The normalized Laplacian is inlined as a `let`-binding inside the theorem statement.
We assume `d_i ≥ 1` for every vertex (the book's standing hypothesis: no isolated vertex).
-/
theorem subq_B_1_a_i {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_no_isolated : ∀ i : V, 1 ≤ G.degree i) (x : V → ℝ) :
    let L : Matrix V V ℝ :=
      fun i j =>
        if i = j then (if G.degree i = 0 then 0 else 1)
        else if G.Adj i j then - 1 / Real.sqrt (G.degree i * G.degree j)
        else 0
    x ⬝ᵥ (L *ᵥ x) =
      (1 / 2) * ∑ i : V, ∑ j ∈ G.neighborFinset i,
        (x i / Real.sqrt (G.degree i) - x j / Real.sqrt (G.degree j)) ^ 2 := by
  sorry

/-! ## B.3.a — Rayleigh quotient in an eigenbasis -/

/--
**Book B.3.a (easy).**
"Soit `(φ_1, …, φ_n)` une base orthonormale de `ℝ^n` avec `L φ_i = λ_i φ_i`. Démontrer que pour
tout `x ∈ ℝ^n` non nul,
`⟨L x, x⟩ / ‖x‖² = (∑ λ_i ⟨φ_i, x⟩²) / (∑ ⟨φ_i, x⟩²)`."
English: Given an orthonormal eigenbasis `φ` for `L` with eigenvalues `λ`, the Rayleigh quotient
of any non-zero `x : V → ℝ` equals the weighted average of `λ_i` with weights `⟨φ_i, x⟩²`.

This statement does not involve the normalized Laplacian explicitly: it is stated for any real
square matrix `L` admitting an orthonormal eigenbasis. No helpers to inline.
-/
theorem subq_B_3_a {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ)
    (φ : V → V → ℝ) (lam : V → ℝ)
    (h_orth : ∀ i j : V, (φ i) ⬝ᵥ (φ j) = if i = j then 1 else 0)
    (h_eig : ∀ i : V, L *ᵥ (φ i) = lam i • (φ i))
    (x : V → ℝ) (hx : x ≠ 0) :
    (x ⬝ᵥ (L *ᵥ x)) / (x ⬝ᵥ x) =
      (∑ i : V, lam i * ((φ i) ⬝ᵥ x) ^ 2) / (∑ i : V, ((φ i) ⬝ᵥ x) ^ 2) := by
  sorry

/-! ## C.2.a (i) — Test vector for C.2 : edge-by-edge formula -/

/--
**Book C.2.a (first part) — medium.**
"Soient `i` et `j` deux sommets distincts non voisins de `G`, et soit `φ ∈ ℝ^n` tel que
`φ(k) = √(d_j)` si `k = i`, `−√(d_i)` si `k = j`, et `0` sinon. Démontrer que pour toute arête
`{k, l} ∈ A`, `(φ(k)/√d_k − φ(l)/√d_l)² = d_j/d_i` si `k = i` ou `l = i`, `d_i/d_j` si `k = j` ou
`l = j`, `0` sinon."
English: Define `φ` as above; then for every edge `{k, l}` of `G`, the squared difference
`(φ(k)/√d_k − φ(l)/√d_l)²` equals `d_j/d_i`, `d_i/d_j`, or `0`, by case analysis on whether the
edge touches `i`, `j`, or neither.

This statement does not involve the normalized Laplacian: it is purely about the test vector
`φ` and the graph degrees. No helpers to inline.
-/
theorem subq_C_2_a_i {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_no_isolated : ∀ v : V, 1 ≤ G.degree v)
    (i j : V) (hij : i ≠ j) (h_nonadj : ¬ G.Adj i j)
    (φ : V → ℝ)
    (hφ : φ = fun k => if k = i then Real.sqrt (G.degree j)
                       else if k = j then - Real.sqrt (G.degree i)
                       else 0)
    (k l : V) (hkl : G.Adj k l) :
    (φ k / Real.sqrt (G.degree k) - φ l / Real.sqrt (G.degree l)) ^ 2 =
      if k = i ∨ l = i then (G.degree j : ℝ) / (G.degree i)
      else if k = j ∨ l = j then (G.degree i : ℝ) / (G.degree j)
      else 0 := by
  sorry

/-! ## C.3.d — `λ_n = 2` ⇒ `G` is bipartite -/

/--
**Book C.3.d (hard).**
"On suppose que `λ_n = 2`. Montrer que `G` est un graphe biparti."
English: If `G` is connected and `2` is the largest eigenvalue of the normalized Laplacian
(equivalently, `2 ∈ spectrum`, given the bound `λ_n ≤ 2` from C.3.b), then `G` is bipartite.

The normalized Laplacian is inlined as a `let`-binding. The bipartiteness predicate is
`SimpleGraph.IsBipartite` from Mathlib (an abbreviation for `Colorable 2`).
-/
theorem subq_C_3_d {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_no_isolated : ∀ v : V, 1 ≤ G.degree v)
    (h_conn : G.Connected)
    (h_lam_n :
      let L : Matrix V V ℝ :=
        fun i j =>
          if i = j then (if G.degree i = 0 then 0 else 1)
          else if G.Adj i j then - 1 / Real.sqrt (G.degree i * G.degree j)
          else 0
      (2 : ℝ) ∈ spectrum ℝ L) :
    G.IsBipartite := by
  sorry

end

end AITP.P7Concrete
