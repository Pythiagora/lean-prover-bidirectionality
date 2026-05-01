import Mathlib

open BigOperators

/-- **Sous-question I.3.a (partie récurrence linéaire).** La suite `(2^n + 3^n)`
est linéaire récurrente : il existe `r ∈ ℕ` et `q : Fin (r+1) → ℝ` avec `q 0 ≠ 0`
tels que `∑ k, q k · (2^(n+(r-k)) + 3^(n+(r-k))) = 0` pour tout `n`.

Transcription du corrigé Mercier–Rombaldi (page 203–204) : trois
mouvements nommés ↦ trois opérations Lean nommées.

* Mouvement 1 (corrigé) : exhiber les témoins `r = 2`, `(q 0, q 1, q 2) = (1, -5, 6)`,
  qui correspondent au polynôme caractéristique `(X - 2)(X - 3) = X² - 5X + 6`.
  ↦ Lean : `refine ⟨2, ![(1 : ℝ), -5, 6], ?_, ?_⟩`.

* Mouvement 2 (corrigé) : vérifier `q 0 ≠ 0`.
  ↦ Lean : `norm_num` sur le but `(1 : ℝ) ≠ 0`.

* Mouvement 3 (corrigé) : montrer la relation `1·(2^(n+2)+3^(n+2)) − 5·(2^(n+1)+3^(n+1))
  + 6·(2^n+3^n) = 0` en factorisant `2^n` et `3^n` puis en utilisant que
  `4 − 10 + 6 = 0` et `9 − 15 + 6 = 0` (les racines `2` et `3` annulent
  `X² − 5X + 6`).
  ↦ Lean : on inscrit cette identité dans un `have h_rec := by ring`, puis on
  déplie la somme `Fin 3` via `Fin.sum_univ_three` et on conclut par `linarith`. -/
theorem subq_I_3_a_recurrent :
    ∃ (r : ℕ) (q : Fin (r + 1) → ℝ), q 0 ≠ 0 ∧
      ∀ n : ℕ, ∑ k : Fin (r + 1),
        q k • ((2 : ℝ) ^ (n + (r - k.val)) + (3 : ℝ) ^ (n + (r - k.val))) = 0 := by
  -- Mouvement 1 : témoins (r = 2, q = (1, -5, 6))
  refine ⟨2, ![(1 : ℝ), -5, 6], ?_, ?_⟩
  · -- Mouvement 2 : q 0 = 1 ≠ 0
    change (1 : ℝ) ≠ 0
    norm_num
  · -- Mouvement 3 : relation de récurrence à n fixé
    intro n
    -- L'identité algébrique du corrigé : factorisation de 2^n et 3^n.
    -- (X - 2)(X - 3) = X² - 5X + 6, d'où 4·2^n − 10·2^n + 6·2^n = 0
    -- et 9·3^n − 15·3^n + 6·3^n = 0.
    have h_rec :
        (1 : ℝ) * ((2 : ℝ) ^ (n + 2) + (3 : ℝ) ^ (n + 2))
          + (-5) * ((2 : ℝ) ^ (n + 1) + (3 : ℝ) ^ (n + 1))
          + 6 * ((2 : ℝ) ^ n + (3 : ℝ) ^ n) = 0 := by
      ring
    -- On déplie la somme indexée par Fin 3 en ses trois termes.
    simp [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          show (2 : ℕ) - 0 = 2 from rfl,
          show (2 : ℕ) - 1 = 1 from rfl]
    linarith [h_rec]
