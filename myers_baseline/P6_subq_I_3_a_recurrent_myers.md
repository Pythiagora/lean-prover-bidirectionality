# Myers-style transcription of Mercier–Rombaldi P6, sous-question I.3.a (récurrence linéaire)

Le script Lean 4 `P6_subq_I_3_a_recurrent_myers.lean` réalise les trois mouvements nommés du corrigé comme trois opérations Lean syntaxiquement distinctes, lisibles à l'envers vers le texte informel sans re-dérivation.

## Théorème (forme existentielle)

```lean4
theorem subq_I_3_a_recurrent :
    ∃ (r : ℕ) (q : Fin (r + 1) → ℝ), q 0 ≠ 0 ∧
      ∀ n : ℕ, ∑ k : Fin (r + 1),
        q k • ((2 : ℝ) ^ (n + (r - k.val)) + (3 : ℝ) ^ (n + (r - k.val))) = 0
```

## Trois mouvements corrigé ↦ trois opérations Lean

Le corrigé Mercier–Rombaldi (page 203, première solution ; page 204 paragraphe final, troisième solution) procède en trois temps. (i) Identifier le polynôme caractéristique : la suite `u_n = 2^n + 3^n` est combinaison linéaire de `2^n` (annulé par `X − 2`) et `3^n` (annulé par `X − 3`), donc `(X − 2)(X − 3) = X² − 5X + 6` annule `u`. (ii) Lire les témoins `r = 2`, `q = (1, −5, 6)` directement dans les coefficients de ce polynôme caractéristique. (iii) Vérifier la relation `1 · (2^(n+2) + 3^(n+2)) − 5 · (2^(n+1) + 3^(n+1)) + 6 · (2^n + 3^n) = 0` en factorisant `2^n` et `3^n` (`(4 − 10 + 6) · 2^n + (9 − 15 + 6) · 3^n = 0`).

Le script Myers inscrit ces trois mouvements en bijection. Le mouvement (ii) — exhibition des témoins — est un `refine ⟨2, ![(1 : ℝ), -5, 6], ?_, ?_⟩`. Les coefficients du polynôme caractéristique apparaissent en clair dans le vecteur littéral, sans encodage `match` ni définition par fonction anonyme. Le mouvement « `q 0 ≠ 0` » se réduit après `change` à `(1 : ℝ) ≠ 0` que `norm_num` ferme. Le mouvement (iii) — identité algébrique — est inscrit comme `have h_rec : 1 * (2^(n+2) + 3^(n+2)) + (-5) * (2^(n+1) + 3^(n+1)) + 6 * (2^n + 3^n) = 0 := by ring`. Le contenu mathématique est l'identité ; `ring` la *certifie* mais ne la cherche pas — les coefficients `(1, -5, 6)` et la structure additive sont écrits à la main. Le déploiement de la somme `Fin 3` en ses trois termes (qui est purement combinatoire, non mathématique) passe par `simp [Fin.sum_univ_three, ...]` avec les trois soustractions naturelles `2 - 0 = 2`, `2 - 1 = 1` injectées comme `rfl`. Le `linarith [h_rec]` final fait du *bookkeeping* sur l'hypothèse nommée — il ne cherche pas un certificat numérique, il combine `h_rec` (déjà sous la bonne forme) avec le but. Une lectrice qui parcourt le script à l'envers retrouve dans l'ordre les trois mouvements : témoins, certification de `q 0 ≠ 0`, identité de récurrence, fermeture par hypothèse nommée.

## Auto-classification

(a) — Transcription Myers fidèle. Les trois `have` / `refine` / `simp + linarith` sont en bijection avec les trois mouvements nommés du corrigé ; les coefficients `(1, -5, 6)` du polynôme caractéristique sont écrits à la main dans le `refine`, pas synthétisés ; l'identité `1·a_{n+2} − 5·a_{n+1} + 6·a_n = 0` est inscrite verbatim dans `h_rec` ; `linarith` voit uniquement une hypothèse déjà nommée, sans hint-list de carrés ou de positivités.

## Vérification kernel + lean-lsp

* `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier : **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée).
* `mcp__lean-lsp__lean_goal` à la ligne 47 (juste avant `linarith [h_rec]`) :
  - `goals_before` : `n : ℕ`, `h_rec : 1 * (2^(n+2) + 3^(n+2)) + -5 * (2^(n+1) + 3^(n+1)) + 6 * (2^n + 3^n) = 0`, but `2^(n+2) + 3^(n+2) + -(5 * (2^(n+1) + 3^(n+1))) + 6 * (2^n + 3^n) = 0` (la différence est purement le placement du `-` ; les deux membres sont AC-équivalents).
  - `goals_after` : `[]` — fermé par `linarith` opérant sur `h_rec` seul, sans hint-list arithmétique.

## Comparaison directe avec PASSes ML représentatifs

### Kimina attempt 00 (PASS, classifié (a) par sub-agent)

```lean4
use 2
use λ k =>
  match k with
  | 0 => (1 : ℝ)
  | 1 => (-5 : ℝ)
  | 2 => (6 : ℝ)
  | _ => (0 : ℝ)
constructor
· simp
· intro n
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  ring_nf
```

Kimina reproduit la structure du corrigé. Les témoins `(1, -5, 6)` sont exhibés. La somme est dépliée par `simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]` (Myers passe par `Fin.sum_univ_three`, mécaniquement équivalent). La fermeture `ring_nf` opère sur l'identité algébrique entière, c'est-à-dire qu'elle re-prouve `(4 - 10 + 6)·2^n + (9 - 15 + 6)·3^n = 0` en interne. Différence avec Myers : Kimina n'inscrit pas l'identité de récurrence comme `have` nommé séparé. Le contenu mathématique du mouvement (iii) du corrigé — « factorisation de `2^n`, `3^n` ; les racines `2` et `3` annulent `X² − 5X + 6` » — n'a pas de support textuel dans le script Kimina ; il est absorbé dans `ring_nf` qui le re-découvre. Verdict : (a) bidirectionnellement satisfaisant au niveau de la macro-structure (témoins + dépliage + clôture algébrique) mais pas au niveau du mouvement (iii) (l'identité n'est pas inscrite comme un objet du script).

### Goedel attempt 05 (PASS, classifié (b) par sub-agent)

```lean4
have h_main : ∃ ... := by
  use 2
  use ![1, -5, 6]
  constructor
  · norm_num [Fin.val_zero]
    <;> simp [Matrix.cons_val_zero]
    <;> norm_num
  · intro n
    simp [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    <;> norm_num [pow_add, pow_one, pow_two, pow_mul, mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;> simp [pow_add, pow_one, pow_two, pow_mul, mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;> linarith [pow_pos (by norm_num : (0 : ℝ) < 2) n,
                  pow_pos (by norm_num : (0 : ℝ) < 3) n]
exact h_main
```

Goedel reproduit les témoins `![1, -5, 6]` (équivalents à Myers). La structure macro est néanmoins enveloppée d'un wrapper `have h_main := by ...; exact h_main` purement décoratif (le but de `h_main` est *littéralement* le but du théorème). Le dépliage de la somme passe par `Fin.sum_univ_succ` (au lieu de `Fin.sum_univ_three`), suivi d'une cascade `<;>` à 7 étapes (`norm_num`, `ring_nf`, `norm_num`, `simp`, `ring_nf`, `norm_num`, `linarith`) avec hint-list `[pow_pos ... 2, pow_pos ... 3]`. Aucune des 7 étapes ne correspond à un mouvement nommé du corrigé. Le `linarith` final reçoit des hypothèses de positivité strictes sur `2^n` et `3^n`, qui n'apparaissent nulle part dans le corrigé (le corrigé ne raisonne pas sur la positivité — il raisonne sur l'annulation des coefficients par les racines `2` et `3` du polynôme caractéristique). Verdict : (b) lower-abstraction. Les témoins sont préservés ; tout le reste du script est shotgun arithmétique RL-tuné, sans correspondance avec le texte du corrigé.

## Hiérarchie observée sur P6.subq_I_3_a_recurrent

| | témoins (1,−5,6) | `q 0 ≠ 0` | dépliage somme | identité récurrence | fermeture | classification |
|---|---|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `refine ⟨2, ![1,-5,6], ...⟩` | `norm_num` | `simp [Fin.sum_univ_three]` | `have h_rec := by ring` | `linarith [h_rec]` | (a) parfait |
| **Kimina att00** | `use 2; use λ k => match k ...` | `simp` | `simp [sum_fin_eq_sum_range, sum_range_succ]` | absente (absorbée dans `ring_nf`) | `ring_nf` | (a) macro mais (iii) absorbée |
| **Goedel att05** | `use 2; use ![1,-5,6]` (dans wrapper) | `norm_num <;> simp <;> norm_num` | `simp [Fin.sum_univ_succ, ...]` | absente | cascade 7-étapes `<;>` + `linarith [pow_pos × 2]` | (b) lower-abstraction |

Trois preuves kernel-équivalentes, trois profils bidirectionnels distincts. La distinction n'est pas stylistique mais structurelle : le mouvement (iii) du corrigé — l'identité de récurrence comme objet mathématique nommé — n'apparaît comme `have` que dans le script Myers. Kimina l'absorbe dans `ring_nf` ; Goedel le dilue dans une cascade `<;>` shotgun.

## Implications pour la métrique de bidirectionalité

1. **Trois positions sur l'axe d'inscription du contenu mathématique.** Sur P12 (carré-completion), Myers et Goedel inscrivaient tous deux l'identité (avec bruit syntaxique chez Goedel) ; Kimina ne l'inscrivait pas. Sur P6.subq_I_3_a_recurrent (récurrence linéaire), Myers reste le seul à inscrire l'identité comme `have` nommé. Kimina la traite par tactique générique (`ring_nf`), Goedel par cascade. Cette divergence sur P6 vs P12 confirme que la bidirectionalité Myers est calibrée à un point fixe : *toujours* inscrire les mouvements nommés du corrigé, indépendamment de la difficulté.

2. **Inversion v6 confirmée à plus haute résolution mais avec rebattage des cartes.** Sur P6, Kimina (98 % (a) au sens INDEX.md « route-preserving ») est macro-fidèle : les témoins et le dépliage de somme correspondent au corrigé. Mais Kimina absorbe le mouvement (iii) dans `ring_nf`. Goedel (100 % (b)) ne préserve que les témoins et dilue tout le reste. Le sous-agent qui a classé Kimina comme (a) sur INDEX.md utilisait une définition « macro-structurelle » de bidirectionalité (témoins + dépliage + clôture algébrique). Une définition plus fine — *chaque* mouvement nommé du corrigé doit avoir une trace nommée dans le script — produirait un classement (a) parfait *uniquement* pour Myers, (a) partiel pour Kimina, (b) pour Goedel.

3. **Ground truth artefact.** Ce fichier `.lean` peut être publié comme baseline kernel-vérifiée pour P6.subq_I_3_a_recurrent dans le repo `lean-prover-bidirectionality`. Les trois `have` / `refine` / `simp + linarith` sont individuellement traçables aux trois phrases du corrigé pages 203–204.

## Phrasing pour WDWFT (P6 instance)

> *Sur P6.subq_I_3_a_recurrent (existence d'une récurrence linéaire pour `2^n + 3^n`), le script Myers-fidèle inscrit (i) les témoins `r = 2`, `q = (1, -5, 6)` directement par `refine ⟨2, ![1,-5,6], ?_, ?_⟩` — coefficients lus dans le polynôme caractéristique `(X-2)(X-3) = X² - 5X + 6` ; (ii) `q 0 ≠ 0` par `norm_num` sur la valeur explicite ; (iii) l'identité de récurrence `1·a_{n+2} − 5·a_{n+1} + 6·a_n = 0` comme un `have h_rec := by ring` nommé, puis fermeture par `linarith [h_rec]`. Le script Kimina canonique (62 PASSes) reproduit (i) et le dépliage de somme mais absorbe (iii) dans un `ring_nf` final, perdant la trace explicite de la factorisation `(4-10+6)·2^n + (9-15+6)·3^n = 0`. Le script Goedel canonique (53 PASSes) préserve (i) puis dilue (iii) dans une cascade `<;>` à 7 étapes avec hint-list de positivité `[pow_pos ... 2, pow_pos ... 3]`, étrangère au corrigé. Les trois sont kernel-équivalents. Seul Myers satisfait le critère bidirectionnel à granularité fine.*
