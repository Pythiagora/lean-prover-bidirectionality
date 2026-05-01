# Solution transcription of Mercier-Rombaldi P10, sub-question III.A.3.c

The Lean 4 script at `P10_subq_III_A_3_c.lean` realises the official solution's four named moves as four syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

The official solution proceeds: instantiate the hypothesis `hx_rec` at `(n, k+1)` to obtain `x (n+1) (k+1) = (1/((k+1:ℕ):ℂ + 1)) · ∑_{j ∈ range((k+1)+1)} x n j`; split the range-`(k+2)` sum at the top via `Finset.sum_range_succ` to extract `x n (k+1)`; simplify the cast `((k+1:ℕ):ℂ) + 1 = (k:ℂ) + 2`; distribute and reorder. Each move is inscribed as a named `have` (or, for the closing distributivity, a single `ring`):

- `have h_rec : x (n+1) (k+1) = (1/(((k+1:ℕ):ℂ)+1)) * ∑ j ∈ range ((k+1)+1), x n j := hx_rec n (k+1)` — the recurrence instantiation is just a function application, not a tactic search. The official solution sentence "on applique la relation de récurrence en `(n, k+1)`" maps one-to-one to a single `hx_rec n (k + 1)` term.
- `have h_split : ∑ j ∈ range ((k+1)+1), x n j = (∑ j ∈ range (k+1), x n j) + x n (k+1) := Finset.sum_range_succ (fun j => x n j) (k+1)` — the sum split is a direct lemma application of `Finset.sum_range_succ`, with no rewrite-cascade or `simp` extension. The official solution sentence "on isole le dernier terme" inscribes verbatim as the named lemma.
- `have h_cast : ((k+1:ℕ):ℂ) + 1 = (k:ℂ) + 2 := by push_cast; ring` — the cast simplification is closed by exactly the two tactics it is *about*: `push_cast` (which pushes the `ℕ → ℂ` coercion through the addition) followed by `ring` (which normalises the resulting commutative-ring expression). No `omega`, no `simp [Complex.ext_iff]`, no `norm_num` cascade.
- `rw [h_rec, h_split, h_cast]; ring` — the three named hypotheses are applied in order, and the residual goal `1/((k:ℂ)+2) · (∑ + x n (k+1)) = 1/((k:ℂ)+2) · x n (k+1) + 1/((k:ℂ)+2) · ∑` is closed by a single `ring` doing exactly the distributivity-and-commutativity bookkeeping it is built for.

This is the bidirectional sweet spot: each named official solution move corresponds to a named Lean operation, and the closing `ring` operates on the goal already reduced to a pure ring-arithmetic equality. A reverse-reader scanning the script meets exactly the official solution's four sentences in order: recurrence instantiation, sum split, cast simplification, distributivity.

## Self-classification

(a) — Faithful transcription. The four official solution moves are in bijection with four syntactically distinct Lean operations: a term application of `hx_rec`, a term application of `Finset.sum_range_succ`, a `push_cast; ring` cast normalisation, and a final `ring` for distributivity. No `simp_all`, no `<;>` chain, no hint-list `nlinarith`, no `field_simp` cascade. The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée).
- `mcp__lean-lsp__lean_goal` à la ligne 29 (juste avant le bloc `rw [h_rec, h_split, h_cast]; ring`):
  - `goals_before`: contexte avec `h_rec`, `h_split`, `h_cast` nommés, but `x (n+1) (k+1) = 1/(↑k+2) · x n (k+1) + 1/(↑k+2) · ∑ j ∈ range (k+1), x n j`
  - après `rw [h_rec, h_split, h_cast]`: but `1/(↑k+2) · (∑ + x n (k+1)) = 1/(↑k+2) · x n (k+1) + 1/(↑k+2) · ∑`
  - `goals_after` (après `ring`): `[]` — fermé proprement
- `mcp__lean-lsp__lean_multi_attempt` à la ligne 30 (la fermeture finale): `ring` ferme; `ring_nf` ferme aussi (mais redondant); `linarith` échoue avec "linarith failed to find a contradiction" (le but est une égalité polynomiale en ℂ, pas un goal linéaire); `linear_combination` requiert un certificat explicite que `ring` rend inutile. Le tactique minimal qui ferme dans le contexte nommé est `ring` — pas de cascade, pas de `simp_all`.
- Au total: 1 itération lean-lsp pour valider, 0 corrections nécessaires.

## Comparaison directe avec scripts ML générés (5 PASSes au total: 4 Goedel + 1 Kimina)

### Goedel attempt 28 (PASS, classifié (b) lower-abstraction par sub-agent)

```lean4
have h_main : x (n + 1) (k + 1) = (1 / ((k : ℂ) + 2)) * (∑ j ∈ Finset.range (k + 1), x n j + x n (k + 1)) := by
  have h₁ : x (n + 1) (k + 1) = (1 / (((k + 1 : ℕ) : ℂ) + 1)) * ∑ j ∈ Finset.range ((k + 1 : ℕ) + 1), x n j := by
    have h₂ := hx_rec n (k + 1)
    simpa using h₂
  rw [h₁]
  have h₃ : (((k + 1 : ℕ) : ℂ) + 1 : ℂ) = ((k : ℂ) + 2 : ℂ) := by
    norm_cast
    <;> ring_nf
    <;> simp [Complex.ext_iff]
    <;> norm_num
    <;> ring_nf
    <;> simp_all [Complex.ext_iff]
    <;> norm_num
    <;> linarith
  rw [h₃]
  have h₄ : ∑ j ∈ Finset.range ((k + 1 : ℕ) + 1), x n j = ∑ j ∈ Finset.range (k + 1), x n j + x n (k + 1) := by
    rw [Finset.sum_range_succ, add_comm]
    <;> simp [add_assoc]
  rw [h₄]
  <;> ring_nf
have h_split : ... := by
  have h₁ : ... := by
    ring_nf
    <;> simp [Complex.ext_iff, Finset.sum_add_distrib, mul_add, add_mul]
    <;> norm_num
    <;> ring_nf
    <;> simp_all [Complex.ext_iff, Finset.sum_add_distrib, mul_add, add_mul]
    <;> norm_num
    <;> linarith
  rw [h₁]
have h_final : ... := by
  rw [h_main]
  rw [h_split]
  <;> ring_nf
  <;> simp [add_comm, add_left_comm, add_assoc]
  <;> ...
apply h_final
```

Goedel reproduit la structure macro (3 `have`s alignés sur les étapes official solution: instantiation, split, distributivité finale) mais ajoute du bruit syntaxique RL closure-tuning massif:

- La cascade `norm_cast <;> ring_nf <;> simp [Complex.ext_iff] <;> norm_num <;> ring_nf <;> simp_all [Complex.ext_iff] <;> norm_num <;> linarith` pour fermer `((k+1:ℕ):ℂ) + 1 = (k:ℂ) + 2` est inutile — `push_cast; ring` (deux tactiques, ~15 chars) suffit. Goedel utilise 7 tactiques chaînées par `<;>` (~140 chars) pour le même goal.
- L'identité de distributivité (`h_split`) est fermée par `ring_nf <;> simp [Complex.ext_iff, Finset.sum_add_distrib, mul_add, add_mul] <;> norm_num <;> ring_nf <;> simp_all [...] <;> norm_num <;> linarith`. Là où le script transcription utilise un seul `ring` final après `rw`, Goedel chaîne 7 tactiques avec hint-list explicite `[mul_add, add_mul]`.
- L'étape finale `h_final` reste fermée par `<;> ring_nf <;> simp [add_comm, add_left_comm, add_assoc] <;> (try norm_num) <;> (try ring_nf) <;> (try simp_all [...]) <;> (try norm_num) <;> (try linarith)` — sept tentatives `(try ...)` enchaînées, dont aucune n'est *l'opération* qui ferme le goal.
- Char-len Goedel att28: 2127 chars vs 1246 pour transcription — facteur **1.7×** d'inflation pour la même preuve kernel-équivalente.

Verdict: structure macro préservée (les 3 `have`s correspondent aux 3 mouvements), arithmétique sub-niveau opaque (chaque sub-closure est une cascade non-sémantique).

### Kimina attempt 25 (PASS, classifié (a) route-preserving par sub-agent)

```lean4
have eq1 : x (n + 1) (k + 1) = (1 / ((k + 1 : ℂ) + 1)) * ∑ j in Finset.range (k + 1 + 1), x n j := by
  specialize hx_rec (n) (k + 1)
  simpa using hx_rec
rw [eq1]
have h1 : (k + 1 : ℂ) + 1 = (k : ℂ) + 2 := by
  simp [Complex.ext_iff]
  all_goals omega
rw [h1]
have h2 : k + 1 + 1 = k + 2 := by omega
simp [h2]
have h3 : ∑ j in Finset.range (k + 2), x n j = (∑ j in Finset.range (k + 1), x n j) + x n (k + 1) := by
  rw [Finset.sum_range_succ]
have eq2 : ... := by ring
have eq3 : ... := by rw [h3]
rw [eq3]
rw [eq2]
```

Kimina att25 est le PASS le plus proche du script transcription en structure: 6 `have`s nommés, chacun correspondant à une étape distincte, fermetures par tactiques individuelles (`omega`, `simpa`, `ring`, `rw [Finset.sum_range_succ]`) plutôt que cascades. Différences résiduelles avec transcription:

- Kimina utilise `specialize hx_rec n (k+1); simpa using hx_rec` pour l'instantiation, mutant l'hypothèse globale. transcription garde `hx_rec` intact et nomme l'instance comme `have h_rec := hx_rec n (k + 1)` — application terme directe, sans tactique.
- Kimina ferme le cast `(k+1:ℂ) + 1 = (k:ℂ) + 2` par `simp [Complex.ext_iff]; all_goals omega`. transcription utilise `push_cast; ring`. Les deux sont propres single-shot, mais `push_cast; ring` est sémantiquement plus précis: la première tactique *est* "pousser la coercion ℕ→ℂ", la seconde *est* "normaliser la somme commutative" — chaque tactique nomme exactement le mouvement qu'elle effectue. `simp [Complex.ext_iff]; omega` invoque l'extensionnalité de ℂ et un solveur linéaire arithmétique sur ℕ, ce qui est correct mais sémantiquement détourné (le but ne mentionne ni l'extensionnalité de ℂ, ni un goal arithmétique sur ℕ).
- Kimina introduit deux `have` intermédiaires (`eq2`, `eq3`) pour chaîner les réécritures finales. transcription fait l'ensemble en `rw [h_rec, h_split, h_cast]; ring` — quatre opérations en deux lignes, sans `have` intermédiaire.
- Char-len Kimina att25: 1152 chars vs 1246 pour transcription — quasi-équivalents (transcription est légèrement plus long parce qu'il ajoute des commentaires `-- Move N`).

Verdict: structurellement aligné, légèrement détourné dans la fermeture du cast.

## Hiérarchie observée sur P10.III.A.3.c

| | recurrence instantiation | cast simplification | sum split | distributivité finale | classification |
|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `have h_rec := hx_rec n (k+1)` | `push_cast; ring` | `Finset.sum_range_succ _ _` (terme) | `rw [...]; ring` | (a) parfait |
| **Kimina att25** | `specialize hx_rec n (k+1); simpa` | `simp [Complex.ext_iff]; omega` | `rw [Finset.sum_range_succ]` | `rw [eq3]; rw [eq2]` (via 2 have intermédiaires) | (a) route-preserving |
| **Goedel att28** | `have h₂ := hx_rec n (k+1); simpa using h₂` | `norm_cast <;> ring_nf <;> simp <;> norm_num <;> ring_nf <;> simp_all <;> norm_num <;> linarith` (7 tactiques) | `rw [Finset.sum_range_succ, add_comm] <;> simp` | `<;> ring_nf <;> simp [...] <;> (try norm_num) <;> (try ring_nf) <;> (try simp_all) <;> (try norm_num) <;> (try linarith)` | (b) lower-abstraction |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts. Sur cette sub-question, le PASS Kimina (kimina_att25) atteint la classification (a) — un cas où Kimina coïncide avec le script transcription à l'épaisseur d'une fermeture de cast près. Les quatre PASSes Goedel restent (b): structure macro préservée mais sub-closures opaques.

## Comparaison aux floor PASS-rates

P10.III.A.3.c a parmi les plus bas PASS-rates de la suite: Goedel 4/64 (6.3%), Kimina 1/64 (1.6%). Le script transcription est obtenu en une itération sans recherche tactique (term-mode pour `hx_rec n (k+1)` et `Finset.sum_range_succ _ _`, `push_cast; ring` pour le cast, `ring` pour la distributivité). L'asymétrie entre la difficulté ML (PASS-rate ~5% combiné) et la facilité transcription (premier essai, 30 lignes commentaires inclus) illustre que la difficulté pour les modèles RL n'est pas dans la *structure du raisonnement* — qui est élémentaire — mais dans la *coordination des coercions ℕ→ℂ et des index `k+1+1` vs `k+2`*. Les modèles compensent par cascades de simp/ring_nf/norm_num qui font effectivement le travail mais le rendent illisible.

## Implications

### Pour AITP v7

1. **Le PASS-rate flooor n'est pas un indicateur direct de complexité bidirectionnelle**: une preuve avec PASS-rate ~5% peut admettre un script transcription de 4 mouvements nommés. La métrique de difficulté ML (PASS-rate) capture la *coordination de surface* (coercions, indices), pas la *profondeur du raisonnement*.
2. **L'inversion v6 confirmée à plus haute résolution**: sur cette sub-question, Kimina (1 PASS) atteint (a); Goedel (4 PASSes) reste à (b). C'est le contraire du pattern modal Goedel-meilleur. La métrique route-preservation discrimine donc orthogonalement au raw PASS-rate.
3. **`push_cast` est sous-utilisé par les deux modèles**: aucun PASS Goedel ni Kimina n'invoque `push_cast` pour la simplification de cast `((k+1:ℕ):ℂ) + 1 = (k:ℂ) + 2`. Goedel utilise `norm_cast` enchaîné par cascade; Kimina utilise `simp [Complex.ext_iff]; omega`. `push_cast` (la tactique idiomatique Mathlib pour ce mouvement précis) n'apparaît nulle part dans les 5 PASSes.

### Pour WDWFT

Cet artefact répond directement à l'objection "la bidirectionalité dépend du choix de tactique idiomatique":

- Le script transcription utilise `push_cast` là où Goedel utilise `norm_cast` (différence de force) et Kimina utilise `simp [Complex.ext_iff]; omega` (détour par l'extensionnalité). Les trois ferment le même goal, mais seul `push_cast` *nomme l'opération* "pousser la coercion".
- Cette différenciation est mécaniquement détectable: `lean_multi_attempt` confirme que `push_cast; ring` ferme le but du cast, là où `simp_all`, `linarith`, `polyrith` (testés) ne ferment pas seuls.
- Le mapping mouvement-official solution → opération-Lean est traçable ligne-par-ligne pour transcription, traçable au niveau macro mais opaque au niveau micro pour Goedel.

Phrasing pour WDWFT (additif au phrasing P12):

> *La bidirectionalité résiste au choix de tactique idiomatique: sur P10.III.A.3.c (récurrence sur sommes finies de ℂ), le script transcription-fidèle inscrit la simplification de coercion comme `push_cast; ring` (deux tactiques nommées, chacune pour un mouvement distinct: pousser la coercion, normaliser la somme commutative). Le PASS Kimina ferme le même goal par `simp [Complex.ext_iff]; omega` — kernel-équivalent mais détourné par l'extensionnalité de ℂ. Le PASS Goedel utilise une cascade de 7 tactiques chaînées par `<;>` qui inclut `norm_cast`, `ring_nf`, `simp`, `norm_num`, `simp_all`, `linarith` — kernel-équivalent mais où aucune tactique individuelle ne nomme le mouvement effectif. Les trois sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel à la résolution sub-tactique.*
