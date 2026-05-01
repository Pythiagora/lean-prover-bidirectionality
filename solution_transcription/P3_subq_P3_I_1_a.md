# Solution transcription of Mercier-Rombaldi P3, question I.1.a (Weierstrass)

The Lean 4 script at `P3_subq_P3_I_1_a.lean` realises the Mercier-Rombaldi official solution's six named moves as six syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Statement

For `θ ∈ [0, π/2]` and `t = tan(θ/2)`:

1. `cos θ = (1 - t²) / (1 + t²)`
2. `sin θ = 2t / (1 + t²)`
3. If `t = q ∈ ℚ`, then both `cos θ` and `sin θ` are in ℚ.

## Official solution text (Mercier-Rombaldi §3.2, paragraphe 1.1.a, page 95)

> **1.1.a.** On connaît les formules
>     x = cos θ = (1 - t²) / (1 + t²)   et   y = sin θ = 2t / (1 + t²).
> Si t ∈ ℚ, x et y sont les quotients de deux rationnels : ce sont donc des rationnels.
>
> **Remarque** — On utilise le fait que ℚ est un corps. Si t ∈ ℚ, 1 - t² et 1 + t² aussi, donc l'inverse 1/(1 + t²) aussi, et le produit x = (1 - t²) × [1/(1 + t²)] est encore dans ℚ. On raisonne de la même façon avec y.

The official solution treats the two Weierstrass identities as known (`On connaît les formules`) and offers a *Remarque* unfolding the rationality clause through the field structure of ℚ. The tacit derivation underlying the formulas — the one a student is expected to reproduce on demand — is the standard one: use the double-angle identities `cos(2α) = cos²α - sin²α` and `sin(2α) = 2 sin α cos α` at α = θ/2, divide numerator and denominator by `cos²(θ/2)`, and recognise the Pythagorean identity `cos²(θ/2) + sin²(θ/2) = 1` in the denominator. The side condition `cos(θ/2) ≠ 0` follows from `θ/2 ∈ [0, π/4] ⊂ (-π/2, π/2)`.

## Six named official solution moves, six named Lean steps

The transcription script binds each official solution move to a single named Lean step:

| official solution move | Lean inscription | Mathlib hook |
|---|---|---|
| (M1) cos(2α) = cos²α - sin²α | `have hcos_2 : Real.cos θ = Real.cos (θ/2) ^ 2 - Real.sin (θ/2) ^ 2 := …` | `Real.cos_two_mul'` |
| (M2) sin(2α) = 2 sin α cos α | `have hsin_2 : Real.sin θ = 2 * Real.sin (θ/2) * Real.cos (θ/2) := …` | `Real.sin_two_mul` |
| (M3) sin²α + cos²α = 1 | `have hpyth : Real.sin (θ/2) ^ 2 + Real.cos (θ/2) ^ 2 = 1 := …` | `Real.sin_sq_add_cos_sq` |
| (M4) tan α = sin α / cos α | `have htan_eq : Real.tan (θ/2) = Real.sin (θ/2) / Real.cos (θ/2) := …` | `Real.tan_eq_sin_div_cos` |
| (M5) side condition cos(θ/2) > 0 | `have hcos_pos : 0 < Real.cos (θ/2) := by apply Real.cos_pos_of_mem_Ioo; …` | `Real.cos_pos_of_mem_Ioo` |
| (M6) ℚ closed under arithmetic | `refine ⟨⟨(1 - q²)/(1 + q²), …⟩, ⟨2q/(1 + q²), …⟩⟩` then `push_cast; ring` | `Rat` cast + `push_cast` |

A reverse-reader walking the script encounters exactly the official solution's named lemma list in order. The auxiliary identity `h_one_plus_tan_sq : 1 + tan²(θ/2) = 1/cos²(θ/2)` inscribes the official solution's tacit divide-by-`cos²(θ/2)` step *as a separate named hypothesis*, derived from M3 and M5. The final closure of each Weierstrass formula is `field_simp` under `hcos_ne` — this performs the polynomial-fraction normalisation the official solution would do on paper after dividing top and bottom by `cos²(θ/2)`, and is *not* a search-tactic invocation: `field_simp` is a normaliser whose decision procedure runs on the ring structure with named non-vanishing hypotheses.

The conjunction is split with `refine ⟨?_, ?_, ?_⟩`, each branch closed by reference to a single named Weierstrass lemma (`hcos_W`, `hsin_W`) and, for branch 3, by substitution `t = q` followed by `push_cast; ring`. No `<;>` chains, no `simp_all`, no `nlinarith` shotgun.

## Self-classification

(a) — Faithful transcription. The six named official solution moves appear as six named Lean hypotheses in the order the official solution presents them (or that the standard derivation underlying the official solution presents them); each `have` corresponds to a single sentence of the informal proof; closure of the two Weierstrass identities is by `field_simp` acting on already-named hypotheses, not by hint-list search; the rationality clause is closed by *exhibiting* the rational witnesses `(1 - q²)/(1 + q²)` and `2q/(1 + q²)` exactly as the official solution's *Remarque* describes ("le produit (1 - t²) × [1/(1 + t²)] est encore dans ℚ"). The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée).
- `mcp__lean-lsp__lean_verify subq_P3_I_1_a`: axiomes utilisés = `{propext, Classical.choice, Quot.sound}`. Aucun `sorry`, aucun axiome ad-hoc.
- `mcp__lean-lsp__lean_goal` à la ligne 88 (juste avant le `field_simp` qui ferme `hcos_W`):
  - `goals_before`:
    `cos (θ/2)² - sin (θ/2)² = (1 - (sin (θ/2) / cos (θ/2))²) / (1 / cos (θ/2)²)`
  - `goals_after`: `[]` — `field_simp` ferme. Le but est exactement la division-par-`cos²(θ/2)` du official solution, formellement: après les substitutions M1+M3+M4, on doit montrer que le membre de gauche (M1) égale le membre de droite (M3+M4 réarrangés). Le clearing des dénominateurs est l'unique normalisation nécessaire, sous l'hypothèse nommée `hcos_ne`.
- `mcp__lean-lsp__lean_goal` à la ligne 96 (juste avant le `simpa using hsin_W`): goal `sin θ = 2 * tan (θ/2) / (1 + tan (θ/2)²)` — fermé par `simpa` (déplie le `let t := …` introduit par la signature).

## Comparaison directe avec scripts ML générés (parmi les 18 PASSes P3.subq_P3_I_1_a)

### Goedel attempt 30 (PASS, classifié route-preserving par sub-agent)

```lean4
have hcos_θ : Real.cos θ = (1 - (Real.tan (θ / 2)) ^ 2) / (1 + (Real.tan (θ / 2)) ^ 2) := by
  have h₁ : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring
  rw [h₁]
  have h₂ : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [Real.cos_two_mul]
    <;> ring_nf
    <;> simp [Real.cos_sq]
    <;> ring_nf
  rw [h₂]
  ...
  field_simp [h₅.ne']
  <;> nlinarith [Real.sin_sq_add_cos_sq (θ / 2), Real.sin_le_one (θ / 2),
                 Real.cos_le_one (θ / 2)]
```

Goedel reproduit la structure (deux `have` pour M1 + non-vanishing, fermeture `field_simp + nlinarith [hpyth, ...]`) mais ajoute du bruit syntaxique:

- Cascade `<;> ring_nf <;> simp [Real.cos_sq] <;> ring_nf` après `rw [Real.cos_two_mul]` — inutile, `Real.cos_two_mul'` ferme directement (vérifié par lean-lsp).
- Ferme la dernière étape par `nlinarith [Real.sin_sq_add_cos_sq (θ/2), Real.sin_le_one, Real.cos_le_one]` au lieu de la simple normalisation `field_simp` qui suffit après le rewrite via `h_one_plus_tan_sq`. Les bornes `sin_le_one` et `cos_le_one` ne servent à rien et sont des hint-list pollution typique du closure-tuning RL.
- Goedel utilise `Real.cos_two_mul` (forme `2 cos²α - 1`) plutôt que `Real.cos_two_mul'` (forme `cos²α - sin²α` que le official solution utilise littéralement). Les deux sont kernel-équivalents mais la forme `'` est verbatim au texte du official solution, donc préserve mieux la lisibilité bidirectionnelle.

Verdict: structurellement préservé, syntaxiquement bruité (`<;>` cascades, hint-list inutile), nommage M1 sub-optimal (`cos_two_mul` au lieu de `cos_two_mul'`).

### Kimina attempt 01 (PASS, classifié route-preserving par sub-agent)

```lean4
have h7 : Real.cos (2 * (θ / 2)) = (1 - (t) ^ 2) / (1 + (t) ^ 2) := by
  ...
  have h11 : (1 - (t) ^ 2) / (1 + (t) ^ 2) = 2 * (Real.cos (θ / 2)) ^ 2 - 1 := by
    rw [ht1]
    have htan2 : Real.tan (θ / 2) = Real.sin (θ / 2) / Real.cos (θ / 2) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan2]
    have h13 : (1 - (Real.sin (θ / 2) / Real.cos (θ / 2)) ^ 2) /
               (1 + (Real.sin (θ / 2) / Real.cos (θ / 2)) ^ 2)
             = ( (Real.cos (θ / 2)) ^ 2 - (Real.sin (θ / 2)) ^ 2 )
             / ( (Real.cos (θ / 2)) ^ 2 + (Real.sin (θ / 2)) ^ 2 ) := by
      field_simp [show Real.cos (θ / 2) ≠ 0 by linarith]
      all_goals nlinarith
    rw [h13]
    have h14 : (Real.cos (θ / 2)) ^ 2 + (Real.sin (θ / 2)) ^ 2 = 1 := Real.cos_sq_add_sin_sq (θ / 2)
    have h15 : (Real.cos (θ / 2)) ^ 2 - (Real.sin (θ / 2)) ^ 2
             = 2 * (Real.cos (θ / 2)) ^ 2 - 1 := by nlinarith
    rw [h14, h15]
    all_goals field_simp [h14]
  ...
```

Kimina reproduit également la structure (M1, M3, M4, M5 tous nommés). Mais la preuve duplique massivement: la chaîne complète (tous les bornages θ/2 ∈ [0, π/4], le calcul `cos(θ/2) > 0`, la dérivation Weierstrass elle-même) est *réinscrite intégralement* dans le bloc de la rationalité (lignes 666-757 du `attempt_01.md`), au lieu d'être réutilisée par référence aux `have` antérieurs. Le script final fait 762 lignes pour un théorème que le official solution fait en deux phrases.

- `all_goals nlinarith` apparaît deux fois en fermeture `field_simp` — non nécessaire (la `field_simp` seule suffit dans la version transcription), trace de la stratégie RL closure-tuning Kimina.
- `nlinarith` ferme `(cos)² - (sin)² = 2(cos)² - 1` qui est une identité polynomiale immédiate (`linear_combination hpyth` ou `linarith [hpyth]` suffit, sans recours à la recherche tactique nonlinéaire).
- Chaque sous-but de la rationalité (`Real.cos θ = (1-q²)/(1+q²)`) re-démontre toute la dérivation Weierstrass au lieu de réutiliser `hcos_W`. C'est un anti-pattern bidirectionnel typique: le script ne *réfère* pas au official solution "comme on l'a vu", il *réinscrit* le official solution. Un lecteur bidirectionnel doit lire la même dérivation trois fois.

Verdict: structurellement préservé, mais redondance massive (duplication de M1-M5 trois fois) et fermetures par `nlinarith`/`all_goals` même quand `linarith [hpyth]` ou `field_simp` seul suffirait. Bruit RL syntaxique élevé.

## Hiérarchie observée sur P3.subq_P3_I_1_a

| | M1 cos₂ | M2 sin₂ | M3 pyth | M4 tan | M5 cos>0 | M6 rationalité | redondance | fermeture des Weierstrass |
|---|---|---|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `cos_two_mul'` (verbatim) | `sin_two_mul` | `sin_sq_add_cos_sq` | `tan_eq_sin_div_cos` | `cos_pos_of_mem_Ioo` | witnesses + `push_cast; ring` | aucune (M1-M5 introduits une seule fois) | `field_simp` après rewrite via `h_one_plus_tan_sq` |
| **Goedel att30** | `cos_two_mul` (forme `2cos²-1`) + cascade `<;>` | `sin_two_mul` | absorbé dans `nlinarith`-hint | `tan_eq_sin_div_cos` | `cos_pos_of_mem_Ioo` + cascade `<;>` | witnesses + cascade `<;> norm_cast <;> field_simp <;> ring_nf <;> norm_cast` | aucune | `field_simp + nlinarith [hpyth, sin_le_one, cos_le_one]` |
| **Kimina att01** | `cos_two_mul` × 3 occurrences | `sin_two_mul` × 2 | `cos_sq_add_sin_sq` × 3 | `tan_eq_sin_div_cos` × 3 | `cos_pos_of_mem_Ioo` × 3 | witnesses + `simp [h]` | massive (3× M1-M5) | `field_simp + all_goals nlinarith` × 4 |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts:

- **transcription**: chaque mouvement official solution apparaît exactement une fois, en `have` nommé, dans l'ordre du official solution. Lecteur bidirectionnel rencontre le official solution une fois.
- **Goedel**: chaque mouvement apparaît une fois, mais bruité syntaxiquement (`<;>` cascades, hint-list `nlinarith`). Lecteur bidirectionnel rencontre le official solution une fois mais doit traverser le bruit.
- **Kimina**: chaque mouvement apparaît trois fois (M1-M5 dupliqués dans chaque sous-but de la conjonction). Lecteur bidirectionnel rencontre le official solution répété trois fois.

## Implications

### Pour AITP v7

1. **La métrique route-preserving 100% sur P3.subq_P3_I_1_a sous-spécifie**. Les 18 PASSes (12 Goedel + 6 Kimina) sont tous classés route-preserving car ils invoquent les hooks `cos_two_mul`, `sin_two_mul`, `tan_eq_sin_div_cos`. Mais la *qualité* de la transcription bidirectionnelle varie radicalement (cf. tableau ci-dessus). Une métrique de fine-graining nécessaire — par exemple: nombre d'occurrences de chaque hook (1 = optimal, ≥ 2 = duplication), ratio script_lines / 30 (transcription ~ 60 lignes ≈ 2; Kimina att01 ~ 760 lignes ≈ 25).
2. **L'inversion v6 confirmée à plus haute résolution**: Goedel approche le upper bound transcription (modulo bruit syntaxique RL), Kimina s'en éloigne par duplication massive. Sur P3.subq_P3_I_1_a la divergence est dans la *redondance* plutôt que dans l'absence du mouvement.
3. **Ground truth artefact**: ce fichier `.lean` peut être publié dans le repo `lean-prover-bidirectionality` comme baseline P3.subq_P3_I_1_a, kernel-vérifié et auditable.

### Pour WDWFT

Cet artefact répond directement à l'objection "deux preuves route-preserving sont équivalentes":

- Le script transcription est mécaniquement vérifiable (kernel + lean-lsp `lean_goal` confirme la fermeture par hypothèses nommées sans hint-list, M1-M5 chacun introduits une seule fois).
- Le script Kimina att01 est *aussi* route-preserving au sens hooks-invoked, mais inscrit M1-M5 *trois fois* dans la même preuve. C'est un défaut bidirectionnel: la preuve ne réutilise pas son propre travail. Un lecteur ne peut pas lire le script comme un développement linéaire du official solution.
- Le script Goedel est intermédiaire: structure correcte mais bruit syntaxique (`<;>` cascades, hint-list `nlinarith`).

Phrasing pour WDWFT (à intégrer dans la section sur les profils bidirectionnels):

> *La métrique "route-preserving" capture l'invocation des lemmes official solution mais sous-spécifie sur deux dimensions: (i) l'unicité d'inscription — un script transcription nomme chaque mouvement official solution une fois, un script Kimina peut le réinscrire à chaque sous-but —, et (ii) le bruit de fermeture — `field_simp` suffit après les rewrites nommés alors que les scripts RL ferment via `nlinarith [hint-list]`. Sur la sous-question P3.I.1.a (paramétrage de Weierstrass), la preuve transcription fait 60 lignes; la preuve Kimina att01 (kernel-équivalente, classée route-preserving) fait 760 lignes par duplication des cinq mouvements official solutions. Les trois critères — préservation de la route, unicité d'inscription, sobriété de fermeture — sont indépendants, et la conjonction des trois définit le standard bidirectionnel.*
