# Myers-style transcription of Mercier-Rombaldi P10, question II.B.1

Le script Lean 4 `P10_subq_II_B_1_myers.lean` réalise les trois mouvements nommés du corrigé comme trois opérations Lean syntaxiquement distinctes, lisibles linéairement sans re-dérivation.

Le corrigé est lapidaire : « On vérifie facilement par récurrence que `α_k ≠ 0` pour tout `k ∈ ℕ`. » Il faut donc reconstruire les mouvements intermédiaires implicites : (1) base — `α_0 = 1/(1-λ) ≠ 0` car `λ ≠ 1`, conséquence de `λ ∉ 𝒜` (instance `k = 0` donne `1/(0+1) = 1`) ; (2) non-annulation du dénominateur récurrent — `D_n = 1 + (1 - 1/λ)·(1/n) = 0` impliquerait par chaîne algébrique `λ·(n+1) = 1`, donc `λ = 1/(n+1)`, contredisant `hlam_notA n` ; (3) récurrence — `α(k+1) = α k / D_{k+1}` avec `α k ≠ 0` (HR) et `D_{k+1} ≠ 0` (Move 2), donc `α(k+1) ≠ 0` par `div_ne_zero`. Ces trois mouvements sont inscrits respectivement comme `have h_one_sub_lam_ne_zero` (Move 1), `have h_denom_ne_zero` (Move 2), et `induction k with | zero => ... | succ k ih => ...` close par `div_ne_zero` (Move 3). Une lectrice qui parcourt le script rencontre exactement la structure « base → dénominateur → récurrence » que le corrigé laisse implicite.

Le mouvement 2 — la chaîne algébrique de `D_n = 0` à `λ = 1/(n+1)` — est la seule étape qui demande du calcul. Le corrigé ne l'écrit pas (« facilement par récurrence ») mais elle est nécessaire en Lean pour traverser la définition de `𝒜`. Elle est inscrite par deux `have` nommés : `h_mul_eq_one : lam * ((n : ℂ) + 1) = 1` (multiplication de `D_n = 0` par `λ·n` puis `field_simp` + `linear_combination`) et `h_lam_eq : lam = 1 / ((n : ℂ) + 1)` (division par `n+1` non nul). Ces deux opérations correspondent ligne-par-ligne à la chaîne « `D_n = 0 ⇒ λ·(n+1) = 1 ⇒ λ = 1/(n+1)` ». Aucun `<;>`, aucun `simp_all`, aucune hint-list — `field_simp` opère sur les hypothèses de non-nullité nommées (`hlam_ne_zero`, `hn_cast_ne`, `hsum_ne`), et `linear_combination` reçoit explicitement la combinaison.

L'hypothèse `hlam_re : (1/lam).re ≠ 1` est inutilisée (warning Lean) — comme dans les deux PASSes Goedel. Le corrigé l'introduit pour la branche II.B.4 (résolvante non vide), pas pour II.B.1.

## Self-classification

(a) — Faithful Myers transcription. Les trois mouvements corrigés correspondent à trois `have`/`induction` nommés ; la chaîne algébrique du dénominateur (Move 2) est inscrite en deux étapes nommées (`h_mul_eq_one`, `h_lam_eq`) au lieu d'être absorbée dans une cascade `simp_all <;> norm_num <;> linarith`. Le `field_simp` n'opère que sur des hypothèses explicitement nommées. Pas de `<;>`-chains.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier : 0 errors, 1 warning (`unused variable hlam_re` — fidèle au corrigé qui ne l'utilise pas non plus).
- `mcp__lean-lsp__lean_verify subq_II_B_1` : axiomes `[propext, Classical.choice, Quot.sound]` — pas de `sorryAx`, pas d'axiomes additionnels. Preuve kernel-vérifiée.
- `mcp__lean-lsp__lean_goal` à la ligne 97 (avant `div_ne_zero`) : `goals_before` `α k / (1 + (1 - 1/lam) * (1/↑(k+1))) ≠ 0` avec `ih : α k ≠ 0` et `h_denom_ne_zero` nommés en contexte ; `goals_after` `[]`. Fermeture propre par `div_ne_zero` agissant sur deux hypothèses nommées sans hint-list.

## Comparaison avec les deux Goedel PASSes

### Goedel att02 (137 lignes, 4495 chars, classifié (a) bruité)

Goedel att02 reproduit la structure trois-blocs (`h_one_sub_lam_ne_zero`, `h_denom_ne_zero`, `h_main` par induction). La différence est syntaxique :

- La chaîne algébrique du Move 2 est étalée sur deux `calc` imbriqués (12 lignes vs 4 chez Myers), avec cascades `field_simp [h₆] <;> ring_nf <;> simp_all [Complex.ext_iff] <;> norm_num <;> (try linarith)` à chaque étape. Le squelette `h₅ : (1 - 1/lam) = -(n : ℂ)` puis `h₆ : 1/lam = 1 + n` puis `h₇ : lam = 1/((n : ℂ) + 1)` est lisible mais bruité par les fallbacks RL.
- L'inversion `1/lam = 1 + n ⇒ lam = 1/(1+n)` passe par un sous-`calc` à deux étapes (`lam = 1 / (1/lam) = 1/(1+n)`) chez Goedel, alors que Myers la fait directement par `field_simp` + `linear_combination` sur `h_mul_eq_one`.
- Goedel utilise `Nat.sub_add_cancel` dans la simplification `α (k.succ - 1) = α k` ; Myers utilise `omega` sur `(k+1) - 1 = k` puis `rw`. Les deux sont valides ; Myers est plus court (1 ligne vs 3).
- Le close final est `div_ne_zero h₆ h₇` chez Goedel et `div_ne_zero ih (h_denom_ne_zero (k+1) hk1)` chez Myers — opération identique, mais Myers passe directement les hypothèses nommées sans alias intermédiaires.

Verdict : structure préservée à un niveau d'abstraction supérieur chez Myers ; Goedel est à 1.4× la longueur (137 vs 97 lignes) à cause des cascades `<;>`.

### Goedel att33 (184 lignes, 5595 chars, classifié (a) bruité)

Att33 est att02 + `by_contra` partout + cascades plus verbeuses. Le Move 2 utilise un `calc` à quatre étapes (vs trois chez att02, deux chez Myers) avec `(1 - 1/lam) = (1 - 1/lam) * 1 = (1 - 1/lam) * (k * (1/k)) = ...`. Inclut `nlinarith [sq_nonneg (lam.re - 1), sq_nonneg (lam.im), ...]` comme fallback dans le bloc dénominateur — shotgun complexe-arithmétique qui n'a aucun équivalent corrigé. Le préambule de raisonnement note explicitement « The condition `Re(1/λ) ≠ 1` is not actually used in the proof » — observation correcte, déjà incorporée dans Myers (qui laisse simplement le warning).

Verdict : att33 est att02 amplifié — plus de bruit, même squelette.

## Hiérarchie observée sur P10.II.B.1

| | base nommée | dénominateur (chaîne algébrique) | récurrence | classification | longueur |
|---|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `have h_one_sub_lam_ne_zero` via `hlam_notA 0` + `linear_combination` | `have h_mul_eq_one` + `have h_lam_eq` (2 étapes, `field_simp` propre) | `induction k with` + `div_ne_zero ih (h_denom_ne_zero (k+1) hk1)` | (a) parfait | 97 lignes |
| **Goedel att02** | `h_one_sub_lam_ne_zero` via `simpa` + `simp_all [Complex.ext_iff] <;> ...` | `calc` à 3 étapes + `calc` inversion à 2 étapes, cascades `<;>` partout | `induction k with` + `div_ne_zero h₆ h₇` | (a) bruité | 137 lignes |
| **Goedel att33** | `by_contra` + cascade verbeuse | `calc` à 4 étapes + `nlinarith [sq_nonneg ...]` fallback | idem att02 | (a) bruité | 184 lignes |
| **Kimina** | — (0/64 PASSes) | — | — | — | — |

Trois preuves kernel-équivalentes sur la branche (a). La gradation interne à (a) est observable : densité des cascades `<;>`, présence de fallbacks `nlinarith`/`simp_all` dans des sous-buts d'arithmétique complexe, longueur des `calc` chains. Myers occupe la position « (a) sans bruit RL » ; Goedel reproduit la structure mais l'enfouit sous du closure-tuning.

## Asymétrie d'arme : Kimina 0/64

Kimina ne produit aucun PASS sur II.B.1 — l'arme RL la plus shotgun-ée échoue exactement où la chaîne algébrique complexe-arithmétique exige une décomposition séquentielle (multiplication par `λ·n`, élimination des divisions, isolation de `λ`). Cette branche n'est pas accessible à un `nlinarith [...]` global. Goedel y arrive deux fois sur 64 par `calc` chains explicites mais bruités. Myers y arrive directement par `field_simp` + `linear_combination` sur des hypothèses nommées.

L'observation est prédictive : sur les sous-questions où le corrigé exige une chaîne algébrique multi-étapes en domaine non-réel (ici `ℂ` avec `field_simp` + coercions `ℕ → ℂ`), Kimina produit 0% PASS, Goedel produit (a) bruité, Myers produit (a) propre. Le critère bidirectionnel discrimine les trois régimes.

## Implications pour WDWFT

Cet artefact reproduit le pattern P12 sur un problème (P10.II.B.1) où :

1. **Le corrigé est lapidaire** (« facilement par récurrence ») et exige une expansion structurelle pour traverser la définition implicite de `𝒜` en Lean. Le critère bidirectionnel s'applique à l'expansion fidèle, pas seulement à la transcription verbatim.
2. **L'arme la plus shotgun-ée échoue** (Kimina 0/64). Là où le corrigé demande une dérivation algébrique explicite, le shotgun ne pénètre pas. La distinction (a) bidirectionnel / (c) opaque shotgun n'est pas seulement structurelle — elle est aussi épistémique : (c) ne peut tout simplement pas exister sur certaines branches.
3. **L'arme intermédiaire (Goedel) reproduit (a) avec bruit RL**. Le squelette est préservé mais étouffé sous des `<;>`-cascades. Une lectrice peut récupérer le mouvement, mais doit filtrer le bruit. Myers offre la baseline sans bruit.

Phrasing pour WDWFT (P10.II.B.1) :

> *Sur P10.II.B.1, le corrigé Mercier-Rombaldi tient en une phrase (« On vérifie facilement par récurrence »), mais l'expansion fidèle exige trois mouvements distincts : base via `λ ≠ 1` (instance de `λ ∉ 𝒜`), non-annulation du dénominateur via chaîne algébrique `D_n = 0 ⇒ λ = 1/(n+1)`, récurrence par `div_ne_zero`. Le script Myers les inscrit comme trois opérations Lean nommées sans cascade `<;>`. Goedel reproduit la structure avec bruit RL (1.4× à 1.9× la longueur). Kimina échoue intégralement (0/64). La gradation est mécaniquement vérifiable et auditable.*
