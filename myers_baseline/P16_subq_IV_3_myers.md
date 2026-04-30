# Myers-style transcription of Mercier-Rombaldi P16, question IV.3

The Lean 4 script at `P16_subq_IV_3_myers.lean` realises the corrigé's six named moves as six syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Corrigé text (Mercier-Rombaldi 2011, p. 16)

> Pour $y \neq x$, on a :
> $$\frac{F_k(y) - F_k(x)}{y - x} = \frac{f(y) - f(x)}{y - x} - k \in \left[m - k, M - k\right] = \left[-\frac{M - m}{2}, \frac{M - m}{2}\right]$$
> et donc :
> $$|F_k(y) - F_k(x)| \leq \frac{M - m}{2} |y - x|$$
> pour tout $(x, y) \in \mathbb{R}^2$.

The argument has a clear six-step structure:

1. **Case-split** on `x = y` (trivial) vs `x ≠ y`.
2. **Slope bound** `m ≤ (f y − f x)/(y − x) ≤ M` from hypothesis `(H)`.
3. **Midpoint algebra**: substituting `k = (m+M)/2` gives `slope − k ∈ [−(M−m)/2, (M−m)/2]`.
4. **`abs_le`** to convert the two-sided bound into `|slope − k| ≤ (M−m)/2`.
5. **Factor** `F y − F x = (slope − k) · (y − x)` (algebraic identity in the field).
6. **`abs_mul` + multiply** by the non-negative `|y − x|` to conclude.

## Bidirectional inscription

Each of the six moves is inscribed as a separate Lean operation, named or syntactically distinct:

| Move (corrigé) | Lean op | Named hypothesis |
|---|---|---|
| 1. Case-split | `by_cases hxy : x = y` + `subst hxy; simp` for the trivial branch | `hxy` |
| 2. Slope bound | `hH x y hxy` destructured into `.1` / `.2` | `h_slope_lo`, `h_slope_hi` |
| 3. Midpoint algebra (lower) | `rw [hk]; linarith` on numerical inequality | `h_dev_lo` |
| 3. Midpoint algebra (upper) | `rw [hk]; linarith` on numerical inequality | `h_dev_hi` |
| 4. `abs_le` | `abs_le.mpr ⟨h_dev_lo, h_dev_hi⟩` | `h_abs_dev` |
| 5. Factor | `rw [hF y, hF x]; field_simp; ring` (with `h_yx_ne` in context) | `h_factor` |
| 6. `abs_mul` + multiply | `rw [h_abs_factor]; exact mul_le_mul_of_nonneg_right h_abs_dev h_yx_abs_nn` | `h_abs_factor`, `h_yx_abs_nn` |

The script does **not** use `nlinarith`, `<;>`, `simp_all`, or `field_simp [show ... by nlinarith]` shotgun. The closing tactic is `mul_le_mul_of_nonneg_right` applied to two named hypotheses — bookkeeping over named facts, not search.

The midpoint computation `k = (m+M)/2 ⇒ m − k = −(M−m)/2 ∧ M − k = (M−m)/2` is left to `linarith` after `rw [hk]` substitutes the definition. This is the same "linarith on named numerical hypotheses" pattern as P12 (`linarith` on `h_id` and `h_sq`); the corrigé's "`m − k = −(M−m)/2`" is a trivial linear computation that any reverse-reader recognises as the named numerical content of `h_dev_lo` / `h_dev_hi`.

The factoring step (move 5) is the only one that requires algebraic massage. We invoke `field_simp` to clear the division `(f y − f x)/(y − x) · (y − x) = f y − f x` (legal because `h_yx_ne : y − x ≠ 0` is already in context — not synthesized inline by `nlinarith`), then `ring` for the polynomial normalisation. This matches the corrigé's bare assertion that the slope-times-denominator product *is* `f y − f x` modulo `k(y − x)`.

## Self-classification

(a) — Faithful Myers transcription. The script's six named operations are in bijection with the six named corrigé moves; the midpoint relation `m − k = −(M−m)/2` is delegated to `linarith` after explicit `rw [hk]`, not absorbed into a hint-list; `field_simp` operates only on the named hypothesis `h_yx_ne`, and the closing inequality is `mul_le_mul_of_nonneg_right` on two named bounds. The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings hors lints d'arguments inutilisés** (`hm`, `hM`, `hmM` figurent dans la signature du théorème pour fidélité au statement P16_concrete et ne peuvent pas être supprimées). Preuve kernel-vérifiée à la première itération.
- `mcp__lean-lsp__lean_goal` à la ligne 46 (juste avant la fermeture):
  - `goals_before`: contexte avec les 8 hypothèses nommées (`h_slope_lo`, `h_slope_hi`, `h_yx_ne`, `h_dev_lo`, `h_dev_hi`, `h_abs_dev`, `h_factor`, `h_abs_factor`, `h_yx_abs_nn`), but `|(f y - f x)/(y - x) - k| * |y - x| ≤ (M - m)/2 * |y - x|`
  - `goals_after`: `[]` — fermé par `mul_le_mul_of_nonneg_right h_abs_dev h_yx_abs_nn`, deux hypothèses nommées en argument
- `mcp__lean-lsp__lean_multi_attempt` à la ligne 29 (étape midpoint algebra lower bound): `rw [hk]; linarith` ferme; `linarith [hk]` ferme aussi (sans `rw`); `rw [hk]; nlinarith` ferme (mais `linarith` suffit). Le tactique minimal qui ferme dans le contexte nommé est `linarith` post-substitution — pas `nlinarith`.

## Comparaison directe avec scripts ML générés (parmi les 42 PASSes P16.subq_IV_3)

Selon `INDEX.md` du seed-robustness sweep:
- **Goedel**: 26 PASSes, dont 23/26 (88%) en route (a) — single by_cases + factor + abs_le.mpr + linarith — et 3/26 (12%) en route (b) — sign-split + nlinarith par branche.
- **Kimina**: 16 PASSes, dont 9/16 (56%) en route (a) et 7/16 (44%) en route (b).

### Goedel attempt 22 (PASS, route (a) compacte, classifié G-a1)

```lean4
have h_main : ∀ (x y : ℝ), |F y - F x| ≤ ((M - m) / 2) * |y - x| := by
  intro x y
  by_cases hxy : x = y
  · -- x = y branch: 14 lines of ring_nf <;> simp [hF] <;> ring_nf <;>
    --                simp <;> ring_nf <;> linarith bookkeeping
    ...
  · have h2 : F y - F x = ((f y - f x) / (y - x) - k) * (y - x) := by
      ...
      field_simp [h5, sub_ne_zero.mpr hxy]
      <;> ring_nf
      <;> field_simp [h5]
      <;> ring_nf
      <;> linarith
    rw [h2]
    have h3 : |((f y - f x) / (y - x) - k) * (y - x)| =
              |(f y - f x) / (y - x) - k| * |y - x| := by rw [abs_mul]
    rw [h3]
    have h4 : |(f y - f x) / (y - x) - k| ≤ (M - m) / 2 := by
      ...
      rw [abs_le]
      constructor <;> linarith
    have h5 : 0 ≤ (M - m) / 2 := by linarith
    have h6 : 0 ≤ |y - x| := abs_nonneg (y - x)
    calc
      |(f y - f x) / (y - x) - k| * |y - x| ≤ ((M - m) / 2) * |y - x| := by
        gcongr
      _ = ((M - m) / 2) * |y - x| := by ring
exact h_main
```

Goedel reproduit la structure (six mouvements distincts: `by_cases`, slope hyps, midpoint via `abs_le; constructor <;> linarith`, factor via `field_simp`, `abs_mul`, `gcongr`) mais ajoute du bruit syntaxique RL closure-tuning:

- Wrapper externe `have h_main := by ...; exact h_main` inutile — pure overhead RL.
- La cascade `field_simp <;> ring_nf <;> field_simp <;> ring_nf <;> linarith` au lieu de `field_simp; ring`.
- La branche `x = y` est traitée par 14 lignes de bookkeeping `ring_nf <;> simp <;> ring_nf <;> linarith` au lieu de `subst hxy; simp` (deux mouvements).
- Le calcul final passe par un `calc` avec deux lignes dont la seconde est `_ = ((M - m) / 2) * |y - x| := by ring` qui réécrit l'égalité réflexive.
- Conclusion via `gcongr` plutôt que `mul_le_mul_of_nonneg_right` nommé sur `h_abs_dev` et `h_yx_abs_nn` — `gcongr` est une tactique qui dérive automatiquement la monotonicité; nommer les deux côtés explicitement est plus bidirectionnel.

Verdict: structurellement préservé, syntaxiquement bruité (~3052 chars vs ~1860 chars Myers).

### Kimina attempt 09 (PASS, route (a) compacte, classifié K-a1)

```lean4
intro x y
have h1 : F y = f y - k * y := by apply hF
have h2 : F x = f x - k * x := by apply hF
have h3 : F y - F x = (f y - f x) - k * (y - x) := by rw [h1, h2]; ring
by_cases h : x = y
· rw [h]; simp
· have hxy : x ≠ y := by intro h_eq; apply h; all_goals linarith
  have h4 : m ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ M := hH x y hxy
  have h5 : m ≤ (f y - f x) / (y - x) := h4.1
  have h6 : (f y - f x) / (y - x) ≤ M := h4.2
  have hk' : k = (m + M) / 2 := hk
  have h13 : |(f y - f x) / (y - x) - (m + M) / 2| ≤ (M - m) / 2 := by
    have h11 : - (M - m) / 2 ≤ (f y - f x) / (y - x) - (m + M) / 2 := by nlinarith
    have h12 : (f y - f x) / (y - x) - (m + M) / 2 ≤ (M - m) / 2 := by nlinarith
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  have h14 : F y - F x = (y - x) * ((f y - f x) / (y - x) - (m + M) / 2) := by
    have hx : y - x ≠ 0 := by intro h_eq; apply hxy; linarith
    rw [h3, hk']
    field_simp [show y - x ≠ 0 by assumption]
    <;> ring
  have h15 : |F y - F x| = |y - x| * |(f y - f x) / (y - x) - (m + M) / 2| := by
    rw [h14]
    have h17 : |(y - x) * ((f y - f x) / (y - x) - (m + M) / 2)| =
               |y - x| * |(f y - f x) / (y - x) - (m + M) / 2| := by rw [abs_mul]
    simpa using h17
  rw [h15]
  nlinarith [abs_nonneg (y - x),
             abs_nonneg ((f y - f x) / (y - x) - (m + M) / 2), h13]
```

Kimina reproduit la structure compacte (sans `have h_main` wrapper) avec les six mouvements identifiables, mais utilise `nlinarith` à trois endroits où `linarith` suffit:

- `have h11 : - (M - m) / 2 ≤ ... := by nlinarith` — la borne midpoint est purement linéaire, `linarith [hk]` ou `rw [hk]; linarith` suffit.
- `have h12 : ... ≤ (M - m) / 2 := by nlinarith` — idem.
- Fermeture `nlinarith [abs_nonneg (y - x), abs_nonneg (...), h13]` — hint-list à trois éléments alors que `mul_le_mul_of_nonneg_right h13 (abs_nonneg _)` ferme directement (et sans hint-list).

Le mouvement `abs_le` est nommé (`apply abs_le.mpr; constructor; · linarith; · linarith`), donc la structure logique reste lisible. Mais l'usage de `nlinarith` masque ce qu'on peut faire avec `linarith` sur des hypothèses nommées.

Verdict: structurellement préservé, sur-puissance tactique sur trois étapes linéaires.

### Kimina attempt 01 (PASS, route (b), classifié K-b1)

```lean4
by_cases h : x = y
· rw [h]; simp
· ...
  by_cases h8 : y - x > 0
  · -- 22 lines: m * (y - x) ≤ f y - f x ≤ M * (y - x), then F y - F x bounds via nlinarith
    have h13 : |F y - F x| ≤ ( (M - m) / 2 ) * |y - x| := by
      have h14 : |y - x| = y - x := by rw [abs_of_pos h8]
      have h17 : |F y - F x| ≤ ( (M - m) / 2 ) * (y - x) := by
        apply abs_le.mpr; constructor; · nlinarith; · nlinarith
      rw [h14] at *
      all_goals nlinarith
    exact h13
  · have h8' : y - x < 0 := by ... push_neg ... tauto
    -- 22 more lines symmetric to above
```

Kimina (b) introduit un secondary by_cases sur `sign(y - x)` que le corrigé évite explicitement. Le corrigé écrit:

> $\dfrac{F_k(y) - F_k(x)}{y - x} = \dfrac{f(y) - f(x)}{y - x} - k \in [-(M-m)/2, (M-m)/2]$

c'est-à-dire qu'il borne *le quotient*, pas le numérateur. La borne sur le quotient ne dépend pas du signe de `y - x`. La factorisation `F y - F x = (slope - k) · (y - x)` puis `abs_mul` est exactement ce qui permet d'éviter le case-split sur le signe.

Kimina (b) construit à la place:
- `m * (y - x) ≤ f y - f x ≤ M * (y - x)` si `y - x > 0`,
- `M * (y - x) ≤ f y - f x ≤ m * (y - x)` si `y - x < 0`,

puis dérive séparément `F y - F x ≥ -(M-m)/2 · (y-x)` et `F y - F x ≤ (M-m)/2 · (y-x)` par `nlinarith` dans chaque branche, et utilise `abs_of_pos` / `abs_of_neg` pour passer à `|y - x|`. Le mouvement corrigé "borne sur le quotient" n'est jamais inscrit. Une lectrice ne peut pas reconstituer le passage clé du corrigé depuis ce script — le texte parle d'un quotient borné, le script parle d'un numérateur borné par signe.

Verdict: route (b) — la structure logique est lisible (deux branches signe + abs_le par branche) mais le mouvement clé du corrigé (borne sur le quotient `(f y - f x)/(y - x) - k`) n'apparaît pas. La ligne directe corrigé→Lean est rompue à l'étape 3.

## Hiérarchie observée sur P16.subq_IV_3

| | case-split | slope bound | midpoint algebra | abs_le | factor | abs_mul + close | classification |
|---|---|---|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `by_cases hxy: x = y; subst+simp` | `h_slope := hH x y hxy` destructuré | `rw [hk]; linarith` × 2 nommé | `abs_le.mpr ⟨h_dev_lo, h_dev_hi⟩` | `field_simp; ring` sur `h_yx_ne` | `mul_le_mul_of_nonneg_right h_abs_dev h_yx_abs_nn` | (a) parfait |
| **Goedel att22 (a)** | `by_cases` + 14 lignes ring_nf cascades | `hH x y hxy` destructuré | `abs_le; constructor <;> linarith` (deux étapes en une) | absorbé dans `abs_le; constructor` | `field_simp <;> ring_nf <;> ...` cascade | `gcongr` + `calc` overhead | (a) bruité |
| **Kimina att09 (a)** | `by_cases` + `simp` | `hH x y hxy` destructuré | `nlinarith` × 2 alors que `linarith` suffit | `abs_le.mpr; constructor; linarith` | `field_simp [show ... by assumption]; <;> ring` | `nlinarith [abs_nonneg, h13]` hint-list | (a) sur-puissant |
| **Kimina att01 (b)** | `by_cases` + secondary `by_cases h8 : y - x > 0` | `hH x y hxy` destructuré | absent — remplacé par sign-split + linear bounds sur f y − f x | `abs_le.mpr; constructor; nlinarith; nlinarith` par branche | absent — remplacé par `m*(y-x) ≤ f y − f x ≤ M*(y-x)` par signe | `abs_of_pos`/`abs_of_neg` + `nlinarith` par branche | (b) lower-abstraction |

Quatre preuves kernel-équivalentes. Quatre profils bidirectionnels distincts. La gradation (a-parfait → a-bruité → a-sur-puissant → b-lower-abstraction) est observable par lecture, mécaniquement vérifiable par lean-lsp (présence/absence des `have` nommés à chaque étape, choix du closer minimal vs `nlinarith`/`gcongr`), et auditable.

## Implications

### Pour AITP v7

1. **La métrique se reproduit sur P16**: avec un humain (Claude jouant Myers) en input + instruction "transcription fidèle", la sortie est (a) parfait au premier essai, kernel-vérifiée, six mouvements en bijection avec les six mouvements du corrigé. Cohérent avec P12 et P11.
2. **L'écart Goedel/Kimina sur la route (a) confirmé**: 88% Goedel route-(a) vs 56% Kimina, avec divergence de profil — Goedel (a) clusters à 2299–3240 chars (cascades RL), Kimina (a) à 1887–2363 chars mais utilisation systématique de `nlinarith` là où `linarith` suffirait. Aucun PASS dans aucune des deux arms ne descend au-dessous de ~1860 chars du Myers humain.
3. **Route (b) Kimina est l'évasion par la force brute**: les 7/16 PASSes Kimina (b) introduisent un sign-split que le corrigé évite; le mouvement clé (borne sur le quotient) disparaît. C'est l'inversion structurelle attendue — Kimina trouve un certificat alternatif que `nlinarith` peut exploiter, plutôt que de suivre l'argument.
4. **Ground truth artefact**: ce fichier `.lean` rejoint les baselines P11, P12 dans le repo de bidirectionalité, kernel-vérifié et auditable.

### Pour WDWFT

Cet artefact répond au point que P16.subq_IV_3 est un test plus dur que P12 — six mouvements au lieu de trois, division réelle, valeur absolue, factor non-trivial:

- Le script Myers est mécaniquement vérifiable (kernel + lean-lsp `lean_goal` confirme la fermeture par `mul_le_mul_of_nonneg_right` sur deux hypothèses nommées sans hint-list).
- Le mapping mouvement-corrigé → opération-Lean est traçable ligne-par-ligne sur six étapes.
- La distinction Myers / Goedel-(a) / Kimina-(a) / Kimina-(b) est *structurelle* (présence/absence d'un `have` nommé pour chaque mouvement, choix du closer minimal), pas *stylistique*.
- Le critère bidirectionnel n'est pas saturé par bruit de mesure — la cible Myers reste plus compacte que tous les PASSes ML, et chaque divergence (ring_nf cascades chez Goedel, nlinarith systématique chez Kimina, sign-split chez Kimina-b) est diagnostiquable.

Phrasing pour WDWFT (à itérer avec P11, P12, P16):

> *La bidirectionalité d'un script tactique se mesure par la préservation des mouvements nommés du corrigé comme opérations Lean nommées, et par le choix du closer minimal compatible avec le contexte nommé. Sur P16.IV.3 (`|F y − F x| ≤ ((M−m)/2)|y − x|`, six mouvements corrigés), le script Myers-fidèle inscrit chacun en un `have` ou un appel de lemme, ferme par `mul_le_mul_of_nonneg_right` sur deux hypothèses nommées (1860 chars). Le script Goedel typique reproduit la structure avec wrapper `h_main`, cascades `ring_nf <;> field_simp <;> ...`, et closer `gcongr` sur calc à deux lignes (~3000 chars). Le script Kimina (a) typique conserve la structure mais utilise `nlinarith` sur des étapes purement linéaires (~2000 chars). Le script Kimina (b) typique introduit un sign-split sur `y − x` que le corrigé évite explicitement — le mouvement clé "borne sur le quotient" disparaît, remplacé par deux branches de `nlinarith` sur `m·(y−x) ≤ f y − f x ≤ M·(y−x)` (~5000 chars). Les quatre scripts sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel sans dette tactique.*
