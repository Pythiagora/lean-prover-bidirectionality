# Solution transcription of Mercier-Rombaldi P8, sub-question A.1.a

The Lean 4 script at `P8_subq_A_1_a.lean` realises the official solution's two named moves as two syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

The official solution argument fits in two French sentences (page 272): "*Une matrice $M$ de $\mathrm{GL}_n(\mathbb{Z})$ est inversible, à coefficients dans $\mathbb{Z}$, et d'inverse $M^{-1}$ à coefficients dans $\mathbb{Z}$. On a $MM^{-1} = I$ [...] donc $\det M \times \det(M^{-1}) = 1$, et comme $\det M$ et $\det(M^{-1})$ sont des entiers relatifs, $\det M = \pm 1$.*" The first sentence delivers the claim "`det M` est un entier inversible". The second extracts ±1 from "les inversibles de ℤ sont exactement ±1". Each move maps to a single named Lean operation. Move 1 — `det M : ℤˣ` is the determinant homomorphism `GL (Fin n) ℤ → ℤˣ`; its underlying `IsUnit` witness is `M.det.isUnit`. This is inscribed as `have h_unit : IsUnit ((M : Matrix (Fin n) (Fin n) ℤ).det) := M.det.isUnit`. The dot-projection compresses two facts the official solution separates ("M est inversible" + "det est un morphisme `GL → ℤˣ`") into one term, but the resulting hypothesis is exactly the *content* of the official solution's first sentence. Move 2 — `Int.isUnit_iff : IsUnit n ↔ n = 1 ∨ n = -1` is the Mathlib statement of "les inversibles de ℤ sont exactement ±1". The script closes with `exact Int.isUnit_iff.mp h_unit`. A reverse-reader meets the official solution's two sentences in order: unit-of-ℤ, then ±1.

## Self-classification

**(a) — Faithful transcription.** The script's two operations are in bijection with the two named official solution moves; no automation tactic is invoked (no `tauto`, no `simp`, no `aesop`, no `decide`, no `<;>`); each move uses a single named Mathlib lemma (`Units.isUnit` via dot-notation through `M.det`, then `Int.isUnit_iff`). The two-line core is the minimal route through the official solution's argument as expressed in Mathlib v4.30.0-rc2.

A note on `M.det.isUnit` vs the alternative `(Matrix.isUnit_iff_isUnit_det _).mp M.isUnit`: both produce the same hypothesis. The dot-projection version compresses the inference because `Matrix.GeneralLinearGroup` is *defined* in Mathlib as `(Matrix _ _ R)ˣ`, with a built-in determinant map `det : GL n R → Rˣ` realised as `Units.map (detMonoidHom)`. The longer version makes the `IsUnit M → IsUnit (det M)` step explicit. Both are bidirectional; the chosen form is shorter and semantically equivalent.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée).
- `mcp__lean-lsp__lean_verify subq_A_1_a`: axioms = `[propext, Classical.choice, Quot.sound]` (les trois standards Mathlib, **pas de `sorryAx`**).
- `mcp__lean-lsp__lean_goal`:
  - ligne 10 (avant move 1): `goals_before = ⊢ (↑M).det = 1 ∨ (↑M).det = -1`.
  - ligne 13 (sur `exact Int.isUnit_iff.mp h_unit`): `goals_before = h_unit : IsUnit (↑M).det ⊢ (↑M).det = 1 ∨ (↑M).det = -1`; `goals_after = []`.
- `mcp__lean-lsp__lean_multi_attempt`: la formulation alternative `(Matrix.isUnit_iff_isUnit_det _).mp M.isUnit` ferme aussi le but mais déclenche un warning `linter.style.longLine` (>100 char). La formulation `M.det.isUnit` retenue ne déclenche aucun warning et compresse la même inférence en moins de tokens.

## Comparaison directe avec scripts ML générés (parmi les 14 PASSes P8.subq_A_1_a)

### Goedel attempt 26 (PASS, classifié G-a1 par sub-agent — route préservée)

```lean4
theorem subq_A_1_a {n : ℕ} (M : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
  have h₁ : IsUnit ( (M : Matrix (Fin n) (Fin n) ℤ).det ) := by
    have h : IsUnit (M : Matrix (Fin n) (Fin n) ℤ) := M.isUnit
    have h₂ : IsUnit ( (M : Matrix (Fin n) (Fin n) ℤ).det ) :=
      Matrix.isUnit_iff_isUnit_det _ |>.mp h
    exact h₂
  have h₂ : (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
    have h₃ : (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
      rw [Int.isUnit_iff] at h₁
      tauto
    exact h₃
  exact h₂
```

Goedel reproduit la structure (un `have` pour `IsUnit (det M)`, un `have` pour la disjonction, fermeture par `Int.isUnit_iff`) mais ajoute du bruit syntaxique:

- L'inversion `M.isUnit → Matrix.isUnit_iff_isUnit_det → IsUnit (det M)` est explicitée en deux `have` imbriqués au lieu d'une projection en chaîne. La sémantique est identique à `M.det.isUnit`, mais le script Goedel re-prouve à chaque `have` que la conclusion intermédiaire est la conclusion suivante (pattern `have h₃ := ...; exact h₃`).
- La fermeture `rw [Int.isUnit_iff] at h₁; tauto` substitue à la version transcription `Int.isUnit_iff.mp h_unit`. Une utilisation de `tauto` (résolveur propositionnel) est ajoutée là où l'élimination directe par `.mp` suffit.
- Pattern RL signature: chaque `have` est suivi d'un `exact` redondant qui fait passer une hypothèse à un nom déjà visible. 5 `have` au total pour ce que le script transcription fait en 1.

Verdict: structurellement préservé, syntaxiquement bruité par le tuning RL. Reverse-reading reste possible mais alourdi.

### Kimina attempt 59 (PASS, classifié K-b par sub-agent — détour par bornes)

```lean4
theorem subq_A_1_a {n : ℕ} (M : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
  have h1 : IsUnit ((M : Matrix (Fin n) (Fin n) ℤ).det : ℤ) := by
    exact M.2
  have h16 : (M : Matrix (Fin n) (Fin n) ℤ).det = 1 ∨ (M : Matrix (Fin n) (Fin n) ℤ).det = -1 := by
    have h17 : IsUnit ((M : Matrix (Fin n) (Fin n) ℤ).det : ℤ) := h1
    have h18 : (M : Matrix (Fin n) (Fin n) ℤ).det ≤ 1 := by
      apply Int.le_of_dvd (show 0 < (1 : ℤ) by norm_num) (IsUnit.dvd_one h17)
    have h19 : (M : Matrix (Fin n) (Fin n) ℤ).det ≥ -1 := by
      have h20 : -( (M : Matrix (Fin n) (Fin n) ℤ).det ) ∣ 1 :=
        Int.neg_dvd.2 (IsUnit.dvd_one h17)
      have h21 : -( (M : Matrix (Fin n) (Fin n) ℤ).det ) ≤ 1 :=
        Int.le_of_dvd (show 0 < (1 : ℤ) by norm_num) h20
      omega
    interval_cases h : (M : Matrix (Fin n) (Fin n) ℤ).det <;> tauto
  exact h16
```

Kimina réussit le move 1 *plus compactement* que Goedel (`exact M.2` extrait directement le champ `IsUnit` du record `Units`, équivalent à `M.det.isUnit` modulo une indirection). Mais le move 2 *abandonne la caractérisation* "les inversibles de ℤ sont ±1" et la remplace par une preuve de bornes:

- Borne supérieure: `det M ≤ 1` via `IsUnit.dvd_one + Int.le_of_dvd`.
- Borne inférieure: `det M ≥ -1` via `Int.neg_dvd + Int.le_of_dvd + omega`.
- Énumération: `interval_cases <;> tauto` énumère `det M ∈ {-1, 0, 1}` puis élimine `det M = 0` par `tauto` (qui voit la contradiction avec `IsUnit 0`).

Le mouvement official solution "*comme $\det M$ et $\det M^{-1}$ sont des entiers relatifs, $\det M = \pm 1$*" — qui invoque implicitement la classification des inversibles de ℤ — *n'est jamais inscrit*. Une lectrice voit le bound-squeezing arriver à ±1 mais ne voit pas que ce résultat suit d'une caractérisation des inversibles de ℤ comme fait mathématique nommé. La preuve est kernel-équivalente, mais la trace logique est *re-routée* à travers de l'arithmétique de divisibilité que le official solution n'utilise pas.

Verdict: move 1 préservé, move 2 occlus. La preuve passe le critère "kernel-vérifié" mais échoue le critère "bidirectionnel".

## Hiérarchie observée sur P8.subq_A_1_a

| | move 1 (`IsUnit (det M)`) | move 2 (caractérisation ℤ-units) | n_lignes | classification |
|---|---|---|---:|---|
| **transcription (Claude/lean-lsp)** | `M.det.isUnit` (1 terme) | `Int.isUnit_iff.mp` (1 terme) | 2 (hors commentaires) | (a) parfait |
| **Goedel att26** | `Matrix.isUnit_iff_isUnit_det.mp M.isUnit` (3 `have`) | `rw [Int.isUnit_iff]; tauto` | 13 (avec `have` redondants) | (a) bruité |
| **Kimina att59** | `M.2` (1 terme, route alternative `Units → IsUnit`) | borne sup + borne inf + `interval_cases <;> tauto` | 14 (avec arithmétique bornes) | (b) opaque sur move 2 |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts. Sur cette sub-question, l'inversion v6 se manifeste sur le **move 2**: Goedel le préserve avec bruit, Kimina l'occlut entièrement par bound-squeezing.

## Implications

### Pour AITP v7

1. **La métrique distingue trois niveaux de bidirectionalité même sur une sub-question à deux mouvements.** P8.subq_A_1_a est l'une des sub-questions les plus courtes du jeu de données (le official solution tient en deux phrases) — et pourtant la trichotomie (a)/(a-bruité)/(b) reste nette.

2. **Le contraste Goedel(a)/Kimina(b) sur cette sub-question répète le pattern observé sur P12.** Goedel reproduit la structure official solutione avec bruit syntaxique RL; Kimina re-route via de l'arithmétique tactique (`interval_cases` ici, `nlinarith` shotgun ailleurs). La différence de profil bidirectionnel n'est pas un artefact d'une sub-question particulière.

3. **Le "two-line ideal" est atteignable.** Sur P8.subq_A_1_a, le official solution tient en deux phrases et le script transcription tient en deux lignes Lean. La compressibilité du script suit la compressibilité du official solution. Cela suggère une heuristique opérationnelle: pour les sub-questions courtes, mesurer `n_have_official solution` vs `n_have_lean` détecte les déviations bidirectionnelles. Sur P8.subq_A_1_a, Goedel produit 5 `have` pour 2 phrases official solution (ratio 2.5×); Kimina produit 6 `have` pour 2 phrases official solution (ratio 3×); transcription produit 1 `have` + 1 `exact` pour 2 phrases official solution (ratio 1×).

### Pour WDWFT

Cet artefact répond directement à l'objection "la bidirectionalité dépend du choix d'API Mathlib":

- Le script transcription utilise `M.det.isUnit` — la projection la plus courte de Mathlib. Goedel utilise `Matrix.isUnit_iff_isUnit_det` — un lemme plus verbeux mais explicitement nommé. Les deux scripts sont bidirectionnels (move 1 préservé). La différence est *quantitative* (n_tokens), pas *catégorielle*.
- Kimina utilise `IsUnit.dvd_one + Int.le_of_dvd + interval_cases` — un détour par l'arithmétique de divisibilité que le official solution n'utilise *jamais*. Le script kimina passe à un *registre logique différent* du official solution. La différence est *catégorielle* (move 2 absent comme caractérisation explicite des ℤ-units).

Phrasing pour WDWFT (résolution P8.subq_A_1_a):

> *Sur la sub-question A.1.a (Mercier-Rombaldi P8), le official solution tient en deux phrases françaises: (1) "`det M` est un entier inversible"; (2) "les inversibles de ℤ sont ±1". Le script transcription fidèle (`have h_unit := M.det.isUnit; exact Int.isUnit_iff.mp h_unit`) inscrit chaque phrase comme un terme Lean nommé. Le script Goedel typique (att26) reproduit la structure avec une cascade de `have` RL-bruités. Le script Kimina typique (att59) préserve la phrase (1) mais remplace la phrase (2) par un argument de bornes (`Int.le_of_dvd + interval_cases <;> tauto`) qui n'apparaît pas dans le official solution. Les trois scripts sont kernel-équivalents. Seul le premier (et, modulo bruit, le second) satisfait le critère bidirectionnel sur les deux mouvements.*
