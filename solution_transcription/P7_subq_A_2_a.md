# Solution transcription of Mercier-Rombaldi P7, question A.2.a

The Lean 4 script at `P7_subq_A_2_a.lean` realises the official solution's named moves as syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Official solution content

Page 242: « Le degré de chaque sommet de $K_n$ est $n - 1$ donc:
$$L = \begin{pmatrix} 1 & -1/(n-1) & \cdots \\ \vdots & \ddots & \\ -1/(n-1) & \cdots & 1 \end{pmatrix} = \frac{n}{n-1} I - \frac{1}{n-1} J. $$ »

The official solution does *not* prove the equality entrywise — it proceeds by factorisation: factor out $-1/(n-1)$, recognise the bracketed matrix as $J - nI$, distribute. In Lean 4 + Mathlib, that route would need a non-trivial algebraic chain over `Matrix`-level rewrites, since `Matrix` is `Fin n → Fin n → ℝ` and the `(i,j)`-projection is the working layer. **No PASS in the rerun4 robustness corpus uses the abstract `smul`-decomposition route**; all 56 PASSes go entrywise. The transcription script also goes entrywise, but the named moves remain in bijection with the official solution's content: side-condition (degree $n-1$ ⇒ denominator nonzero), entrywise reduction, diagonal/off-diagonal split, arithmetic check.

## Named official solution moves and Lean correspondents

| # | Official solution move | Lean operation |
|---|---|---|
| 0 | "le degré de chaque sommet est $n - 1$" ⇒ `(n - 1) ≠ 0` in ℝ | `have h_n1 : (n : ℝ) - 1 ≠ 0 := by have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn; linarith` |
| 1 | matrix equality reduces to per-cell equality | `ext i j` |
| 2 | unfold `L_{ij}`, `I_{ij}`, `J_{ij}`, `(αI - βJ)_{ij}` | `simp only [L, J, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]` |
| 3 | dichotomy diagonal / off-diagonal | `by_cases h : i = j` |
| 4a | diagonal: `n/(n-1) - 1/(n-1) = (n-1)/(n-1) = 1` | `simp [h]; field_simp` |
| 4b | off-diagonal: `0 - 1/(n-1) = -1/(n-1)` | `simp [h]; ring` |

Each move is a distinct line; no `<;>` chains; no `try` blocks; no `all_goals`; no `nlinarith` hint-list. The side-condition `h_n1` is named once and consumed implicitly by `field_simp` in move 4a (where division is normalised). Move 4b is pure inverse-vs-division normalisation (`-1/x = -x⁻¹`) and needs no field hypothesis — `ring` suffices.

## Self-classification

(a) — Faithful transcription. The official solution's algebraic-factorisation route cannot be transcribed literally in Mathlib's matrix layer (no PASS in 56 attempts uses it), so the transcription script falls back on the entrywise route, which is the *next-most-faithful* transcription: every step in the script is a named move legible to a reader holding the official solution. The two arithmetic identities checked at the leaves (`n/(n-1) - 1/(n-1) = 1` and `0 - 1/(n-1) = -1/(n-1)`) are exactly the two equations the official solution would write if asked to verify entrywise. No automation is doing search — `field_simp` is doing fraction normalisation against the named hypothesis `h_n1`, and `ring` is doing inverse-vs-division equivalence.

A stricter (a*) classification would require the abstract `smul`-decomposition route. That route appears unreachable with current Mathlib API in a clean transcription form.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` on `P7.lean`: **0 errors, 0 warnings, 0 infos** (kernel-vérifié).
- `mcp__lean-lsp__lean_goal` à la ligne 22 (avant `simp only`): but `L i j = ((↑n / (↑n - 1)) • 1 - (1 / (↑n - 1)) • J) i j` — exactement la formulation entrywise du official solution.
- `mcp__lean-lsp__lean_goal` à la ligne 30 (avant `field_simp`, branche diagonale): but `1 = ↑n / (↑n - 1) - (↑n - 1)⁻¹` — l'identité arithmétique du official solution `n/(n-1) - 1/(n-1) = 1`.
- `mcp__lean-lsp__lean_goal` à la ligne 34 (avant `ring`, branche off-diagonale): but `-1 / (↑n - 1) = -(↑n - 1)⁻¹` — la normalisation triviale division↔inverse.

## Comparaison directe avec scripts ML générés

### Goedel attempt 00 (PASS)

```lean4
ext i j
simp only [L, J]
by_cases h : i = j
· simp [h, Matrix.one_apply, Matrix.smul_apply, Finset.sum_ite_eq']
  <;> field_simp [h₁]
  <;> ring_nf
  <;> field_simp [h₁]
  <;> ring_nf
  <;> norm_num
  <;> (try { ... linarith })
  <;> (try { simp_all [Fin.ext_iff] <;> norm_num <;> linarith })
· simp [h, Matrix.one_apply, ...]
  <;> field_simp [h₁]
  <;> ... (same cascade)
```

Goedel reproduit la structure macro (`ext`, `by_cases`, `simp` + arithmétique) mais ajoute du bruit syntaxique RL closure-tuning massif:

- Cascade `field_simp <;> ring_nf <;> field_simp <;> ring_nf <;> norm_num <;> try linarith <;> try simp_all`. Cinq tactiques où une suffit (`field_simp` ou `ring`).
- Inclut `Finset.sum_ite_eq'` qui n'a aucun rapport avec la preuve (héritage d'autres formes du `Matrix.one_apply`).
- Side-condition `h₁ : (n : ℝ) - 1 ≠ 0` correctement nommée (équivalent à mon `h_n1`).

Verdict: structurellement préservé, syntaxiquement bruité par cascade défensive `<;>`.

### Kimina attempt 36 (PASS)

```lean4
funext i j
simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, L, J]
split_ifs with h
· simp [h]
  all_goals
    field_simp [(show (n : ℝ) ≥ 2 by ...), (show (n : ℝ) - 1 ≠ 0 by ... nlinarith)]
    <;> ring
· simp [h]
  all_goals
    field_simp [(show ...), (show ...)]
    <;> ring
```

Kimina reproduit aussi la structure macro mais:

- Utilise `split_ifs` au lieu de `by_cases` (équivalent ici, mais moins littéral envers la dichotomie official solutione).
- Inline les side-conditions à chaque appel `field_simp` au lieu de les nommer une fois (`have h_n1 := ...`). Effet: lecture inverse plus difficile — la lectrice doit reconnaître que les `show ... ≠ 0` répétés sont la *même* hypothèse.
- `nlinarith` au lieu de `linarith` pour dériver `(n : ℝ) - 1 ≠ 0` à partir de `n ≥ 2`. Surpuissance: `linarith` suffit (vérifié dans le transcription).
- `all_goals ... <;> ring` redondant: après `simp [h]; field_simp [...]`, il ne reste qu'un goal et `ring` suffit.

Verdict: structurellement préservé, side-conditions dénommées par inlining, automation surpuissée.

### Kimina attempt 54 (PASS)

```lean4
funext i j
have hn1 : (n : ℝ) ≥ 2 := by ...
have hn2 : (n : ℝ) - 1 ≥ 1 := by nlinarith
have h1 : (n : ℝ) - 1 > 0 := by
  have hn1 : (n : ℝ) ≥ 2 := by ...
  nlinarith
by_cases h : i = j
· rw [h]
  simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h,
        Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  all_goals
    field_simp at *
    all_goals nlinarith
· rw [if_neg h]
  simp [..., Finset.sum_eq_add_sum_diff_singleton ..., ...]
  all_goals
    field_simp at *
    all_goals try { nlinarith }
```

Kimina att54 illustre la dérive opposée: trois side-conditions différentes pour la même chose (`hn1 : n ≥ 2`, `hn2 : n - 1 ≥ 1`, `h1 : n - 1 > 0`), dont deux sont inutiles. `Finset.sum_eq_add_sum_diff_singleton` est mobilisé sans nécessité (artefact d'un raisonnement sur `Matrix.mul`, alors que la preuve n'utilise pas de produit matriciel). La fermeture passe par `nlinarith` agissant sur un état post-`field_simp` enchevêtré.

Verdict: structure macro (a) mais hypothèses dupliquées et lemmes hors-sujet importés.

## Hiérarchie observée sur P7.A.2.a

| | side-cond nommée | per-cell ext | dichotomie | diag arith | off-diag arith | classification |
|---|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `have h_n1 : ↑n - 1 ≠ 0` (1 ligne) | `ext i j` | `by_cases h` | `simp [h]; field_simp` | `simp [h]; ring` | (a) faithful |
| **Goedel att00** | `have h₁ : (n:ℝ)-1 ≠ 0` (3 lignes via h₂, h₃) | `ext i j` | `by_cases h` | cascade 5-tac `<;>` + `try` | cascade idem | (a) bruité |
| **Kimina att36** | inline répété dans `field_simp` | `funext i j` | `split_ifs` | `simp [h]; field_simp [...]; ring` | idem | (a) inlined |
| **Kimina att54** | 3 hypothèses redondantes (`hn1`, `hn2`, `h1`) | `funext i j` | `by_cases h` | `Finset.sum_eq_add_sum_diff_singleton` + `field_simp at *; nlinarith` | idem + `try` | (a) overkill |

Quatre preuves kernel-équivalentes. Quatre profils bidirectionnels distincts. Toutes structurées comme (a) au sens macro (`ext` + `by_cases` + arithmétique nommée), mais la finesse bidirectionnelle se joue ailleurs:

1. **Side-condition unique vs dupliquée**: transcription nomme `h_n1` une fois et la consomme implicitement; Kimina att54 instancie trois copies; Kimina att36 l'inline à chaque appel.
2. **Tactique minimale vs cascade défensive**: transcription utilise `field_simp` (diag) et `ring` (off-diag) — un appel par cellule; Goedel cascade six tactiques avec `<;>` et `try`; Kimina att54 importe un lemme de `Finset.sum` non utilisé.
3. **Correspondance dichotomie official solutione**: `by_cases h : i = j` (transcription, Goedel, Kimina att54) traduit littéralement « si $i = j$, ... sinon, ... »; `split_ifs` (Kimina att36) est équivalent mais moins légalement adressé au texte.

## Implications

### Pour AITP v7

1. **Plafond transcription atteint à structure (a)**: avec lean-lsp + official solution en main + instruction "transcription fidèle", la sortie est (a) faithful. Le critère bidirectionnel n'est pas saturé par bruit de mesure.
2. **Distinction Goedel / Kimina sur P7**: les deux modèles produisent des PASSes structurellement (a) mais divergent sur la *dénomination* des side-conditions (transcription/Goedel: nommée; Kimina att36: inlined; Kimina att54: triple-instanciée). Cette gradation est mécaniquement détectable (compter les `have` dans la preuve, mesurer la longueur de la cascade `<;>`).
3. **Route abstraite `smul`-decomposition: 0/56 PASSes**. Confirmation empirique: ni Goedel ni Kimina ne tentent la route official solutione littérale. Ce gap est intéressant pour WDWFT — il indique que la "transcription la plus littérale possible" en Mathlib actuel n'est pas accessible aux modèles RL et reste un horizon.

### Pour WDWFT

P7.A.2.a est un cas test où **le official solution n'est pas littéralement transcriptible** dans le formalisme cible (Mathlib v4.30.0-rc2). Le transcription script descend d'un cran (entrywise) mais préserve toutes les autres caractéristiques bidirectionnelles: side-condition nommée, dichotomie nommée, arithmétique de feuille nommée, automation minimale.

Phrasing pour WDWFT (révisé après expérimentation P7):

> *La bidirectionalité d'un script tactique n'est pas un seuil binaire mais une gradation. Sur P7.A.2.a (matrice du Laplacien de $K_n$), la route official solutione — factoriser $-1/(n-1)$, reconnaître $J - nI$, distribuer — n'est pas atteignable dans Mathlib actuel (0/56 PASSes la tentent). Le transcription script descend au niveau entrywise, mais y maintient: side-condition nommée une fois (`h_n1`), réduction par `ext + simp only` aux entrées, dichotomie `by_cases h : i = j` parallèle au texte du official solution, arithmétique close par `field_simp` (diag) ou `ring` (off-diag) — un appel par cellule. Goedel reproduit la structure mais avec cascade `<;>` à six tactiques. Kimina (deux PASSes échantillonnés) reproduit aussi la structure mais inline les side-conditions ou les triple-instancie. Toutes les preuves sont kernel-équivalentes; toutes sont (a) au sens macro. La gradation fine — *combien de fois la même hypothèse est-elle nommée, et quelle est la longueur de la cascade défensive* — est elle aussi mécaniquement auditable.*

## Verification trace

- File: `/home/dxwoo/Code/AITP/lean_corpus/LeanCorpus/P7.lean`
- Copy: `/home/dxwoo/Code/AITP/rerun4/solution_transcription/P7_subq_A_2_a.lean`
- Kernel status: PASS (lean-lsp `lean_diagnostic_messages` returns 0 items)
- Goal trace recorded at lines 22, 30, 34 — see § Vérification.
- Classification: (a) faithful (structural-macro level); not (a*) abstract-route (unreachable in Mathlib).
