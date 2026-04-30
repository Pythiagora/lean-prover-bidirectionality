# Myers-style transcription of Mercier-Rombaldi P12, question I.B.2.a

The Lean 4 script at `P12_subq_I_B_2_a_myers.lean` realises the corrigé's three named moves as three syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

The corrigé opens with a small reduction of a real quadratic form: `x^2 + xy + y^2 = (y + x/2)^2 + (3/4) x^2`. This algebraic identity is inscribed verbatim as `have h_id : x ^ 2 + x * y + y ^ 2 = (y + x / 2) ^ 2 + (3 / 4 : ℝ) * x ^ 2 := by ring`. The square completion is the *content* of the named move; `ring` is a normaliser that *certifies* the identity once stated, but it does not search for or guess the completing square — the pivot `(y + x/2)` appears explicitly in the goal that `ring` is asked to discharge. The corrigé's second named move, "the square is non-negative", is inscribed as `have h_sq : (y + x / 2) ^ 2 ≥ 0 := sq_nonneg _`, where `sq_nonneg` is the Mathlib lemma stating `∀ a, 0 ≤ a^2` and the `_` is the same pivot the corrigé wrote. The third move — "the inequality follows by adding `(3/4) x^2` to the non-negativity bound" — is closed by `linarith`, which here operates on the two named hypotheses `h_id` and `h_sq` already in context. This is the bidirectional sweet spot: `linarith` is doing *bookkeeping over named facts*, not pattern-matching against a hint list of guessed squares (as `nlinarith [sq_nonneg (y + x/2)]` would do). A reverse-reader scanning the script meets exactly the corrigé's three sentences in order: identity, non-negativity, combination.

## Self-classification

(a) — Faithful Myers transcription. The script's three `have` / closing steps are in bijection with the three named corrigé moves; the completing-square pivot `(y + x/2)` is written by hand inside `h_id`, not synthesized by automation; `linarith` sees only already-named hypotheses. The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée).
- `mcp__lean-lsp__lean_goal` à la ligne 15 (juste avant `linarith`):
  - `goals_before`: contexte avec `h_id`, `h_sq` nommés, but `x^2 + x*y + y^2 ≥ 3/4 * x^2`
  - `goals_after`: `[]` — fermé proprement par `linarith` agissant sur les hypothèses nommées sans hint-list
- `mcp__lean-lsp__lean_multi_attempt` à la ligne 15: `linarith` ferme; `nlinarith` ferme aussi (mais inutilement plus puissant); `polyrith` indisponible (service externe arrêté); `positivity` ne s'applique pas (pas un goal de positivité). Le tactique minimal qui ferme dans le contexte nommé est `linarith` — pas `nlinarith`.

## Comparaison directe avec scripts ML générés (parmi les 119 PASSes P12)

### Goedel attempt 01 (PASS, classifié (a) par sub-agent)

```lean4
have h_main : (1 / 4 : ℝ) * x ^ 2 + x * y + y ^ 2 ≥ 0 := by
  have h1 : (1 / 4 : ℝ) * x ^ 2 + x * y + y ^ 2 = (y + x / 2) ^ 2 := by
    ring_nf
    <;> field_simp
    <;> ring_nf
    <;> linarith
  rw [h1]
  nlinarith [sq_nonneg (y + x / 2)]
have h_final : ... := by ...
```

Goedel reproduit la structure (`have h1` pour l'identité, `nlinarith [sq_nonneg]` pour la non-négativité) mais ajoute du bruit syntaxique RL closure-tuning:

- La cascade `ring_nf <;> field_simp <;> ring_nf <;> linarith` après `ring_nf` est inutile — `ring` seul suffit (vérifié par lean-lsp).
- L'identité Goedel `(1/4)·x² + xy + y² = (y + x/2)²` est mathématiquement équivalente à la version corrigé `x² + xy + y² = (y + x/2)² + (3/4)·x²` mais nécessite une étape supplémentaire (`have h_final`) pour relier au but. Le corrigé fait l'algèbre directement.
- Goedel ferme via `nlinarith [sq_nonneg ...]` même quand `linarith` suffirait.

Verdict: structurellement préservé, syntaxiquement bruité.

### Kimina attempt 05 (PASS, classifié (b) par sub-agent)

```lean4
nlinarith [sq_nonneg (x + 2 * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y), sq_nonneg (x)]
```

Aucun `have`. L'identité algébrique n'est jamais énoncée. Cinq carrés candidats sont passés en hint-list à `nlinarith`, qui résout par recherche tactique. Le mouvement corrigé `(y + x/2)²` n'apparaît même pas — Kimina trouve un certificat différent que `nlinarith` exploite (`(x + 2y)²` fait également l'affaire algébriquement).

Verdict: identité utilisée mais jamais inscrite. Une lectrice ne peut pas reconstituer le corrigé depuis ce script.

## Hiérarchie observée sur P12

| | identité nommée | non-négativité nommée | fermeture | classification |
|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `have h_id : = (y + x/2)² + (3/4)x² := by ring` | `have h_sq := sq_nonneg _` | `linarith` | (a) parfait |
| **Goedel att01** | `have h1 : = (y + x/2)² := by ring_nf <;> ...` | absorbé dans `nlinarith [sq_nonneg ...]` | `nlinarith` + restructuration `have h_final` | (a) bruité |
| **Kimina att05** | absente | absorbée dans hint-list 5-carrés | `nlinarith` shotgun | (b) opaque |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts. La gradation est observable par lecture, mécaniquement vérifiable par lean-lsp (présence/absence des `have` nommés), et auditable.

## Implications

### Pour AITP v7

1. **La métrique est calibrée**: avec un humain (Claude jouant Myers) en input + instruction "transcription fidèle", la sortie est (a) parfait. Le critère bidirectionnel n'est pas saturé par bruit de mesure.
2. **L'inversion v6 confirmée à plus haute résolution**: Goedel approche le upper bound Myers (modulo bruit syntaxique RL); Kimina s'en éloigne radicalement (le mouvement corrigé n'est jamais nommé dans la majorité des PASSes Kimina).
3. **Ground truth artefact**: ce fichier `.lean` peut être publié dans le repo `lean-prover-bidirectionality` comme baseline, kernel-vérifié et auditable.

### Pour WDWFT

Cet artefact répond directement à l'objection "la bidirectionalité est juste de la lisibilité subjective":

- Le script Myers est mécaniquement vérifiable (kernel + lean-lsp `lean_goal` confirme la fermeture par hypothèses nommées sans hint-list).
- Le mapping mouvement-corrigé → opération-Lean est traçable ligne-par-ligne.
- La distinction Myers / Goedel / Kimina est *structurelle* (présence/absence d'un `have` nommé pour chaque mouvement), pas *stylistique*.

Phrasing pour WDWFT (révisé après expérimentation):

> *La bidirectionalité d'un script tactique se mesure par la préservation des mouvements nommés du corrigé comme opérations Lean nommées. Sur P12 (`x²+xy+y² ≥ (3/4)x²`), le script Myers-fidèle (`have h_id := by ring; have h_sq := sq_nonneg _; linarith`) inscrit chacun des trois mouvements corrigés en un `have` ou un appel de lemme. Le script Goedel typique reproduit la structure avec bruit syntaxique (`ring_nf <;> field_simp <;> ring_nf <;> linarith` au lieu de `ring`). Le script Kimina typique élimine la structure: l'identité algébrique disparaît, absorbée dans une hint-list `nlinarith [sq_nonneg ...]`. Les trois scripts sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel.*
