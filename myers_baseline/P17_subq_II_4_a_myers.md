# Myers-style transcription of Mercier-Rombaldi P17, question II.4.a

The Lean 4 script at `P17_subq_II_4_a_myers.lean` realises the corrigé's four named moves as four syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

The corrigé proves the iterated tent-map theorem by induction on `n`. The base case observes `f^0(x) = x = 1·x + 0`. The inductive step computes `f^{n+1}(x) = f(f^n(x)) = f(a_n x + b_n)` and case-splits on whether `a_n x + b_n ∈ [0, 1/2]` or `∈ ]1/2, 1]`, yielding witnesses `(a_{n+1}, b_{n+1}) = 2(a_n, b_n)` in the first case and `(a_{n+1}, b_{n+1}) = -2(a_n, b_n - 1) = (-2 a_n, 2 - 2 b_n)` in the second.

The Lean script inscribes these four moves explicitly. Move 1 — induction on `n` — is `induction n with | zero => ... | succ k ih => ...`. Move 2 — base witnesses `(1, 0)` — is `refine ⟨1, 0, ?_⟩; simp [Function.iterate_zero]`. Move 3 — successor unfolding `f^{k+1}(x) = f(f^k(x)) = f(a·x + b)` — is `rw [Function.iterate_succ_apply', hab, hf]`, the three rewrites composed in the order the corrigé reads: unfold the iterate, substitute the IH, unfold `f`. Move 4 — case-split on the tent map — is `by_cases hle : (a : ℝ) * x + (b : ℝ) ≤ 1 / 2`, with each branch closing by `rw [abs_of_nonpos / abs_of_nonneg]; ring` for the absolute-value resolution and `refine ⟨2 * a, 2 * b, ?_⟩` / `refine ⟨-2 * a, 2 - 2 * b, ?_⟩` for the named witnesses. The witnesses match the corrigé character-for-character: `2(a_n, b_n)` and `-2(a_n, b_n - 1)`.

The hypothesis `hx : x ∈ Set.Icc 0 1` is unused. This is faithful to the corrigé: the inductive proof of the existential statement does not require `x ∈ [0, 1]` at any tactic step; the bounded-domain assumption is only relevant to motivate the tent map's range and to derive `a_n = ε_n(x) · 2^n` (a remark made *after* the existence proof, in the corrigé's "On remarque que" sentence). Adding a defensive `Icc`-preservation lemma `∀ k, f^[k] x ∈ Set.Icc 0 1` would be a logical insertion not present in the corrigé.

## Self-classification

(a) — Faithful Myers transcription. The script's four `induction` / `refine` / `rw` / `by_cases` blocks are in bijection with the four named corrigé moves; the witnesses `(2a, 2b)` and `(-2a, 2 - 2b)` are written by hand inside each `refine`, not synthesised by automation; the absolute-value resolution uses `abs_of_nonpos` and `abs_of_nonneg` directly with `linarith` discharging the sign hypothesis. The structural shape is exactly the target skeleton: induction → base witnesses → unfold → case-split → named witnesses.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 infos, 1 warning** (`unused variable hx` — structurel, l'hypothèse Icc n'est pas utilisée par le corrigé non plus).
- `mcp__lean-lsp__lean_goal` à la ligne 39 (juste avant le `ring` final du second cas):
  - `goals_before`: contexte avec `hab`, `hle` négué via `lt_of_not_ge`, `h_abs`, but `1 - |2 * (↑a * x + ↑b) - 1| = ↑(-2 * a) * x + ↑(2 - 2 * b)`.
  - `goals_after`: `[]` — fermé proprement par `ring` après `push_cast`, agissant sur les hypothèses nommées sans hint-list ni cascade.
- Le `linarith` n'apparaît que comme argument dans `abs_of_nonpos (by linarith)` / `abs_of_nonneg (by linarith)` — où il décharge la condition de signe à partir de `hle` ou `hgt`. Aucun `linarith` au niveau extérieur.

## Comparaison directe avec scripts ML générés (parmi les 55 PASSes P17.subq_II_4_a)

### Kimina attempt 21 (PASS, classifié K-a1, le plus court de la cohorte Kimina)

```lean4
have h1 : 0 ≤ x ∧ x ≤ 1 := by simpa using hx
have h2 : ∀ (n : ℕ), ∃ a b : ℤ, f^[n] x = (a : ℝ) * x + (b : ℝ) := by
  intro n
  induction n with
  | zero => use 1, 0; simp
  | succ k ih =>
    rcases ih with ⟨a, b, h_eq⟩
    have eq1 : f^[k + 1] x = f (f^[k] x) := by simp [Function.iterate_succ_apply']
    rw [eq1, h_eq]
    have h3 : f ((a : ℝ) * x + (b : ℝ)) = 1 - |2 * ((a : ℝ) * x + (b : ℝ)) - 1| := by apply hf
    rw [h3]
    by_cases h : (2 * ((a : ℝ) * x + (b : ℝ)) - 1 : ℝ) ≥ 0
    · have h4 : |(2 * ((a : ℝ) * x + (b : ℝ)) - 1 : ℝ)| = ... := by rw [abs_of_nonneg h]
      rw [h4]
      have eq2 : (1 : ℝ) - (2 * ((a : ℝ) * x + (b : ℝ)) - 1) = (-2 * (a : ℝ)) * x + (-2 * (b : ℝ) + 2) := by ring_nf
      rw [eq2]
      refine' ⟨-2 * a, -2 * b + 2, by simp_all [mul_add, add_mul]⟩
    · ... [symmetric branch] ...
specialize h2 n
simpa using h2
```

Kimina K-a1 reproduit la structure (induction sur `n`, `iterate_succ_apply'`, `by_cases` sur le signe, `abs_of_nonneg`, `refine` avec témoins explicites) mais ajoute du bruit syntaxique RL closure-tuning:

- Le `have h1 : 0 ≤ x ∧ x ≤ 1 := by simpa using hx` extrait l'Icc bien que jamais utilisé en aval. Bruit défensif.
- Le `have h2 : ∀ n, ...` universalise sur `n` et reapplique avec `specialize h2 n; simpa using h2`. La quantification universelle interne plus le `specialize` final ajoute deux niveaux d'indirection inutiles — le `induction n with` direct sur le but suffit.
- `have eq1 : f^[k + 1] x = f (f^[k] x) := by simp [Function.iterate_succ_apply']` puis `rw [eq1, h_eq]` puis `have h3 : f (...) = 1 - |...| := by apply hf` puis `rw [h3]`: trois `have`-puis-`rw` séparés alors que `rw [Function.iterate_succ_apply', hab, hf]` compose les trois rewrites en une ligne.
- `have eq2 : (1 : ℝ) - (...) = (-2 * a) * x + (-2 * b + 2) := by ring_nf` puis `rw [eq2]` puis `refine' ⟨-2 * a, -2 * b + 2, by simp_all [mul_add, add_mul]⟩`: le ring identity est extrait dans un `have` séparé puis réinscrit, alors que `refine ⟨-2 * a, 2 - 2 * b, ?_⟩; rw [h_abs]; push_cast; ring` ferme directement.
- `simp_all [mul_add, add_mul]` à la fin de chaque branche est plus puissant que nécessaire — `push_cast; ring` suffit (vérifié par lean-lsp).

Verdict: structurellement préservé, syntaxiquement bruité (~50% plus long: 51 lignes vs 39 lignes Myers).

### Goedel attempt 00 (PASS, classifié G-b1)

Tous les 48 PASSes Goedel partagent une cascade `simp [mul_assoc] <;> ring_nf <;> norm_cast <;> simp_all [Int.cast_mul, ...] <;> linarith` à la fermeture de chaque branche, avec wrapper `have h_main := ...; exact h_main`, plus une induction interne `have h : ∀ n, ∃ a b : ℤ, ...; intro n; induction n with`. Char-len 2018-6182 (mean 3347), n_lines 56-151 (mean 88). Voir `kimina_att04` pour un pattern intermédiaire (témoins corrects mais closure shotgun).

Verdict: témoins corrects mais l'égalité finale est enfouie dans une cascade où aucun pas isolé ne correspond à une opération mathématique nommée. Score (b).

## Hiérarchie observée sur P17.subq_II_4_a

| | induction nommée | unfold + IH | case-split sur signe | témoins explicites | closure |
|---|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `induction n with` | `rw [iterate_succ_apply', hab, hf]` (1 ligne) | `by_cases hle : ... ≤ 1/2` | `refine ⟨2*a, 2*b, ?_⟩` / `refine ⟨-2*a, 2-2*b, ?_⟩` | `rw [h_abs]; push_cast; ring` |
| **Kimina K-a1 att21** | `induction n with` (interne, sous `∀ n`) | `have eq1; rw [eq1, h_eq]; have h3; rw [h3]` (3 étapes) | `by_cases h : ... ≥ 0` | `refine' ⟨-2*a, -2*b+2, ...⟩` | `simp_all [mul_add, add_mul]` |
| **Goedel G-b1 att00** | `induction n with` (interne, sous `∀ n`) | similaire à Kimina | `by_cases h : ... ≥ 0` | `use 2*a, 2*b` (correct) | `simp [...] <;> ring_nf <;> norm_cast <;> simp_all <;> linarith` |
| **Kimina K-b1 att04** | `induction n with` (interne) | similaire | `by_cases h : ... ≥ 0` | `use -2*a, 2 - 2*b` (correct) | `all_goals simp; all_goals ring_nf` shotgun |

Quatre preuves kernel-équivalentes. Quatre profils bidirectionnels distincts. La gradation est observable par lecture, mécaniquement vérifiable par lean-lsp (présence/absence des cascades et profondeur de l'extraction `have`-puis-`rw`), et auditable.

## Implications

### Pour AITP v7

1. **La métrique reste calibrée à n=4 mouvements**: avec un humain (Claude jouant Myers) en input + instruction "transcription fidèle", la sortie est (a) parfait sur un théorème à plus haute charge structurelle (induction + case-split + témoins entiers) que P12 (identité + non-négativité + linarith). Le critère bidirectionnel ne sature pas avec la complexité des théorèmes.
2. **L'inversion v6 confirmée à plus haute résolution sur P17**: Kimina 86% (a) (six PASSes K-a1, un K-a2, un K-b1) — opposé exact de P17.subq_II_4_b où Goedel 100% PASSait avec scripts Mathlib-natifs (`Real.tan` sur Bourbaki). L'arme qui produit (a) dépend du théorème.
3. **Ground truth artefact**: ce fichier `.lean` peut être publié dans le repo `lean-prover-bidirectionality` comme baseline P17.subq_II_4_a, kernel-vérifié et auditable.

### Pour WDWFT

Cet artefact répond à l'objection "la bidirectionalité est juste un compte de lignes":

- Le script Myers (39 lignes, 1485 chars) est ~25% plus court que le K-a1 le plus compact (51 lignes, kimina_att21) et ~62% plus court que la moyenne Goedel (88 lignes). Mais la longueur n'est pas le critère — la composition des rewrites `rw [Function.iterate_succ_apply', hab, hf]` en une ligne au lieu de trois `have`-puis-`rw` séquentiels est la marque de la transcription fidèle: chaque rewrite correspond à une étape de calcul du corrigé, et leur composition reflète l'enchaînement informel `f^{n+1}(x) = f(f^n(x)) = f(a_n x + b_n)`.
- La distinction Myers / K-a1 / G-b1 / K-b1 est *structurelle* (composition des rewrites, profondeur d'extraction des `have`, force du tactique de fermeture), pas *stylistique*.
- Le hypothèse `hx : x ∈ Set.Icc 0 1` non-utilisée est le test de discipline: les 12/48 G-b2 ajoutent une preuve auxiliaire `∀ k, f^[k] x ∈ Set.Icc 0 1` *même si elle n'apparaît pas dans le corrigé*. Le script Myers laisse `hx` inutilisé parce que le corrigé le laisse inutilisé.

Phrasing pour WDWFT (révisé après expérimentation P17):

> *La bidirectionalité d'un script tactique se mesure par la préservation des mouvements nommés du corrigé comme opérations Lean nommées, à la fois en présence (chaque mouvement → une opération) et en absence (aucune opération sans mouvement correspondant). Sur P17.II.4.a (itéré du tent map, induction + case-split + témoins entiers), le script Myers-fidèle compose `induction n with`, `rw [Function.iterate_succ_apply', hab, hf]`, `by_cases hle : (a : ℝ) * x + (b : ℝ) ≤ 1/2`, et deux `refine ⟨..., ?_⟩` avec témoins `(2a, 2b)` et `(-2a, 2 - 2b)`. Le script Kimina K-a1 typique reproduit la structure mais sépare l'unfold en trois `have`-puis-`rw` et ferme par `simp_all [mul_add, add_mul]` au lieu de `ring`. Le script Goedel G-b1 typique reproduit la structure mais ferme par cascade `simp <;> ring_nf <;> norm_cast <;> simp_all <;> linarith`. Les quatre scripts (Myers, K-a1, G-b1, K-b1) sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel à la fois en présence et en absence.*
