# Myers-style transcription of Mercier-Rombaldi P11, question IV.2.a

The Lean 4 script at `P11_subq_IV_2_a_myers.lean` realises the corrigé's three named moves as three syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

The corrigé writes (page 026/027): "La fonction $v$ définie sur $J_T = \{t - T \mid t \in J\}$ par $v(\tau) = u(\tau + T)$ est dérivable [...] avec $v'(\tau) = u'(\tau + T) = f(\tau + T, u(\tau + T)) = f(\tau, v(\tau))$." Three named moves: (1) chain rule on $s \mapsto s + T$, derivative is $1$; (2) apply the ODE hypothesis $u' = f(t, u)$ at $\tau + T$ to obtain $u'(\tau + T) = f(\tau + T, u(\tau + T))$; (3) apply $T$-periodicity of $f$ in the time slot to convert $f(\tau + T, \cdot)$ to $f(\tau, \cdot)$.

The Myers script encodes each move as one named tactic. Move 1 is `have h_chain : HasDerivAt (fun s : ℝ => s + T) 1 τ := (hasDerivAt_id τ).add_const T` — the named lemma `hasDerivAt_id` gives the identity's derivative, `.add_const T` is the named operation that shifts by a constant; no automation guesses the derivative `1`. Move 2 is `have h_step := (hu (τ + T)).comp τ h_chain` — `hu` is instantiated at the explicit point `τ + T` and composed via the named `HasDerivAt.comp` with the chain-rule hypothesis. The intermediate `* 1` artefact (from chain-rule arithmetic `f(τ+T, u(τ+T)) * 1`) is discharged by `rw [mul_one] at h_step`, a single named identity rewrite — not `simp`, not `ring`, not a flexible cleanup. Move 3 is `rw [f_periodic] at h_step` — the named periodicity hypothesis is applied directly as a rewrite to convert the time slot, with no rewriting of the value slot. The closing `exact h_step` discharges the goal because Lean accepts `u ∘ (fun s ↦ s + T)` as definitionally equal to `fun s ↦ u (s + T)` — no eta-expansion or `funext` is needed.

A reverse-reader scanning the script meets exactly the corrigé's three sentences in order: chain rule, ODE hypothesis at $\tau + T$, periodicity rewrite.

## Self-classification

(a) — Faithful Myers transcription. Each of the three corrigé moves maps to one named Lean operation: `(hasDerivAt_id _).add_const T` for the chain rule, `.comp τ` for the composition with `hu (τ + T)`, `rw [f_periodic]` for the periodicity. The `mul_one` step is not a corrigé move but a syntactic artefact of the chain-rule output `f(_) * 1`; cleared by the named identity, not by `simp`. No `<;>`, no `nlinarith`, no `ring_nf`, no shotgun. The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée, sans avertissement de tactique flexible).
- `mcp__lean-lsp__lean_verify` sur `subq_IV_2_a`: axiomes `[propext, Classical.choice, Quot.sound]` — preuve close avec axiomes standards, aucun `sorry`, aucun `axiom` ad hoc.
- `mcp__lean-lsp__lean_goal` à la ligne 33 (juste avant `exact h_step`):
  - `goals_before`: `HasDerivAt (u ∘ fun s ↦ s + T) (f τ (u (τ + T))) τ` (avec `h_step` nommé)
  - But final: `HasDerivAt (fun s ↦ u (s + T)) (f τ (u (τ + T))) τ`
  - `goals_after`: `[]` — fermé par `exact h_step` (defeq de `u ∘ (· + T)` et `fun s ↦ u (s + T)`).
- `mcp__lean-lsp__lean_multi_attempt` à la ligne 30: `rw [mul_one] at h_step` réduit `f(τ+T, u(τ+T)) * 1` à `f(τ+T, u(τ+T))`; la rewrite combinée `rw [f_periodic, mul_one]` ferme également. La forme à trois tactiques nommées séparées (`rw mul_one` / `rw f_periodic` / `exact`) préserve la lecture mouvement-par-mouvement.

## Comparaison directe avec scripts ML générés

### Goedel attempt 01 (PASS)

```lean4
intro τ
have h1 : HasDerivAt (fun s : ℝ => u (s + T)) (f (τ + T) (u (τ + T))) τ := by
  have h2 : HasDerivAt (fun s : ℝ => s + T) 1 τ := by
    simpa using (hasDerivAt_id τ).add_const T
  have h3 : HasDerivAt u (f (τ + T) (u (τ + T))) (τ + T) := hu (τ + T)
  have h4 : HasDerivAt (fun s : ℝ => u (s + T)) (f (τ + T) (u (τ + T)) * 1) τ := HasDerivAt.comp τ h3 h2
  convert h4 using 1 <;> ring
  <;> simp [mul_one]
have h2 : f (τ + T) (u (τ + T)) = f τ (u (τ + T)) := by
  have h3 := f_periodic τ (u (τ + T))
  ring_nf at h3 ⊢
  <;> linarith
have h3 : HasDerivAt (fun s : ℝ => u (s + T)) (f τ (u (τ + T))) τ := by
  have h4 : f (τ + T) (u (τ + T)) = f τ (u (τ + T)) := h2
  have h5 : HasDerivAt (fun s : ℝ => u (s + T)) (f (τ + T) (u (τ + T))) τ := h1
  convert h5 using 1
  <;> rw [h4]
exact h3
```

Goedel reproduit la structure (`hasDerivAt_id.add_const`, `HasDerivAt.comp`, périodicité) mais ajoute du bruit syntaxique RL closure-tuning :

- `simpa using (hasDerivAt_id τ).add_const T` : le `simpa` est inutile, le terme est déjà du bon type (vérifié dans le script Myers).
- `convert h4 using 1 <;> ring <;> simp [mul_one]` : trois fermetures cascadées pour gérer `* 1`. Le Myers le fait en une `rw [mul_one]`.
- `have h2 : f (τ + T) _ = f τ _ := by have h3 := f_periodic τ _; ring_nf at h3 ⊢; <;> linarith` : la périodicité est reformulée comme une égalité auxiliaire puis traitée par `ring_nf + linarith`. Le Myers la rewrite directement par `rw [f_periodic]`.
- `convert h5 using 1 <;> rw [h4]` : transport tactique du `HasDerivAt` à travers l'égalité. Le Myers utilise `rw [f_periodic] at h_step` sur l'hypothèse, pas sur le but.

Verdict: structurellement préservé (les trois mouvements corrigé sont identifiables), syntaxiquement bruité (chaque mouvement enveloppé d'au moins un `simpa` / `convert` / `<;>` superflu).

### Kimina attempt 08 (PASS)

```lean4
intro τ
have h1 : HasDerivAt u (f (τ + T) (u (τ + T))) (τ + T) := by
  specialize hu (τ + T)
  simpa using hu
have h2 : HasDerivAt (fun s : ℝ => u (s + T)) (f (τ + T) (u (τ + T))) τ := by
  have h6 : HasDerivAt (fun s : ℝ => s + T) 1 τ := by
    simp [hasDerivAt_id', add_left_inj]
  have h7 : HasDerivAt u (f (τ + T) (u (τ + T))) (τ + T) := h1
  have h8 : HasDerivAt (fun s : ℝ => u (s + T)) (f (τ + T) (u (τ + T)) * 1) τ := by
    apply HasDerivAt.comp
    exact h7
    exact h6
  simpa using h8
have h9 : f (τ + T) (u (τ + T)) = f τ (u (τ + T)) := by
  specialize f_periodic (τ) (u (τ + T))
  ring_nf at f_periodic ⊢
  linarith
rw [h9] at h2
exact h2
```

Kimina suit la même structure tripartite que Goedel (chain rule, comp, périodicité), avec un bruit légèrement différent :

- `specialize hu (τ + T); simpa using hu` au lieu du direct `hu (τ + T)`.
- `simp [hasDerivAt_id', add_left_inj]` pour la dérivée de `s + T` au lieu du nommé `(hasDerivAt_id _).add_const T`. La preuve invoque `add_left_inj` qui n'a aucune pertinence sémantique (c'est une lemma d'injectivité de l'addition).
- `apply HasDerivAt.comp; exact h7; exact h6` au lieu de `(hu _).comp τ h_chain` (style preuve-explicite vs. style applicatif).
- `ring_nf at f_periodic ⊢; linarith` pour appliquer la périodicité au lieu de `rw [f_periodic]`. La périodicité est traitée comme une identité arithmétique opaque.
- `rw [h9] at h2` : transport via égalité auxiliaire au lieu d'un rewrite direct sur l'hypothèse `f_periodic`.

Verdict: structure tripartite préservée mais avec une couche d'indirection (égalité auxiliaire `h9` puis `rw [h9]`) qui obscurcit le mouvement corrigé "appliquer la périodicité". Le `add_left_inj` injecté par `simp` est un faux positif sémantique.

## Hiérarchie observée sur P11.subq_IV_2_a

| | chain rule nommé | comp + hu nommé | périodicité nommée | classification |
|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `(hasDerivAt_id τ).add_const T` | `(hu (τ+T)).comp τ h_chain` | `rw [f_periodic] at h_step` | (a) parfait |
| **Goedel att01** | `simpa using (hasDerivAt_id τ).add_const T` | `HasDerivAt.comp τ h3 h2` + `convert h4 using 1 <;> ring <;> simp [mul_one]` | `have h2 : ... = ... := by ring_nf at h3 ⊢ <;> linarith` puis `convert h5 using 1 <;> rw [h4]` | (a) bruité |
| **Kimina att08** | `simp [hasDerivAt_id', add_left_inj]` (avec lemma non pertinente) | `apply HasDerivAt.comp; exact h7; exact h6` puis `simpa using h8` | `ring_nf at f_periodic ⊢; linarith` puis `rw [h9] at h2` | (a) bruité, sémantiquement opaque sur la périodicité |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts. La gradation est observable par lecture, mécaniquement vérifiable par lean-lsp (présence/absence du `rw [f_periodic]` direct), et auditable.

Observation supplémentaire : sur P11.subq_IV_2_a, ni Goedel ni Kimina ne tombent en (b) opaque (style mono-tactique). Les deux préservent la structure tripartite. Le bruit est local, pas structurel — contrairement à P12.I.B.2.a où Kimina absorbe l'identité algébrique entière dans une hint-list `nlinarith`. Cette différence reflète la nature du théorème : ici, la chaîne `chain rule → comp → rewrite` est une obligation de preuve quasi-mécanique (`HasDerivAt` ne se ferme pas par `nlinarith`), donc la marge pour le shotgun est étroite. Le bruit RL se manifeste alors dans le micro-style (`simpa`, `convert`, `ring_nf + linarith` à la place de `rw`) plutôt que dans la disparition du mouvement.

## Implications

### Pour AITP v7

1. **La métrique se calibre théorème-par-théorème** : sur P11.IV.2.a, la distinction Myers / Goedel / Kimina est plus fine (sub-tactique) que sur P12.I.B.2.a (structure entière). Une métrique bidirectionnelle agrégée doit pondérer la profondeur de bruit, pas seulement la présence/absence d'un `have` nommé.
2. **Les obligations de preuve `HasDerivAt` ferment l'espace shotgun** : aucune tactique généraliste ne ferme un goal `HasDerivAt (fun s => ...) _ τ` en un coup. Les modèles RL convergent donc vers la structure tripartite, mais avec du bruit local. C'est un cas où l'invariant bidirectionnel est partiellement protégé par la nature syntaxique du goal.
3. **Le nommage de la périodicité est le marqueur discriminant** : Myers fait `rw [f_periodic] at h_step` ; Goedel et Kimina passent par une égalité auxiliaire `h9 : f(τ+T) _ = f(τ) _ := by ring_nf + linarith`. La périodicité `f(t+T,x) = f(t,x)` n'est pas une identité arithmétique — la traiter par `ring_nf + linarith` est un mouvement sémantiquement faux qui se trouve fonctionner ici par coïncidence (le `linarith` referme une égalité triviale après que `ring_nf` ait appliqué la définition).

### Pour WDWFT

Cet artefact répond à la question "le critère bidirectionnel survit-il à des théorèmes plus structurés que des inégalités algébriques ?" :

- Oui, mais à grain plus fin. La distinction passe du niveau structure (présence d'un `have`) au niveau lemme nommé (`rw [f_periodic]` vs `ring_nf + linarith` après une égalité auxiliaire).
- Le critère reste mécaniquement auditable : un script Myers contient le rewrite par `f_periodic` ; un script ML, même PASS et structurellement correct, le remplace par une chaîne `have h_eq := f_periodic _ _; ring_nf + linarith`.
- L'invariant bidirectionnel à raffiner pour WDWFT : "chaque hypothèse-axiome du théorème (ici `f_periodic`) doit apparaître comme citation de lemme nommé dans le script, pas comme prémisse implicite d'une routine arithmétique".

Phrasing pour WDWFT (révisé après expérimentation P11.IV.2.a) :

> *Sur les théorèmes à structure de preuve obligatoire (`HasDerivAt`, `Continuous`, etc.), la bidirectionalité se mesure non plus à la présence des `have` nommés (que tous les modèles préservent par contrainte syntaxique) mais à la fidélité du nommage des hypothèses du théorème dans le corps de la preuve. Sur P11.IV.2.a, le mouvement "appliquer la périodicité" est inscrit comme `rw [f_periodic]` chez Myers, mais comme `have h_eq := f_periodic τ _ ; ring_nf at h_eq ⊢ ; linarith` chez Goedel et Kimina — une égalité auxiliaire fermée par routine arithmétique. Les trois scripts sont kernel-équivalents. Seul le premier inscrit la périodicité comme citation, pas comme conséquence calculée.*
