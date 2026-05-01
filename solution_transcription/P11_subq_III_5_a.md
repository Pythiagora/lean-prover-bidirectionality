# Solution transcription of Mercier-Rombaldi P11, sub-question III.5.a

The Lean 4 script at `P11_subq_III_5_a.lean` realises the official solution's time-reversal argument as four named moves per direction of the iff, each readable back into the informal text without re-derivation.

## Theorem

```lean4
theorem subq_III_5_a
    (f : ℝ → ℝ → ℝ) (u : ℝ → ℝ) :
    (∀ t : ℝ, HasDerivAt u (f t (u t)) t) ↔
      (∀ τ : ℝ, HasDerivAt (fun s => u (-s))
        (-f (-τ) (u (-τ))) τ) := by ...
```

The official solution (page_018.tex, III.5.a opening) introduces, for an interval `J` and a function `u` on `J`, the time-reversed objects `\widehat{J} = -J` and `\widehat{u}(τ) = u(-τ)`, then states verbatim: `v'(τ) = -u'(-τ) = -f(-τ, u(-τ))`. The transcription script transcribes this by `constructor` followed by four named moves in each direction.

**Forward direction** (`u` solves `x' = f(t,x)` ⇒ `v(τ) = u(-τ)` solves `v' = -f(-τ, v)`):

1. `have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) τ := (hasDerivAt_id τ).neg` — the official solution's "the derivative of `s ↦ -s` is `-1`" inscribed as a single named application of `HasDerivAt.neg` to `hasDerivAt_id`.
2. `have h_u : HasDerivAt u (f (-τ) (u (-τ))) (-τ) := h (-τ)` — instantiation of the hypothesis at the time-reversed point. This is the "u' = f(t, u(t)) à -τ" step in the official solution.
3. `have h_comp : HasDerivAt (fun s => u (-s)) (f (-τ) (u (-τ)) * (-1 : ℝ)) τ := h_u.comp τ h_neg` — the chain rule, exactly as named in the official solution. `HasDerivAt.comp` is the Mathlib name for the chain rule on `HasDerivAt`; the multiplicand `* (-1)` reflects the derivative of the inner map.
4. `have h_rw : f (-τ) (u (-τ)) * (-1 : ℝ) = -f (-τ) (u (-τ)) := by ring; rw [h_rw] at h_comp; exact h_comp` — the official solution's `-u'(-τ) = -f(-τ, u(-τ))` is a one-line algebraic rewrite, certified by `ring` over a named identity, then propagated by `rw`.

**Backward direction** (mirror): the official solution observes that `\widehat{\widehat{u}} = u` (double time-reversal recovers the original). The Lean script makes this symmetry explicit:

1. `h_neg : HasDerivAt (fun s : ℝ => -s) (-1) t` — same chain-rule setup at `t`.
2. `h_v : HasDerivAt (fun s => u (-s)) (-f (- -t) (u (- -t))) (-t) := h (-t)` — the assumed derivative of `v = u ∘ neg` instantiated at `-t`.
3. `h_comp := h_v.comp t h_neg` — chain rule applied to `v ∘ neg`, which is pointwise `u`.
4. `h_fun : (fun s => (fun r => u (-r)) (-s)) = u := by funext s; simp` and `h_val : (-f (- -t) (u (- -t))) * (-1) = f t (u t) := by rw [neg_neg]; ring` — the two rewrites that collapse `v ∘ neg` to `u` and `(-f(t, u t)) * (-1)` to `f(t, u t)`. The `rw [neg_neg]` step is the named-rewrite version of the official solution's "`-(-t) = t`" — not absorbed into `simp` or `norm_num`.

The bidirectional sweet spot is preserved: every move named in the official solution corresponds to a named Lean operation (`HasDerivAt.neg`, `HasDerivAt.comp`, `neg_neg`, `ring`), and the funext rewrite for the involution `s ↦ -(-s) = s` is a single line.

## Self-classification

(a) — Faithful transcription. The four moves of the official solution (chain rule on `s ↦ -s`, instantiation of the ODE hypothesis at the reversed point, composition, algebraic simplification) are in bijection with the four `have` lines per direction. The `constructor` split mirrors the official solution's "réciproquement" symmetry. No `<;>` chains, no `simp_all`, no `nlinarith` shotgun. The chain rule is named explicitly via `HasDerivAt.comp` rather than left to `fun_prop` or `simp` to discover.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages`: **0 errors, 0 warnings, 0 infos** — kernel-clean.
- `mcp__lean-lsp__lean_verify` on `subq_III_5_a`:
  - `axioms`: `["propext", "Classical.choice", "Quot.sound"]` — Mathlib-standard, no `sorryAx`, no `Lean.ofReduceBool` (i.e. no `native_decide` smuggling).
  - `warnings`: `[]`.
- `mcp__lean-lsp__lean_goal` at line 44 (final `exact h_comp` of the backward direction):
  - `goals_before`: `⊢ HasDerivAt u (f t (u t)) t`
  - `goals_after`: `[]` — closed by named hypothesis assembled through the chain.
- `mcp__lean-lsp__lean_multi_attempt` at line 42 confirmed `rw [neg_neg]; ring` is the minimal transcription-readable closure for `(-f (-(-t)) (u (-(-t)))) * (-1) = f t (u t)`. Alternatives: `simp [neg_neg]` closes (one tactic, but absorbs both the involution and the sign flip into a single black-box pass); `ring` alone fails (it does not unfold `-(-t)`); `simp; ring` produces a "no goals to be solved" warning (`simp` already closed the goal). `rw [neg_neg]; ring` separates the two named moves cleanly.

44 lines, no `<;>` cascade, no `decide`, no `aesop`, no `fun_prop`. The chain rule and the involution are each visible as a separate named operation.

## Comparaison directe avec Goedel PASS att10 (most representative G-a1 (a))

Goedel att10 (98 lines, `n_have = 44`, `uses_constructor = True`, `uses_simp = True`, `uses_ring = True`, `uses_ring_nf = True`, `uses_norm_num = True`) is structurally `(a)` in the seed robustness sub-agent classification but instructive to compare.

### Forward direction

Goedel att10:
```lean4
have h₁ : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) τ := by
  simpa using (hasDerivAt_id τ).neg
have h₂ : HasDerivAt u (f (-τ) (u (-τ))) (-τ) := h (-τ)
have h₃ : HasDerivAt (fun s => u (-s)) (f (-τ) (u (-τ)) * (-1 : ℝ)) τ := by
  have h₄ : HasDerivAt (fun s => u (-s)) (f (-τ) (u (-τ)) * (-1 : ℝ)) τ := HasDerivAt.comp τ h₂ h₁
  exact h₄
have h₄ : (f (-τ) (u (-τ)) * (-1 : ℝ)) = -f (-τ) (u (-τ)) := by ring
convert h₃ using 1
<;> simp [h₄]
<;> ring
```

The structural skeleton is identical to transcription (the four named moves are present: `h₁` chain-rule lemma, `h₂` ODE instantiation, `h₃` composition, `h₄` algebraic rewrite). Three syntactic noise patterns:

- `simpa using (hasDerivAt_id τ).neg` instead of `(hasDerivAt_id τ).neg`. The `simpa` is unnecessary — the term has the right type. RL closure-tuning artifact.
- `h₃` is wrapped in a redundant `have h₄ := HasDerivAt.comp τ h₂ h₁; exact h₄` indirection instead of just `:= h₂.comp τ h₁`.
- The final close is `convert h₃ using 1 <;> simp [h₄] <;> ring`. The `<;>` cascade is the prohibited shotgun. transcription uses `rw [h_rw] at h_comp; exact h_comp` — a single named rewrite plus exact, two tactics, no `<;>`.

### Backward direction

Goedel att10's backward direction is 70+ lines of nested `have` chains repeating the same content under different variable names (`h₁₀` through `h₃₅`, terminating in a working chain-rule application identical in spirit to transcription but buried in dead bindings). The actual mathematical content is:

```lean4
have h₂₉ : u = (fun s => u (-s)) ∘ (fun s : ℝ => -s) := by funext s; simp [neg_neg] <;> ring_nf
rw [h₂₉]
have h₃₀ : HasDerivAt ((fun s => u (-s)) ∘ (fun s : ℝ => -s)) ((-f t (u t)) * (-1 : ℝ)) t :=
  HasDerivAt.comp t h₃₂ h₃₁
have h₃₁ : ((-f t (u t)) * (-1 : ℝ)) = f t (u t) := by ring
convert h₃₀ using 1 <;> simp [h₃₁] <;> ring_nf
```

This is the same four-move skeleton (involution rewrite via `funext`, chain rule, algebraic close, propagation). Goedel arrives at the move; transcription writes it once. The 70-line nesting `h₁₂ := by have h₁₃ := h₁₀; have h₁₄ := h₁₁; have h₁₅ := h₁₃; ...` is pure RL token bloat with zero mathematical content — a reverse-reader auditing the script must skip 50+ lines before finding the move that the official solution names in one sentence.

### Summary table

| | chain-rule lemma | ODE instantiation | composition | algebraic close | total lines | classification |
|---|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `(hasDerivAt_id τ).neg` direct term | `h (-τ)` direct term | `h_u.comp τ h_neg` direct dot-call | `ring` + `rw [neg_neg]; ring` named | **44** | (a) clean |
| **Goedel att10** | `simpa using (hasDerivAt_id τ).neg` | `h (-τ)` direct | `HasDerivAt.comp τ h₂ h₁` wrapped in dead `have h₄ := ...; exact h₄` | `convert ... <;> simp [...] <;> ring` cascade | **98** (with ~50 lines dead nesting in backward direction) | (a) bruité, with structural redundancy |
| **Kimina** | n/a (0 PASS on this theorem) | n/a | n/a | n/a | n/a | n/a |

Both kernel-equivalent. Both pass. Same axiom footprint. The bidirectional gradient is structural: transcription writes the chain rule once per direction; Goedel writes it once per direction surrounded by RL closure-tuning noise (`simpa`, redundant rebindings, `<;>` chains, repeated identity have-chains in the backward direction). Kimina has 0 PASSes, i.e. cannot reach this proof at all in 60 attempts.

## Implications

### Pour AITP v7

1. **Le critère bidirectionnel discrimine sur P11.III.5.a**: transcription et Goedel sont tous deux `(a)` mais avec un facteur 2,2× sur les lignes (44 vs 98) et un facteur ≥3 sur les `have` mathématiquement-actifs vs total `have` (Goedel a `n_have = 44`, dont ~30 sont des rebindings vides dans la backward direction). Le ratio `n_have_actifs / n_lines` est un proxy mécanique de la bidirectionalité.
2. **Kimina 0/60 sur ce théorème**: confirme l'observation v6 que Kimina, calibrée sur des compétitions arithmétiques, échoue radicalement sur les théorèmes d'analyse réelle nécessitant un appel explicite au chain rule via `HasDerivAt.comp`. Goedel passe ici parce qu'il a vu plus de Mathlib analyse pendant le RL.
3. **Le `<;>` cascade est l'empreinte RL la plus visible**: Goedel emploie `<;> simp [h₄] <;> ring` deux fois (forward et backward) là où transcription utilise `rw [...] at h_comp; exact h_comp` (deux tactiques séquentielles, aucun `<;>`). Le `<;>` est facilement détectable mécaniquement et constitue un indicateur lisibilité-bruit auditable sans subjectivité.

### Pour WDWFT

L'objection "le chain rule est inévitablement opaque en Lean parce que `HasDerivAt.comp` est lui-même un objet technique" est désamorcée par cet artefact:

- Le script transcription nomme le chain rule comme `h_u.comp τ h_neg`. C'est *un* dot-call, *un* identifiant Mathlib (`HasDerivAt.comp`), traçable directement vers la phrase official solution "par la règle de la chaîne". La technicité est concentrée en un point lexical, pas dispersée.
- La `funext` pour l'involution `s ↦ -(-s) = s` (backward direction) est explicite — c'est exactement la phrase official solution `\widehat{\widehat{u}} = u` ou "réciproquement, on applique l'argument à `\widehat{u}`".
- La rewrite `rw [neg_neg]` est la version Lean du calcul official solution `-(-t) = t`. Une lectrice mathématicienne reconnaît `neg_neg` comme nom de l'identité d'involution; aucune recherche tactique n'a été cachée.

Phrasing pour WDWFT (P11.III.5.a, time-reversal in ODEs):

> *Sur P11.III.5.a (le théorème de renversement du temps `u' = f(t, u) ⇔ \widehat{u}'(τ) = -f(-τ, \widehat{u}(τ))`), le script transcription-fidèle inscrit chacun des quatre mouvements official solutions (chain-rule sur `s ↦ -s`, instantiation de l'hypothèse au point réversé, composition, simplification algébrique) en un seul `have` ou un seul terme-application Lean nommé. Le script Goedel reproduit la structure mais avec `simpa using` superflu, indirections `have h₄ := ...; exact h₄`, et `<;>` cascades pour la propagation finale — 98 lignes contre 44 pour la même preuve kernel. Kimina ne passe sur aucune des 60 tentatives. La hiérarchie 0-PASS / (a) bruité / (a) propre observée sur P11.III.5.a généralise l'inversion v6: la qualité du certificat décroît du humain (transcription) au RL surentraîné closure-orienté (Goedel) au RL spécialisé compétitions (Kimina), exactement dans cet ordre.*
