# Solution transcription of Mercier-Rombaldi P4, sub-question III.1

The Lean 4 script at `P4_subq_P4_III_1.lean` realises the official solution's two named moves as two syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Official solution content (page 140, Partie III, III.1)

> L'application $d_A : M_n(\mathbb{C}) \to M_n(\mathbb{C})$ est linéaire, puisque pour tous $X, Y \in M_n(\mathbb{C})$ et tout $\lambda \in \mathbb{C}$,
> $d_A(X + \lambda Y) = A(X + \lambda Y) - (X + \lambda Y) A = (AX - XA) + \lambda(AY - YA) = d_A(X) + \lambda d_A(Y)$.
>
> et telle que :
> $d_A(XY) = AXY - XYA = (AX - XA)Y + X(AY - YA) = d_A(X) Y + X d_A(Y)$.

Two named moves: (1) the linearity decomposition `d_A = (X ↦ AX) − (X ↦ XA)` over the two pieces of bilinear matrix multiplication; (2) the Leibniz expansion via the cancellation identity `A·(X·Y) − (X·Y)·A = (AX − XA)Y + X(AY − YA)`, which holds in any noncommutative ring.

## transcription script structure

Move 1 (linearity) is inscribed by constructing `d` as the literal difference of two named Mathlib linear maps:

```lean4
let d : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A
```

`LinearMap.mulLeft ℂ A` is the Mathlib bundled linear map `X ↦ A * X`; `LinearMap.mulRight ℂ A` is `X ↦ X * A`. The official solution's sentence "`d_A` est linéaire car somme/différence de deux opérations bilinéaires" maps one-to-one onto this construction. No `LinearMap.mk` with handwritten `map_add'`/`map_smul'` is needed — the linearity is *imported* from named Mathlib lemmas, not re-proven via `simp`-cascades. The defining equation `d X = A * X - X * A` then closes by `rfl` because `(LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A) X` reduces definitionally to `A * X - X * A`.

Move 2 (Leibniz) is inscribed verbatim as the `have` corresponding to the official solution's central algebraic line:

```lean4
have h_leib :
    A * (X * Y) - (X * Y) * A
      = (A * X - X * A) * Y + X * (A * Y - Y * A) := by
  noncomm_ring
```

`noncomm_ring` is the noncommutative analog of `ring` — it normalises sums/differences/products in any (non-commutative) ring without assuming commutativity, which `ring` would falsely require here. The official solution identity is *the content* of the move; `noncomm_ring` is the certifier. A `change` then unfolds `d` to expose the goal as exactly the two sides of `h_leib`, closed by `exact h_leib`.

A reverse-reader scanning the script meets exactly the official solution's two sentences in order: linearity-as-difference-of-bilinear-pieces, Leibniz-as-cancellation-identity.

## Self-classification

(a) — Faithful transcription. The script's two operations are in bijection with the two named official solution moves; the Mathlib hooks `LinearMap.mulLeft` / `LinearMap.mulRight` carry the linearity move at the *correct* abstraction level (matrix multiplication is bilinear, Mathlib already knows this); the cancellation identity is written by hand as `h_leib` and discharged by the noncommutative ring normaliser. No `<;>` cascades, no `simp` shotguns, no `aesop`. The structural shape is exactly the target skeleton.

A reasonable objection: the Lean statement asks for a `LinearMap`, not a Mathlib `Derivation` — so the official solution's *naming* of the object as "une dérivation" is not preserved as a typeclass. This is a constraint of the JSONL theorem statement, not a degradation by the script. Within the LinearMap-typed target, the (a)-route *is* the `LinearMap.mulLeft − LinearMap.mulRight` construction. Per the prior analysis, 0/8 PASSes use Mathlib `Derivation` and all 8 use anonymous `LinearMap`; among the LinearMap-typed scripts, the present transcription is the named-bilinear-pieces variant.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` on the file: **0 errors, 0 warnings, 0 infos** after replacing the initial `show` with `change` (Mathlib style linter flags `show` when it actually changes the goal — here the unfolding of `let d` qualifies).
- `mcp__lean-lsp__lean_goal` at line 42 (just before `noncomm_ring`):
  - `goals_before`: `⊢ A * (X * Y) - X * Y * A = (A * X - X * A) * Y + X * (A * Y - Y * A)` — pure noncommutative-ring identity in `Matrix (Fin n) (Fin n) ℂ`.
  - `goals_after`: `[]` — closed.
- `mcp__lean-lsp__lean_multi_attempt` at line 42 over `["noncomm_ring", "ring", "simp [mul_sub, sub_mul, mul_assoc]; abel", "abel"]`:
  - `noncomm_ring`: closes (no goals).
  - `ring`: fails — `ring_nf made no progress on the goal`. Confirms matrices are noncommutative; `ring` is the wrong normaliser.
  - `simp [mul_sub, sub_mul, mul_assoc]; abel`: also closes but heavier; `abel` reports "No goals to be solved" because `simp` already finished.
  - `abel` alone: leaves the multiplicative identity unsolved, as expected (additive normaliser only).
  
  The minimal closer for the official solution identity is `noncomm_ring`. This is the right tool by definition: the move *is* a noncommutative-ring rewriting.

## Comparaison directe avec scripts ML générés (parmi les 8 PASSes P4.subq_P4_III_1)

### Goedel attempt 55 (PASS, classifié (b) par sub-agent)

Script structure (final, kernel-passing):

```lean4
use {
  toFun := fun X => A * X - X * A
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    <;>
    abel
  map_smul' := by
    intro c X
    simp [Matrix.mul_smul, Matrix.smul_mul, sub_smul, smul_sub]
    <;>
    ring_nf
    <;>
    simp_all [Complex.ext_iff, Matrix.mul_apply, Fin.sum_univ_succ]
    <;>
    norm_num
    <;>
    aesop
}
```

Goedel constructs the `LinearMap` anonymously via `LinearMap.mk` (anonymous structure) and discharges `map_add'` / `map_smul'` with `simp` + `<;>`-cascades into `abel` / `ring_nf` / `simp_all` / `norm_num` / `aesop`. The official solution sentence "linearity decomposes into two pieces of bilinear multiplication" is absent — it is replaced by a closure search over `simp` lemma sets. For Leibniz:

```lean4
simp [sub_mul, mul_sub]
<;>
simp_all [Matrix.mul_assoc]
<;>
ring_nf
<;>
simp_all [Matrix.mul_assoc]
<;>
abel
```

Five-tactic cascade. The cancellation identity `A(XY) − (XY)A = (AX − XA)Y + X(AY − YA)` is never written down. The `simp` rewrites and `abel` happen to close the kernel goal, but no named hypothesis records the move.

Verdict: structure absent in `map_add'`/`map_smul'` (the linearity is search-discharged, not bilinear-decomposed); Leibniz never named. (b) lower-abstraction.

### Kimina attempt 24 (PASS, classifié (b) par sub-agent)

Script structure (final, kernel-passing):

```lean4
use { toFun := fun X => A * X - X * A,
      map_add' := by
        intro X Y
        simp [Matrix.mul_add, Matrix.add_mul]
        all_goals try ring_nf
      map_smul' := by
        intro c X
        simp [Matrix.mul_smul, Matrix.smul_mul]
        all_goals try ring_nf
    }
constructor
· intro X
  rfl
· intro X Y
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  all_goals try ring_nf
```

Kimina is the *shotgun* version of Goedel: same anonymous `LinearMap` construction, but with `simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]; all_goals try ring_nf` for the entire Leibniz step. Three lemma names are passed to `simp`; `ring_nf` (the *commutative* normaliser, which here happens to succeed on the residual goal because the surviving terms commute) closes. Neither the bilinear decomposition of linearity nor the cancellation identity is inscribed. The Leibniz *content* is fully absorbed into the `simp` set + closure tactic.

Verdict: identité Leibniz utilisée mais jamais inscrite. Une lectrice ne peut pas reconstituer le official solution depuis ce script. (b) lower-abstraction, plus opaque que Goedel.

## Hiérarchie observée sur P4.subq_P4_III_1

| | linéarité nommée | identité Leibniz nommée | construction de `d` | classification |
|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A` (named bilinear pieces) | `have h_leib : ... := by noncomm_ring` | différence de deux LinearMaps Mathlib | (a) parfait |
| **Goedel att55** | absorbée dans `LinearMap.mk` + `simp <;> abel <;> ring_nf <;> simp_all <;> norm_num <;> aesop` | absorbée dans `simp [sub_mul, mul_sub] <;> simp_all <;> ring_nf <;> simp_all <;> abel` | anonymous structure | (b) opaque |
| **Kimina att24** | absorbée dans `LinearMap.mk` + `simp [...]; all_goals try ring_nf` | absorbée dans `simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]; all_goals try ring_nf` | anonymous structure | (b) opaque |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts. La gradation est observable par lecture, mécaniquement vérifiable par lean-lsp (présence/absence des `have`/`let` nommés et des Mathlib hooks `LinearMap.mulLeft`/`LinearMap.mulRight`), et auditable.

## Implications

### Pour AITP v7

1. **Le upper bound transcription-fidèle pour P4.III.1 est non-trivial mais court** : 30 lignes de Lean propre, deux moves nommés, pas de cascade. Le coût en effort humain (Claude jouant transcription) est dominé par la connaissance que `LinearMap.mulLeft`/`LinearMap.mulRight` existent — sans cette connaissance, la (a)-route s'effondre vers la (b)-route Goedel/Kimina.
2. **L'inversion v6 confirmée** : Goedel et Kimina convergent vers la même architecture `LinearMap.mk` + cascades. Aucun des 8 PASSes n'utilise `Derivation` ou `LinearMap.mulLeft`. Le critère bidirectionnel les classe tous (b), conformément à l'analyse INDEX.md.
3. **`noncomm_ring` est le bon test bidirectionnel pour P4** : `ring` *échoue* (vérifié par multi_attempt), donc choisir `noncomm_ring` n'est pas une décoration stylistique — c'est la reconnaissance que la structure mathématique est noncommutative. Goedel/Kimina contournent cette reconnaissance en passant à `simp` + `ring_nf` (qui sur le résidu post-`simp` ne voit plus que des termes commutatifs).

### Pour WDWFT

Cet artefact répond à l'objection "la bidirectionalité est triviale quand le official solution est court" :

- Sur P4.III.1, le official solution est court (~6 lignes algébriques) mais la bidirectionalité n'est *pas* triviale : Goedel (3275 chars de script) et Kimina (895 chars) produisent des artefacts kernel-équivalents mais structurellement opaques.
- Le mapping mouvement-official solution → opération-Lean (linéarité ↔ `mulLeft − mulRight`, Leibniz ↔ `noncomm_ring` sur l'identité de cancellation) est traçable ligne-par-ligne dans le script transcription et absent dans les scripts ML.
- La distinction transcription / Goedel / Kimina est *structurelle* (présence/absence de `LinearMap.mulLeft`, présence/absence du `have h_leib`), pas *stylistique*.

Phrasing pour WDWFT (formulation P4-spécifique) :

> *La bidirectionalité d'un script tactique se mesure par la préservation des mouvements nommés du official solution comme opérations Lean nommées. Sur P4.III.1 (`d_A : X ↦ AX − XA` est une dérivation), le script transcription-fidèle (`let d := LinearMap.mulLeft ℂ A − LinearMap.mulRight ℂ A; have h_leib := by noncomm_ring`) inscrit chacun des deux mouvements official solutions en une opération nommée. Le script Goedel typique reproduit la signature mais absorbe les deux mouvements dans un `LinearMap.mk` + cinq tactiques en cascade. Le script Kimina typique fait de même en plus court, en s'appuyant sur `simp; all_goals try ring_nf` — la commutativité fortuite du résidu post-`simp` masque que le problème originel est noncommutatif. Les trois scripts sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel.*
