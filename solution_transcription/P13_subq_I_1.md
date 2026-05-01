# Solution transcription of Mercier-Rombaldi P13, question I.1

The Lean 4 script at `P13_subq_I_1.lean` realises the official solution's six named moves as six syntactically distinct Lean operations, each readable back into the informal text without re-derivation. The theorem asserts existence and uniqueness of `u ∈ [0, 1]` such that `f_n(u) = 0`, where `f_n(x) = (∑ k ∈ range n, x^(k+1)) - 1`.

The official solution route is: (i) `f_n(0) = -1`, (ii) `f_n(1) = n - 1 ≥ 0` using `1 ≤ n`, (iii) `f_n` continuous on `[0, 1]` (polynomial-continuity), (iv) IVT yields existence, (v) strict monotonicity yields uniqueness, (vi) combine into `∃!`. The transcription script inscribes each move as a named `have` block, then closes the `∃!` by trichotomy on `y` versus the IVT-witness `u`.

Move (i) is `have h_f0 : f n 0 = -1`; closed by `Finset.sum_eq_zero` plus `zero_pow (Nat.succ_ne_zero k)` for each summand `0^(k+1) = 0`. The `Nat.succ_ne_zero k` invocation is the algebraic content "the exponent `k+1` is positive, so `0^(k+1)` collapses"; no `simp` shotgun. Move (ii) is `have h_f1 : f n 1 = (n : ℝ) - 1` with the inner sum collapsing under `simp` (single-tactic, on a sum of constants — not the proof's load-bearing automation), followed by `have h_f1_nn : 0 ≤ f n 1` whose closure uses `exact_mod_cast hn` to cast `1 ≤ n` to `(1 : ℝ) ≤ (n : ℝ)`, then `linarith`. The hypothesis `hn` is *named* in the closure, not absorbed.

Move (iii) is `have h_cont : ContinuousOn (f n) (Set.Icc 0 1)`. The structural decomposition `ContinuousOn.sub` (sum minus constant) and `continuousOn_finset_sum` (finite sum of continuous functions) appears explicitly; each summand `x^(k+1)` is closed by `(continuousOn_id).pow (k + 1)`. This is the official solution's "polynomial-continuity" inscribed as a *named* sequence of structure lemmas, not a `continuity` tactic shotgun (Kimina's choice).

Move (iv) is `have h_ivt : ∃ u ∈ Set.Icc 0 1, f n u = 0`, closed by `intermediate_value_Icc h01 h_cont` applied to `0 ∈ Icc (f n 0) (f n 1)`. The IVT lemma is the canonical `intermediate_value_Icc` from `Mathlib.Topology.Order.IntermediateValue`, whose signature is `a ≤ b → ContinuousOn f (Icc a b) → Icc (f a) (f b) ⊆ f '' Icc a b`. This is the *named* official solution invocation, not Kimina's variant `Continuous.exists_eq_of_le_of_le` (which works on `Continuous` rather than `ContinuousOn` and is a non-canonical IVT formulation).

Move (v) is `have h_strict_mono`, closed by `Finset.sum_lt_sum_of_nonempty` (range is nonempty since `n ≥ 1`) plus `pow_lt_pow_left₀ hxy hx (Nat.succ_ne_zero k)` term-wise. Goedel and Kimina both reach for `Finset.sum_lt_sum` (the weaker variant requiring a witness `k₀` of strict inequality), which forces them to additionally prove `0 ∈ range n` and the per-`k` non-strict inequality. `Finset.sum_lt_sum_of_nonempty` directly takes the strict per-term inequality plus nonemptiness — exactly the official solution's argument shape.

Move (vi) is the `∃!`-closure: `obtain ⟨u, hu_mem, hu_eq⟩ := h_ivt; refine ⟨u, ⟨..., ?_⟩; rintro y ⟨hy0, hy1, hy_eq⟩; rcases lt_trichotomy y u with hlt | heq | hgt`. Three cases: `y < u`, `y = u`, `y > u`. The first two close by `h_strict_mono` + `linarith`; the middle closes by `exact heq`. This trichotomy is the natural translation of the official solution's "strictly increasing ⇒ at most one root", and avoids the Goedel/Kimina pattern of `by_contra` followed by `lt_or_gt_of_ne`.

## Self-classification

(a) — Faithful transcription. The script's six `have` / closing blocks are in bijection with the six named official solution moves; the IVT lemma `intermediate_value_Icc` is named (not buried in a tactic cascade); the strict monotonicity is closed via `pow_lt_pow_left₀` + `Finset.sum_lt_sum_of_nonempty` (named, term-wise); the `∃!` closure uses `lt_trichotomy` (named, three cases) rather than `by_contra` + `lt_or_gt_of_ne`. No `simp_all`, no `field_simp`, no multi-`try` cascade. The structural shape matches the target skeleton exactly.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` sur le fichier: **0 errors, 0 warnings, 0 infos** (preuve kernel-vérifiée, file 73 lines).
- `mcp__lean-lsp__lean_run_code` avec `#print axioms subq_I_1`: dépend uniquement de `[propext, Classical.choice, Quot.sound]` — les trois axiomes Mathlib standard, pas de `sorry`, pas d'axiome ajouté.
- `mcp__lean-lsp__lean_goal` à la ligne 73 (juste avant la dernière `linarith`): contexte avec `h_strict_mono`, `hu_eq : f n u = 0`, `hy_eq : f n y = 0`, et `this : f n u < f n y` ⇒ `linarith` ferme par contradiction sur les égalités à 0 et l'inégalité stricte. Aucun `nlinarith`, aucun hint-list.
- `mcp__lean-lsp__lean_goal` à la ligne 59 (intérieur de `h_strict_mono`): goal `x ^ (k + 1) < y ^ (k + 1)` avec `hx : 0 ≤ x`, `hxy : x < y`, `k ∈ Finset.range n` ⇒ fermé par `pow_lt_pow_left₀ hxy hx (Nat.succ_ne_zero k)` (3 arguments nommés, pas de `nlinarith`).

## Comparaison directe avec scripts ML générés (5 PASSes total)

### Goedel attempt 01 (PASS, classifié (b) par INDEX.md)

```lean4
have h_strict_mono : ∀ (x y : ℝ), 0 ≤ x → x < y → y ≤ 1 → f n x < f n y := by sorry
have h_continuous : ContinuousOn (f n) (Set.Icc 0 1) := by sorry
have h_f0 : f n 0 < 0 := by sorry
have h_f1 : 0 ≤ f n 1 := by sorry
have h_exists : ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ f n u = 0 := by
  ...
  apply intermediate_value_Icc (by norm_num) h₁
  constructor <;>
  (try norm_num) <;> (try linarith) <;>
  (try { cases n with | zero => contradiction
    | succ n => simp_all [f_def, Finset.sum_range_succ, pow_succ]
                <;> norm_num at * <;> linarith }) <;>
  ... (×4 cascade duplications)
have h_unique : ∀ u₁ u₂, ... := by
  by_contra h
  ...
  cases' lt_or_gt_of_ne h₃ with h₃ h₃
  · ...; have h₆ : f n u₁ = 0 := by tauto; ...
  · ...; have h₆ : f n u₁ = 0 := by tauto; ...
```

Goedel reproduit la structure top-level (six blocs `have` analogues aux six mouvements official solutions) mais ajoute du bruit syntaxique RL closure-tuning massif:

- **Cascade IVT side-conditions**: la condition `0 ∈ Icc (f n 0) (f n 1)` est dischargée par une cascade de quatre `try { cases n with ... simp_all [f_def, Finset.sum_range_succ, pow_succ] <;> norm_num at * <;> linarith }`, chacune dupliquant le travail. Le transcription script remplace cette cascade par une ligne: `⟨h_f0_neg, h_f1_nn⟩`.
- **`tauto` pour extraction**: Goedel utilise `f n u₁ = 0 := by tauto` pour extraire un membre de la conjonction. Le transcription script utilise `rintro y ⟨hy0, hy1, hy_eq⟩` au point d'introduction, exposant chaque composant nommément.
- **Duplication du `by_contra`**: l'argument d'unicité est écrit deux fois (cas `u₁ < u₂` et `u₁ > u₂`) au lieu de la trichotomie à trois branches.
- **Verbosité**: 210 lignes vs transcription 73 lignes (ratio 2.9×).

Verdict: structurellement préservé (les six moves sont là), syntaxiquement bruité — la cascade `try { ... } <;> ...` cache le mouvement IVT au lieu de l'inscrire.

### Goedel attempts 32, 44 (PASSes, classifiées (b))

Structurellement identiques à att01 (même squelette en six `have`, même cascade `simp_all` + `cases n` pour les side-conditions IVT, même duplication `by_contra` pour l'unicité). Les variations sont cosmétiques: att32 utilise `h_main_existence`/`h_main_uniqueness` comme noms top-level; att44 utilise `continuousOn_id.pow` (plus court que la version `ContinuousOn.sum` + `ContinuousOn.pow` dépliée). Aucune ne nomme un `StrictMonoOn`, aucune n'utilise `lt_trichotomy`.

### Kimina attempt 08 (PASS, classifié (a) par INDEX.md)

```lean4
have h7 : Continuous (fun x : ℝ => f n x) := by
  funext x; rw [f_def]; continuity
...
apply Continuous.exists_mem_set_of_le_of_lt_of_continuous
· exact h7
· norm_num
· exact h8
· exact h9
...
by_cases h15 : d < c
· ...; apply h12 d c; all_goals nlinarith
by_cases h17 : d > c
· ...; apply h12 c d; all_goals nlinarith
· have h21 : d = c := by linarith; linarith
```

Kimina utilise `Continuous` (continuité globale via la tactique `continuity`) au lieu de `ContinuousOn`. Le lemme IVT invoqué est `Continuous.exists_mem_set_of_le_of_lt_of_continuous` — un nom non-canonique (le canonique est `intermediate_value_Icc` pour `ContinuousOn` ou `Continuous.exists_eq_of_le_of_le` pour `Continuous`). L'unicité est traitée par `by_cases h15 : d < c` puis `by_cases h17 : d > c`, avec dans le else implicite `d = c`. C'est une trichotomie déguisée en deux `by_cases` — fonctionnellement équivalent à `lt_trichotomy` mais structurellement moins lisible.

Verdict: les six moves sont préservés, le squelette logique est correct, mais l'invocation IVT cible un lemme non-canonique et la `continuity`-tactique opacifie la décomposition polynomiale.

### Kimina attempt 48 (PASS, classifié (a))

Utilise `Continuous.exists_eq_of_le_of_le` (encore un nom non-canonique pour IVT, mais différent de att08). L'unicité utilise `by_cases h15 : v < u` / `by_cases h16 : v > u` (même pattern que att08). Les sommes sont fermées par `Finset.sum_lt_sum` (la variante "weak ineq + witness of strict ineq") au lieu de `Finset.sum_lt_sum_of_nonempty` (la variante "strict per-term + nonempty"). Cela force Kimina à prouver explicitement `0 ∈ range n` et la borne non-stricte par `pow_le_pow_left` en plus de la stricte par `pow_lt_pow_left`. Le transcription script évite ce duplicat en utilisant `Finset.sum_lt_sum_of_nonempty` qui ne demande que la version stricte.

Verdict: trois recherches CoT distinctes pour le lemme IVT (Goedel: `intermediate_value_Icc`; Kimina att08: `exists_mem_set_of_le_of_lt_of_continuous`; Kimina att48: `exists_eq_of_le_of_le`) suggèrent que le nom canonique n'est pas saturé dans le pre-training. Le transcription script récupère le canonique au premier appel `lean_leansearch`.

## Hiérarchie observée sur P13.subq_I_1

| | f_n(0)=-1 nommé | f_n(1)=n-1 nommé | continuité nommée | IVT nommé | strict mono nommée | unicité par |
|---|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | `have h_f0` + `Finset.sum_eq_zero` + `zero_pow` | `have h_f1` + `simp` interne | `ContinuousOn.sub` + `continuousOn_finset_sum` + `.pow` | `intermediate_value_Icc` (canonique) | `Finset.sum_lt_sum_of_nonempty` + `pow_lt_pow_left₀` | `lt_trichotomy` |
| **Goedel att01** | absorbé dans cascade `simp_all [f_def, sum_range_succ, pow_succ]` | absorbé dans cascade idem | `ContinuousOn.sub` + `.sum` + `.pow` (nommé) | `intermediate_value_Icc` (canonique) mais condition par cascade `try { cases n; simp_all; norm_num; linarith }` ×4 | inline dans `by_contra` | `by_contra` + `lt_or_gt_of_ne` (deux cas dupliqués) |
| **Goedel att32, 44** | idem att01 | idem att01 | idem att01 | idem att01 | idem att01 | idem att01 |
| **Kimina att08** | absorbé dans `simp` | absorbé dans `simp` + induction interne | `continuity` (shotgun) sur `Continuous` | `Continuous.exists_mem_set_of_le_of_lt_of_continuous` (non-canonique) | inline dans `by_cases` | `by_cases <` + `by_cases >` (trichotomie déguisée) |
| **Kimina att48** | `simp` interne | induction sur `n` avec `Finset.sum_range_succ` (route-aligné) | `continuity` (shotgun) | `Continuous.exists_eq_of_le_of_le` (non-canonique différent de att08) | `Finset.sum_lt_sum` (weak+witness) avec `pow_le_pow_left` *et* `pow_lt_pow_left` | `by_cases <` + `by_cases >` |

Cinq preuves kernel-équivalentes. Cinq profils bidirectionnels distincts. La gradation est observable par lecture (présence/absence des `have` nommés et de l'IVT canonique), mécaniquement vérifiable par lean-lsp (`#print axioms` confirme zéro `sorry`, `lean_goal` confirme la fermeture par hypothèses nommées sans hint-list), et auditable.

## Implications

### Pour AITP v7

1. **La métrique est calibrée sur un théorème à 6 mouvements**: avec un humain (Claude jouant transcription) en input + instruction "transcription fidèle", la sortie est (a) parfait (six `have` nommés en bijection avec les six mouvements). Le critère bidirectionnel n'est pas saturé par bruit de mesure même sur des théorèmes plus longs (P13 vs P12 a deux fois plus de mouvements).
2. **Inversion des arms confirmée à plus haute résolution sur IVT**: Goedel (3/3 PASSes) classés (b) — IVT nommé canonique mais side-condition par cascade `simp_all`. Kimina (2/2 PASSes) classés (a) par INDEX.md — mais les deux Kimina utilisent des **noms IVT non-canoniques différents** entre eux. Ce point a été omis dans l'analyse INDEX.md initiale: "weakly bidirectional" cache que ni att08 ni att48 n'invoquent le lemme canonique `intermediate_value_Icc`. Le transcription le récupère.
3. **`Finset.sum_lt_sum_of_nonempty` vs `Finset.sum_lt_sum`**: distinction sub-tactique observable. La première est *exactement* la formulation official solution ("tous strictement, donc somme stricte"), la seconde requiert un certificat plus faible (un seul k strict + tous les autres faibles) qui n'apparaît pas dans le official solution. Goedel et Kimina utilisent systématiquement la deuxième.
4. **Ground truth artefact**: ce fichier `.lean` peut être publié dans le repo `lean-prover-bidirectionality` comme baseline P13.I.1, kernel-vérifié et auditable.

### Pour WDWFT

Cet artefact répond à l'objection "la bidirectionalité ne distingue rien sur des théorèmes longs":

- Le script transcription est mécaniquement vérifiable (kernel + `lean_goal` confirme la fermeture par hypothèses nommées sans hint-list).
- Le mapping mouvement-official solution → opération-Lean est traçable ligne-par-ligne sur six niveaux (pas seulement trois comme P12).
- La distinction transcription / Goedel / Kimina est *structurelle* (présence/absence des `have` nommés à chaque mouvement, choix canonique vs non-canonique pour IVT, `lt_trichotomy` vs `by_contra` vs `by_cases` dupliqués pour l'unicité), pas *stylistique*.

Phrasing pour WDWFT (P13 instance):

> *Sur P13.I.1 (existence et unicité d'un zéro de `f_n(x) = ∑ x^(k+1) - 1` dans `[0,1]` pour `n ≥ 1`), le script transcription-fidèle inscrit chacun des six mouvements official solutions en un `have` ou un appel de lemme nommé: `f_n(0) = -1` par `Finset.sum_eq_zero + zero_pow`, `f_n(1) = n - 1 ≥ 0` par cast nommé de `1 ≤ n`, continuité par décomposition `ContinuousOn.sub + finset_sum + pow`, IVT par le lemme canonique `intermediate_value_Icc`, monotonie stricte par `Finset.sum_lt_sum_of_nonempty + pow_lt_pow_left₀`, unicité par `lt_trichotomy`. Le script Goedel typique reproduit le squelette six-`have` mais ferme les side-conditions IVT par cascade `try { cases n; simp_all [f_def, sum_range_succ]; norm_num; linarith }` répétée quatre fois, et duplique l'argument d'unicité dans un `by_contra` à deux branches. Le script Kimina typique invoque IVT par un nom non-canonique (deux noms différents sur deux PASSes), utilise la tactique `continuity` au lieu de la décomposition explicite, et déguise la trichotomie en `by_cases <` + `by_cases >`. Les cinq scripts sont kernel-équivalents. Seul le premier satisfait le critère bidirectionnel.*
