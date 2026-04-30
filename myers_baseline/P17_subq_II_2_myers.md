# Myers-style transcription of Mercier–Rombaldi P17, sub-question II.2

The Lean 4 script at `P17_subq_II_2_myers.lean` realises the corrigé's three named moves as three syntactically distinct Lean operations, each readable back into the informal text without re-derivation. The theorem states that under the tent map `f(x) = 1 − |2x − 1|` on `[0, 1]`, `x ∈ ℚ ⇔ f(x) ∈ ℚ`.

## Corrigé route (page_025.tex, item 2 of partie II)

The corrigé proceeds via the equivalence chain `f(x) ∈ ℚ ⇔ 1 − |2x − 1| ∈ ℚ ⇔ |2x − 1| ∈ ℚ ⇔ 2x − 1 ∈ ℚ ⇔ x ∈ ℚ`. Operationally — and this is the form actually used in the Lean transcription — the énoncé (page_006.tex) gives the piecewise expansion: `f(x) = 2x` on `[0, 1/2]`, `f(x) = 2 − 2x` on `]1/2, 1]`. Three named moves: (1) case-split on `x ≤ 1/2` vs `x > 1/2`; (2) compute `f x` per case via `abs_of_nonpos` / `abs_of_nonneg`; (3) transport rationality through the affine map (witness `2*q` or `2 − 2*q` forward; `q/2` or `1 − q/2` backward).

## Script structure

The script opens with `obtain ⟨hx0, hx1⟩ := hx` to expose the interval bounds, then `constructor` splits the `↔`. Each direction is handled by an explicit `rcases le_or_gt x (1/2 : ℝ) with hxle | hxgt` — the corrigé's case-split inscribed as a single Lean tactic with the named hypothesis `hxle : x ≤ 1/2` (or `hxgt : 1/2 < x`) entering the local context. Inside each branch:

- The sign condition is named: `have h_nonpos : 2 * x - 1 ≤ 0 := by linarith` (resp. `h_nonneg : 0 ≤ 2 * x - 1`). This is the corrigé's intermediate observation, not absorbed into automation.
- The absolute value is rewritten as a named identity: `have h_abs : |2 * x - 1| = -(2 * x - 1) := abs_of_nonpos h_nonpos` (resp. `abs_of_nonneg`). The Mathlib lemma name is the corrigé's move.
- The piecewise formula is named: `have h_fx : f x = 2 * x := by rw [hf x, h_abs]; ring` (resp. `f x = 2 - 2 * x`). The closing tactic `ring` is a normaliser that certifies the algebraic identity once the rewrite chain has reduced `f x` to its scalar form; it does not search.
- The rational witness is explicit: `refine ⟨2 * q, ?_⟩` forward, `refine ⟨q / 2, ?_⟩` backward (or the symmetric variants in the upper branch). The closing rewrite uses `push_cast` to align `(2 * q : ℚ)` and `(2 * (q : ℝ))`, then `ring`.

Backward direction reuses the same case-split scaffold: `h_fx : f x = 2 * x`, then from `hq : f x = ↑q` deduces `h_2x : 2 * x = ↑q` and `h_x_eq : x = ↑q / 2` (via `linarith`), and concludes with `refine ⟨q / 2, _⟩; rw [h_x_eq]; push_cast; ring`. A reverse-reader scanning the script meets exactly the corrigé's three sentences in order: case-split, piecewise formula, rational inversion.

## Self-classification

(a) — Faithful Myers transcription. The script's `rcases le_or_gt`, `abs_of_nonpos` / `abs_of_nonneg`, and explicit `refine ⟨2 * q, _⟩` / `refine ⟨q / 2, _⟩` witnesses are in bijection with the three named corrigé moves. Sign conditions and piecewise formulas are inscribed as `have` steps in the local context, not absorbed into a closing tactic. No `<;>` cascades, no `simp_all`, no `field_simp`. Closing tactics are `ring`, `linarith`, and `push_cast; ring` — each acting on already-named hypotheses.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` on the file: **0 errors, 0 warnings, 0 infos** (kernel-verified).
- `mcp__lean-lsp__lean_goal` at line 42 (just before the forward `refine` in the `x ≤ 1/2` branch):
  - context contains `hxle`, `h_nonpos`, `h_abs`, `h_fx` named; goal is `∃ q, f x = ↑q`.
- `mcp__lean-lsp__lean_goal` at line 82 (last `ring` of the backward `x > 1/2` branch):
  - context contains all five `have` steps named (`h_nonneg`, `h_abs`, `h_fx`, `h_2x`, `h_x_eq`); goal is the trivial `1 - ↑q / 2 = 1 - ↑q / 2`, closed by `ring`. `goals_after`: `[]`.
- Length: 82 lines / ~3.0 K chars total. Below mean Kimina (73 lines, 2.4 K chars) only by a small margin once header/comments are stripped.

## Comparaison directe avec scripts ML générés (P17.subq_II_2)

Per the `INDEX.md` of `/home/dxwoo/Code/AITP/rerun4/seed_robustness/per_theorem/P17.subq_II_2/`: 58 PASSes total (35 Goedel + 23 Kimina), with a perfect arm split — Goedel 35/35 classified (b), Kimina 23/23 classified (a). The arms share the same case-split skeleton; divergence is concentrated in scaffold depth and closing-tactic verbosity.

### Goedel attempt 01 (PASS, classified (b) — G-b1 sub-style, 33/35 of Goedel)

```lean4
have h_main : (∃ q : ℚ, x = (q : ℝ)) ↔ (∃ q : ℚ, f x = (q : ℝ)) := by
  ...
  refine' ⟨1 - |(2 * q - 1 : ℚ)|, _⟩
  norm_cast at h₃ ⊢
  <;> simp_all [hf]
  <;> ring_nf at *
  <;> norm_num at *
  <;> linarith
...
exact h_main
```

Two structural deviations from the corrigé:

- The `have h_main := by ...; exact h_main` wrapper is universally present (33/35 Goedel files) and absent from both the Myers script and from every Kimina PASS (0/23). It adds an extra layer of indirection — the user reads the script, hits a `have`, must follow the binder to the body, returns to the `exact h_main` to confirm closure. Pure scaffold, no semantic content.
- Closing tactics in the forward direction use the rational witness `1 - |(2 * q - 1 : ℚ)|` — i.e., the absolute-value formula is *kept inside the rational witness itself*, then closed by a 4–5-tactic shotgun (`norm_cast <;> simp_all <;> ring_nf <;> norm_num <;> linarith`). The corrigé's piecewise inversion `f(x) = 2x` (resp. `2 − 2x`) never appears as a named step; it is *implicit* in the witness shape and recovered by automation. A reverse-reader cannot extract `f(x) = 2x` from the script without executing it.

The case-split structure *is* preserved (Goedel 27/35 use `by_cases h : x ≤ 1/2`), so the route is shared at the skeleton level. But scaffold + arithmetic shotgun together obscure the corrigé's named moves.

Verdict: route-aligned, scaffold-bloated, arithmetically opaque.

### Kimina attempt 15 (PASS, classified (a) — K-a1 sub-style, 15/23 of Kimina)

```lean4
by_cases h2 : x ≥ 1 / 2
· -- x ≥ 1/2
  have h3 : 2 * x - 1 ≥ 0 := by linarith
  have hfx : f x = 2 - 2 * x := by
    rw [hf]
    rw [abs_of_nonneg h3]
    ring
  rw [hfx]
  have h_eq2 : x = (q : ℝ) := by linarith
  refine ⟨(2 : ℚ) - 2 * q, by ...⟩
```

Structurally near-identical to the Myers script:

- Same `by_cases` on `x ≥ 1/2` (vs Myers' `rcases le_or_gt`, semantically equivalent).
- Sign condition named (`h3 : 2 * x - 1 ≥ 0`).
- Piecewise formula named (`hfx : f x = 2 - 2 * x := by rw [hf]; rw [abs_of_nonneg h3]; ring`) — exact same three-step rewrite chain as Myers' `h_fx`.
- Rational witness explicit (`refine ⟨(2 : ℚ) - 2 * q, _⟩`).
- Closing tactic is `linarith` or `norm_num`, not a shotgun (Kimina `simp_all` 2/23, `field_simp` 1/23).

The structural difference Myers vs Kimina is essentially zero on this theorem. The two scripts are kernel-equivalent and bidirectional-equivalent. The only minor delta is that Kimina occasionally invokes `nlinarith` (12/23) where Myers prefers `linarith` — a cosmetic difference, both close on already-named hypotheses.

Verdict: structurally and epistemically aligned with the corrigé. (a) classification confirmed.

## Hiérarchie observée sur P17.subq_II_2

| | case-split nommé | sign condition nommée | piecewise `f x = ...` nommé | rational witness explicite | closure | classification |
|---|---|---|---|---|---|---|
| **Myers (Claude/lean-lsp)** | `rcases le_or_gt x (1/2)` | `have h_nonpos := by linarith` | `have h_fx : f x = 2*x := by rw [hf, h_abs]; ring` | `refine ⟨2*q, _⟩` etc. | `push_cast; ring` | (a) parfait |
| **Kimina att15** (K-a1) | `by_cases h2 : x ≥ 1/2` | `have h3 := by linarith` | `have hfx := by rw [hf]; rw [abs_of_nonneg h3]; ring` | `refine ⟨2 - 2*q, _⟩` | `linarith` | (a) parfait |
| **Goedel att01** (G-b1) | `by_cases h : x ≤ 1/2` (présent mais enveloppé dans `have h_main`) | absorbée dans `nlinarith` puis re-exposée plus loin | absent — la formule reste implicite dans le witness `1 - \|2*q - 1\|` | `refine' ⟨1 - \|(2*q - 1 : ℚ)\|, _⟩` | `norm_cast <;> simp_all <;> ring_nf <;> norm_num <;> linarith` | (b) bruité |

Three preuves kernel-équivalentes, three profils bidirectionnels distincts. The Myers and Kimina-K-a1 scripts are tightly aligned; the Goedel-G-b1 script preserves the case-split but smuggles the piecewise formula into the witness term, where the corrigé's intermediate computation is no longer recoverable by reading.

## Lecture — implications pour WDWFT

Sur P17.subq_II_2, l'arm split Goedel 35/35 (b) vs Kimina 23/23 (a) est *structural*, pas stochastique. La distinction se localise sur quatre observables binaires:

1. **`have h_main` wrapper** présent (Goedel 94%) vs absent (Kimina 0%).
2. **Piecewise formula** comme `have` nommé (Kimina) vs absorbée dans le witness term (Goedel).
3. **Closing tactic** mono- (`linarith`/`norm_num`, Kimina 91%) vs cascade 4–5-tactic (Goedel 89%).
4. **`field_simp` + `simp_all`** dans la fermeture (Goedel 33/35 + 31/35) vs essentiellement absents (Kimina 1/23 + 2/23).

Chacun des quatre observables est mécaniquement détectable par grep ou `lean_diagnostic_messages` — le critère bidirectionnel n'est pas une intuition de lecteur, c'est un *invariant syntaxique* du script. Le script Myers ici se positionne au pôle (a) sur les quatre dimensions: pas de wrapper, piecewise nommé, fermeture mono-tactique (`ring` ou `linarith`), aucun `simp_all` / `field_simp`.

Phrasing pour WDWFT (révisé après cette expérimentation et celle de P12):

> *La bidirectionnalité d'un script tactique se mesure par la préservation des mouvements nommés du corrigé comme opérations Lean nommées. Sur P17.subq_II_2 (`x ∈ ℚ ⇔ f(x) ∈ ℚ` pour la tente), le script Myers-fidèle (`rcases le_or_gt`; `have h_nonpos`; `have h_abs := abs_of_nonpos`; `have h_fx`; `refine ⟨2*q, _⟩`; `ring`) inscrit chacun des trois mouvements corrigés (case-split, formule par morceaux, inversion linéaire) en un `have` ou un appel de lemme nommé. Le script Kimina typique reproduit la structure quasi à l'identique. Le script Goedel typique préserve la case-split mais absorbe la formule par morceaux dans le witness rationnel `1 - |2*q - 1|`, fermé par cascade `simp_all <;> field_simp <;> ring_nf <;> norm_num <;> linarith` — la formule `f(x) = 2x` n'est jamais énoncée, le lecteur ne peut la reconstruire sans exécuter le script. Les trois preuves sont kernel-équivalentes; seules les deux premières satisfont le critère bidirectionnel.*

L'inversion P17.subq_II_2 (Kimina > Goedel sur (a)) confirme que l'arm-ranking n'est pas constant à travers les théorèmes: Kimina domine ici, Goedel dominait sur P12. Le critère bidirectionnel est *par-théorème*, ce qui rend l'analyse mécanique d'autant plus utile pour l'évaluation WDWFT à grande échelle.
