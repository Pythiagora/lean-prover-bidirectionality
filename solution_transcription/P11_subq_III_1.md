# Solution transcription of Mercier-Rombaldi P11, sub-question III.1

The Lean 4 script at `P11_subq_III_1.lean` realises the official solution's two named moves as two syntactically distinct Lean blocks, each readable back into the informal text without re-derivation.

## Official solution text (verbatim, page 020.tex line 35-39)

> **1.** En notant $M = \sup\limits_{t \in \,]p, q[} |g'(t)|$ et en utilisant le théorème des accroissements finis, on a pour tous $x, y$ dans $\,]p, q[$ :
> $$|g(x) - g(y)| = |x - y| |g'(\xi)| \le M |x - y| \xrightarrow[(x, y) \to (q, q)]{} 0.$$
> On déduit alors du critère de Cauchy que la fonction $g$ admet une limite finie en $q$.

Two named moves: (1) **MVT / accroissements finis** giving the Lipschitz bound; (2) **critère de Cauchy** + completeness of ℝ giving the limit.

## Move-by-move mapping

| Official solution move | Lean operation | Mathlib lemma |
|---|---|---|
| MVT / accroissements finis: $\|g(x) - g(y)\| \le M\|x - y\|$ on $\,]p, q[$ | `have h_lip : LipschitzOnWith M.toNNReal g (Set.Ioo p q) := h_conv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le h_dwa h_bdd_nn` | `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` (Mathlib.Analysis.Calculus.MeanValue) |
| critère de Cauchy: image of a Cauchy filter under uniformly-continuous-on map is Cauchy | `have h_cauchy_map := h_cauchy_nhds.map_of_le h_uc h_le_principal` | `Cauchy.map_of_le` + `LipschitzOnWith.uniformContinuousOn` |
| ℝ complète ⇒ limite finie | `exact (cauchy_map_iff_exists_tendsto).mp h_cauchy_map` | `cauchy_map_iff_exists_tendsto` (Mathlib.Topology.UniformSpace.Cauchy) |

The "MVT" of the official solution is precisely `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`: the Mathlib name *contains* `MeanValue` in its module path. The two moves of the two-line official solution are inscribed as two named `have` blocks (`h_lip`, `h_cauchy_map`), with two minor preliminaries (`hM_nn` to lift `|g' t| ≤ M` to `M ≥ 0`, and `h_le_principal` to express that the left-neighbourhood filter is contained in the principal filter of $\,]p, q[$).

The final discharge `(cauchy_map_iff_exists_tendsto).mp h_cauchy_map` is the formal statement of "ℝ is complete + Cauchy filter has a limit". No `nlinarith`, no hint-list, no shotgun automation.

## Self-classification

(a) — Faithful transcription. The two `have` blocks (`h_lip`, `h_cauchy_map`) and the closing `cauchy_map_iff_exists_tendsto.mp` are in bijection with the official solution's three logical steps: MVT bound, Cauchy criterion application, completeness conclusion. The intermediate hypotheses (`hM_nn`, `h_conv`, `h_dwa`, `h_bdd_nn`, `h_uc`, `h_cauchy_nhds`, `h_le_principal`) are bookkeeping required by the typed Mathlib API (NNReal lifts, convexity, the conversion from `HasDerivAt` to `HasDerivWithinAt`, the principal-filter containment) — none of them invoke search or guessing. The pivot lemma names appear by hand, not via tactic hint-lists.

A reverse-reader scanning the script meets exactly the two official solution sentences in order: the MVT-Lipschitz bound, then the Cauchy-completeness conclusion.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages`: **0 errors, 0 warnings, 0 infos**. Kernel-verified.
- `mcp__lean-lsp__lean_verify subq_III_1`: axioms `[propext, Classical.choice, Quot.sound]` — standard Mathlib trio only. No `sorry`, no `native_decide`, no extras.
- `mcp__lean-lsp__lean_goal` à la dernière ligne: `goals_before` montre les hypothèses `h_lip`, `h_uc`, `h_cauchy_nhds`, `h_le_principal`, `h_cauchy_map` toutes en contexte; `goals_after` = `[]`. Fermé proprement.

## Mathlib API notes

- `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` (Mathlib.Analysis.Calculus.MeanValue): exactly the named MVT-Lipschitz lemma. Constraint: needs `‖f'(x)‖₊ ≤ C` with `C : NNReal`. Lifting `|g' t| ≤ M` (`M : ℝ`) to `‖g' t‖₊ ≤ M.toNNReal` requires `0 ≤ M`, which itself follows from `g'_bdd` evaluated at any midpoint of `Ioo p q`.
- `cauchy_map_iff_exists_tendsto` (Mathlib.Topology.UniformSpace.Cauchy): the goal-pattern match is exact — `Cauchy (map g (𝓝[<] q)) ↔ ∃ ℓ, Tendsto g (𝓝[<] q) (𝓝 ℓ)`. Needs `[CompleteSpace ℝ]` (instance) and `(𝓝[<] q).NeBot` (instance via `nhdsLT_neBot` for `[NoMinOrder ℝ]`).
- `nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b` (Mathlib.Topology.Order.OrderClosed): used to rewrite `𝓝[<] q` as `𝓝[Ioo p q] q`, after which `inf_le_right` discharges the principal-filter containment (since `𝓝[s] x = 𝓝 x ⊓ 𝓟 s` by definition).

The Mathlib API for this theorem is **complete**: no gaps, no missing lemmas, no manual reconstruction of MVT or Cauchy-completeness needed. Both named official solution moves have direct Mathlib counterparts under names that semantically reflect the moves (`MeanValue`, `Cauchy`, `complete`).

## WDWFT signal — ceiling-case data point

Both Goedel and Kimina produced **0 PASSes in 128 attempts** on this theorem at K=64/32k. The transcription compiles in **a single iteration** (one `nhdsWithin_le_principal` typo discharged via `inf_le_right`).

This is direct WDWFT evidence: the official solution's two named moves **DO** have faithful Mathlib transcriptions. The provers' failure is not a Mathlib API gap — the API is complete, the named lemmas exist, the route is two-line. The provers' failure is at the level of *premise selection / structural reasoning over named operations*: they could not retrieve `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` and `cauchy_map_iff_exists_tendsto` and chain them, even though both are bog-standard analysis-foundation lemmas.

In the bidirectionality vocabulary: the **upper bound** (a) is achievable on this theorem; the SOTA neural provers operate so far below the upper bound that they collapse to 0% pass-rate on a problem whose official solution is two sentences. This is the WDWFT gap in its sharpest form — the gap between *named-move retrieval* and *spaghetti-tactic search*.

### Phrasing for WDWFT (revised, this theorem)

> *On Mercier-Rombaldi P11.III.1 ("a function with bounded derivative on $\,]p, q[$ admits a limit at $q^-$"), the official solution is two sentences: MVT giving an $M$-Lipschitz bound, then the Cauchy criterion plus completeness of $\mathbb{R}$. Both named moves have direct Mathlib transcriptions: `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le` and `cauchy_map_iff_exists_tendsto`. The transcription-style script we exhibit compiles in a single iteration, with two named `have` blocks in structural bijection with the two official solution sentences. Goedel and Kimina, the SOTA neural provers, both produce 0 PASSes in 128 attempts at K=64/32k on this theorem. The Mathlib API is complete; the named lemmas exist; the route is short. The failure is at the level of premise selection over named operations, not at the level of the formal library. This is the WDWFT gap: a official solution that a domain expert reads as two named moves becomes, for current neural provers, computationally inaccessible — the bidirectional structure that makes the proof legible to a human is the same structure that retrieval-based provers cannot reproduce.*
