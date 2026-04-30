# Myers-style transcription of Mercier–Rombaldi P9, sub-question 22 — winding-number invariance under reparametrisation

## Verdict

**(failed) — kernel-blocked at Move 3 by a transcription gap in the énoncé and a Mathlib API gap.**

Both blockers are documented below. The failure is informative: it confirms that this theorem is the corpus's **ceiling case** in the strong sense — not "Myers can do it but ML provers can't", but "Myers can faithfully name the corrigé moves yet still hits a wall that no current LLM-based prover could plausibly cross either, because the wall is partly in the énoncé and partly in Mathlib".

The accompanying `.lean` file at `/home/dxwoo/Code/AITP/lean_corpus/LeanCorpus/P9_subq_22_myers.lean` is structurally a Myers transcription with the three corrigé moves named in comment blocks; only `sorry` closes the theorem. The file compiles with a single `declaration uses 'sorry'` warning.

## The corrigé proof (page 351–352)

The corrigé picks `[a, b]` of length `l_w` (a period of `w`), a `C¹` increasing diffeomorphism `φ : [0, l_z] → [a, b]` such that `z = w ∘ φ`, then proceeds in three named moves:

**Move 1 — Substitution of variables.** Chain rule on `z = w ∘ φ` plus `φ' > 0` yields:
```
e^(i α(t)) = z'(t) / |z'(t)|
           = w'(φ t) · φ'(t) / |w'(φ t) · φ'(t)|
           = w'(φ t) / |w'(φ t)|
           = e^(i β(φ t))
```
on `[0, l_z]`.

**Move 2 — Lift uniqueness mod 2π.** From Move 1, `t ↦ k_t = (α(t) − β(φ(t)))/(2π)` is integer-valued. Continuity of `α` and `β ∘ φ` on the connected set `[0, l_z]` plus integer-valuedness implies `k_t` is constant.

**Move 3 — Endpoint difference.**
```
α(l_z) − α(0) = β(φ l_z) − β(φ 0)               [from Move 2]
              = β(b) − β(a)                      [b = φ l_z, a = φ 0]
              = α_w(l_w) − α_w(0)                [by Q21]
```

The Q21 step (period-shift invariance of the rotation index) is what bridges `β(b) − β(a)` (a length-`l_w` interval at offset `a`) to `α_w(l_w) − α_w(0)` (a length-`l_w` interval at offset `0`).

## Blocking diagnosis

### Blocker A — énoncé transcription gap (load-bearing).

The corrigé fixes:
- `[a, b]` with `b − a = l_w`,
- `φ : [0, l_z] → [a, b]` a `C¹` diffeomorphism, hence `φ(0) = a` and `φ(l_z) = b`.

The Lean statement provides:
- `φ : ℝ → ℝ` smooth, `StrictMono`, with smooth inverse `ψ`,
- `z = w ∘ φ` everywhere on ℝ.

The Lean statement does **not** provide `φ(0) = 0`, `φ(l_z) = l_w`, nor any normalisation that would tie `φ`'s endpoint values to `α_w`'s domain `[0, l_w]`. From the matching of periods one can derive `φ(t + l_z) = φ(t) + l_w` (using `z = w ∘ φ`, periodicity of both, and `l_z`/`l_w` minimality), so `φ(l_z) = φ(0) + l_w` — but `φ(0)` itself is unconstrained.

This means: **the lift values `α_w(φ 0)` and `α_w(φ l_z)` referred to by Move 1 are only meaningful if `φ 0, φ l_z ∈ [0, l_w]`**, which the statement does not enforce. Outside `[0, l_w]`, `α_w` is, formally, a function `ℝ → ℝ` constrained nowhere — junk.

### Blocker B — Mathlib API gap (Q21 absent).

Even granting an extension `α̃_w : ℝ → ℝ` of `α_w` to a coherent lift on all of ℝ — which would itself require constructing a global continuous lift à la Q16 — the equality
```
α̃_w(φ 0 + l_w) − α̃_w(φ 0) = α_w(l_w) − α_w(0)
```
for arbitrary `φ 0 ∈ ℝ` is the content of **Q21** (period-shift invariance). Q21 is not a hypothesis. Mathlib v4.30.0-rc2 has:
- `Complex.exp_eq_exp_iff_exists_int` (uniqueness of lift mod 2π) — present.
- `Circle.exp_eq_exp` (variant) — present.
- `IsPreconnected.constant`, `IsPreconnected.constant_of_mapsTo` — present.
- `HasDerivAt.comp` (chain rule) — present.
- `strictMono_of_hasDerivAt_pos` and the converse — present.

But Mathlib does **not** have:
- A "rotation index of a regular periodic curve" definition as `(α(l) − α(0))/(2π)`.
- Period-shift invariance of any such index.
- Topological invariance of the rotation index under reparametrisation of the support.

The closest relevant Mathlib infrastructure (`CircleDeg1Lift`, `Real.Angle`, `Complex.arg`) handles instantaneous arguments and translation-number theory for circle homeomorphisms, not parametric curves' rotation indices.

### Classification of the move blockages

| Move | Blocker | Mathematically content-rich? | API-bound? |
|---|---|---|---|
| 1 (substitution) | énoncé gap (`φ t` may exit `[0, l_w]`) | yes — chain rule is content, but the **applicability** to `α_w(φ t)` is what fails | partly: Mathlib has the chain rule and `0 < φ' t` |
| 2 (lift uniqueness) | none, conditionally on Move 1's output | no — pure API closure (`exp_eq_exp_iff_exists_int`, `IsPreconnected.constant`) | **fully closable** if Move 1 gives the input |
| 3 (endpoint difference) | Q21 absent + énoncé gap for `φ 0`, `φ l_z` | **yes** — Q21 is its own non-trivial sub-question (period-shift invariance) | yes — Mathlib has no winding-number-of-curve API |

### Synthesis

The hardness here is **not** a failure of Myers-style transcription. The corrigé moves are nameable and the `.lean` file names them. The hardness is:

1. A **transcription bug** in the énoncé encoding (the Lean statement is strictly weaker than the corrigé statement, omitting `φ(0) = 0` or equivalent).
2. A **content-rich missing lemma** (Q21) that is itself a separate sub-question of the original problem.
3. A **Mathlib coverage hole** for parametric-curve winding numbers.

A sound Myers transcription would require one of:
- Strengthening the Lean statement to include `φ(0) = 0`, `φ(l_z) = l_w` (or the equivalent for the reparametrisation), making Move 3 a substitution.
- Pre-establishing Q21 as a lemma in `LeanCorpus.P9` and threading it as a hypothesis.
- Reformulating the goal to mention the rotation index abstractly and proving topological invariance via the `Real.Angle` lifting machinery (substantial Mathlib augmentation).

## Comparison to Goedel and Kimina results

- **Goedel attempt (0/64 PASS)**: provers had no chance because the corrigé moves are simultaneously content-rich (Q21 is not a Mathlib lemma) and statement-blocked (the énoncé does not give `φ(0) = 0`). Tactic-search cannot synthesise a missing Q21 from local hypotheses.
- **Kimina attempt (1/64, Lake-truncated false positive)**: the single PASS is a build artefact, not a real closure. Kimina's `nlinarith`-style shotgun cannot bridge a topological invariance argument over a connected interval.

The Myers-faithful artefact (this file) reaches the same wall as Goedel and Kimina — not because Claude+lean-lsp is insufficient, but because the wall is *external* to the prover-versus-prover comparison: the énoncé encoding is strictly weaker than the corrigé statement, and the corrigé proof relies on a non-trivial lemma (Q21) that is not in Mathlib and not threaded as a hypothesis.

## Implications for WDWFT (the bidirectionality paper)

This is a clean **boundary case** for the bidirectionality criterion:

1. The corrigé moves can be **named** in the Lean file (Moves 1, 2, 3 appear as commented section headers with explicit Mathlib API references). A reverse-reader scanning the file meets the corrigé's three sentences in order.

2. The moves **cannot be instantiated** as `have`-bound operations because the Lean type-checker rejects ill-typed substitutions (`α_w (φ 0)` where `φ 0 ∉ [0, l_w]`), and because the closing lemma (Q21) is not in Mathlib.

3. The **diagnosis is mechanically auditable**: the .lean file compiles with a single `sorry` warning; lean-lsp `lean_diagnostic_messages` confirms no other errors. The structural failure is at the named, locatable junction (Move 3 closing).

This contrasts with the typical ML-prover failure mode (Goedel, Kimina) which is **opaque**: a tactic-search timeout reveals nothing about which corrigé move blocked or why. The Myers route's failure is **diagnostic** — it identifies the énoncé gap and the Mathlib gap as separable concerns.

A claim defensible at WDWFT: bidirectionality is not a binary "transcribable / not-transcribable" property of theorems, but a graded property whose granularity is exposed by attempting Myers transcription. P9.subq_22 lies on the boundary: its corrigé is *nameable* (Moves 1/2/3 have clear referents) but not *closable* in Mathlib v4.30.0-rc2 from the énoncé as encoded. The failure is informative for both directions: it specifies what would need to be added to Mathlib (a rotation-index theory) and what would need to be added to the énoncé encoding (`φ(0) = 0` or equivalent) for full bidirectional closure.

## Verification

- File `/home/dxwoo/Code/AITP/lean_corpus/LeanCorpus/P9_subq_22_myers.lean`:
  - `lean_diagnostic_messages`: 0 errors, 1 warning (`declaration uses 'sorry'` at line 28), 0 infos.
  - The `sorry` is at the end of the proof, after the three Move comment blocks.
- Copy at `/home/dxwoo/Code/AITP/rerun4/myers_baseline/P9_subq_22_myers.lean`.

## Self-classification

**(failed)** — Myers cannot close this theorem in Mathlib v4.30.0-rc2 from the énoncé as stated. The proof is admitted at Move 3 (endpoint difference), with the precise blockers being:

- (énoncé gap) `φ(0) = 0` and `φ(l_z) = l_w` are not hypotheses, so Move 1's "`α_w (φ t)`" is ill-typed as a lift evaluation.
- (Mathlib gap) Q21 (period-shift invariance of the rotation index) is not a Mathlib lemma and not a threaded hypothesis.
- (content-rich) Q21 is itself a non-trivial sub-result of P9, mathematically prior to Q22.

The failure is consistent with Goedel 0/64 and Kimina 1/64 (truncated false-positive): no tactic-search prover could synthesise the missing Q21 from the local hypotheses, and no statement-level rewriting could resolve the missing `φ(0) = 0`. The failure is therefore evidence that this theorem requires either a Mathlib augmentation (rotation-index theory) or an énoncé strengthening (additional hypotheses on `φ`) to be reachable — and **this is itself a publishable finding** about the texture of corpus-level reach.
