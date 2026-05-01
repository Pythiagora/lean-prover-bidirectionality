# Solution transcription of Mercier-Rombaldi P11, question I.3.b

The Lean 4 script at `P11_subq_I_3_b.lean` realises the official solution's three named moves as syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Official solution text (page_010.tex, lines 25–27)

> **(b)** Comme $q$ est strictement positif, la fonction $\varphi$ est à valeurs positives ou nulles (c'est une somme de carrés) et $p \ge 0$. Si $p = 0$, on a $u_1^2(t) + \frac{q}{2} u_1^4(t) + u_2^2(t) = 0$ pour tout réel $t$, ce qui équivaut à dire que $u_1(t) = u_2(t) = 0$ puisque tous les termes de la somme sont positifs ou nuls.

Three named moves:

1. **"Somme de carrés ⇒ chaque terme ≥ 0"**: each of $u_1^2$, $\tfrac{q}{2} u_1^4$, $u_2^2$ is non-negative.
2. **"$p \ge 0$"**: the sum of three non-negatives equals $p$, hence $p \ge 0$.
3. **"$p = 0$ ⇒ chaque terme = 0 ⇒ $u_1(t) = u_2(t) = 0$"**: when the sum vanishes, each non-negative summand vanishes, and $u_i(t)^2 = 0 \Leftrightarrow u_i(t) = 0$.

## Mapping official solution moves → Lean operations

The script splits the conjunction with `refine ⟨?_, ?_⟩` and treats each conjunct in order.

**First conjunct ($p \ge 0$).** Move 1 is inscribed as four named non-negativity hypotheses:
```lean4
have h_u1_sq_nn : 0 ≤ (u₁ 0) ^ 2 := sq_nonneg _
have h_u2_sq_nn : 0 ≤ (u₂ 0) ^ 2 := sq_nonneg _
have h_u1_4_nn  : 0 ≤ (u₁ 0) ^ 4 := by
  have : (u₁ 0) ^ 4 = ((u₁ 0) ^ 2) ^ 2 := by ring
  rw [this]; exact sq_nonneg _
have h_q_term_nn : 0 ≤ (q / 2) * (u₁ 0) ^ 4 := mul_nonneg h_q_half_nn h_u1_4_nn
```
Each non-negativity is a separate `have` with a Mathlib lemma name (`sq_nonneg`, `mul_nonneg`); the $u_1^4 \ge 0$ step explicitly factors $u_1^4 = (u_1^2)^2$ as the official solution's "somme de carrés" suggests, rather than invoking `positivity` as a black box. Move 2 is then a single `linarith` over the named hypotheses plus `h0 := hp 0` — bookkeeping over named facts, not pattern-matching against guessed squares.

**Second conjunct ($p = 0 \Rightarrow \forall t, u_1(t) = u_2(t) = 0$).** After `intro hp_zero t`, the same four non-negativity facts are reproduced at the symbolic time $t$, then Move 3 splits in two sub-steps:
```lean4
have h_u1_sq_zero : (u₁ t) ^ 2 = 0 := by linarith
have h_u2_sq_zero : (u₂ t) ^ 2 = 0 := by linarith
refine ⟨sq_eq_zero_iff.mp h_u1_sq_zero, sq_eq_zero_iff.mp h_u2_sq_zero⟩
```
The "tous les termes sont positifs ou nuls" half of the official solution's reasoning is `linarith` working on three non-negativity hypotheses and the sum-equals-zero hypothesis (no nonlinear search). The "$u_i^2 = 0 \Leftrightarrow u_i = 0$" half is the named lemma `sq_eq_zero_iff` — the canonical Mathlib statement of exactly the official solution's implication, applied with `.mp`. A reverse-reader scanning the script meets the official solution's three sentences in order: each-term-nonneg, sum-pins-each-to-zero, square-zero-implies-zero.

## Self-classification

**(a) — Faithful transcription.** The script's named `have`s and closing lemmas are in bijection with the three official solution moves. The three non-negativities are written individually with named Mathlib lemmas (`sq_nonneg`, `mul_nonneg`), not absorbed into a `positivity` call. The conclusion `u_i(t) = 0` from `(u_i t)^2 = 0` is a direct application of `sq_eq_zero_iff` — the named lemma corresponding exactly to the official solution's invocation of "tous les termes sont positifs ou nuls". `linarith` is used twice, in both cases as bookkeeping over already-named non-negativity hypotheses, never with a hint-list of guessed squares.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` on the file: **0 errors, 0 warnings, 0 infos** (kernel-verified, first attempt, no iteration required).
- `mcp__lean-lsp__lean_goal` at line 25 (just before the first `linarith`):
  - `goals_before`: context with `h0`, `h_u1_sq_nn`, `h_u2_sq_nn`, `h_u1_4_nn`, `h_q_half_nn`, `h_q_term_nn` named; goal `0 ≤ p`.
  - `goals_after`: `[]` — closed cleanly by `linarith` over the named hypotheses.
- `mcp__lean-lsp__lean_goal` at line 46 (last `exact sq_eq_zero_iff.mp h_u2_sq_zero`):
  - `goals_before`: context with `h_u2_sq_zero : u₂ t ^ 2 = 0`; goal `u₂ t = 0`.
  - `goals_after`: `[]` — closed by the named iff lemma applied with `.mp`.
- `mcp__lean-lsp__lean_multi_attempt` at line 25: `linarith` closes; `nlinarith` also closes (overpowered for this goal); `positivity` **fails** (cannot prove `0 ≤ p` because `p` is not syntactically a non-negative expression — it is a free variable equal to a sum of squares only via `h0`). The minimal closing tactic in the named context is `linarith`.
- `mcp__lean-lsp__lean_multi_attempt` at line 46: `exact sq_eq_zero_iff.mp h_u2_sq_zero` closes; `nlinarith [sq_nonneg (u₂ t), h_u2_sq_zero]` also closes (shotgun alternative). The transcription script deliberately chooses the named iff lemma over the shotgun.

## Significance — the (a) target was open on P11.I.3.b

Per prior analysis of the 114 PASS scripts on P11.I.3.b across the AITP rerun4 model panel, **all 114** classify as (b) — the closing tactic is invariably `nlinarith [sq_nonneg ..., sq_nonneg ..., ...]` with a hint-list of guessed squares, sometimes wrapped in a `constructor` split but with no `have` chain naming the official solution's moves. The official solution's structural skeleton — *each term non-negative; sum non-negative; sum-zero forces each term zero; squared-zero forces zero* — is absorbed into the `nlinarith` search. A reverse-reader cannot reconstruct the official solution from any of those 114 PASSes.

This transcription script demonstrates that **(a) is achievable on P11.I.3.b**. The three official solution moves are inscribed as named operations:
- Move 1: four `have h_*_nn` lines, each a named Mathlib lemma application.
- Move 2: `linarith` over named hypotheses (no hint-list, no `nlinarith`).
- Move 3: `linarith` (sum-zero ⇒ each-zero, named context) followed by `sq_eq_zero_iff.mp` (named iff).

The 114/114 (b) rate is therefore **not** a property of the theorem — it is a property of the model panel's tactic-distribution under standard prompting. The transcription proves the upper bound is reachable, calibrating the bidirectional metric for this theorem.

## Hiérarchie observée sur P11.I.3.b

| | non-négativité nommée | $p \ge 0$ | sum-zero ⇒ term-zero | square-zero ⇒ term-zero | classification |
|---|---|---|---|---|---|
| **transcription (Claude/lean-lsp)** | 4× `have ... := sq_nonneg / mul_nonneg` | `linarith` | `linarith` | `sq_eq_zero_iff.mp` | (a) |
| **Typical PASS (n=114)** | absorbée dans hint-list | `nlinarith [sq_nonneg ...]` | absorbée | absorbée | (b) shotgun |

Two kernel-equivalent classes of proof. Only the first preserves the official solution's named structure as named Lean operations.

## Files

- `.lean` (project): `/home/dxwoo/Code/AITP/lean_corpus/LeanCorpus/P11_subq_I_3_b.lean`
- `.lean` (rerun4 archive): `/home/dxwoo/Code/AITP/rerun4/solution_transcription/P11_subq_I_3_b.lean`
- `.md` synthesis (this file): `/home/dxwoo/Code/AITP/rerun4/solution_transcription/P11_subq_I_3_b.md`
- Official solution source: `/home/dxwoo/Code/AITP/Problem_11/latex/pages/page_010.tex`, lines 25–27.
