# Myers-style transcription of Mercier-Rombaldi P9, sub-question 4 (continuity-of-Φ sub-lemma)

The Lean 4 script at `P9_subq_4_myers.lean` realises the corrigé's four named moves as four syntactically distinct Lean operations, each readable back into the informal text without re-derivation.

## Corrigé context

In Mercier-Rombaldi's I.B.4 (page 323), the segment `[α, β]` does not meet ℝ; the corrigé introduces the rational fraction
`F(X) = (Re α + X · Re(β − α)) / (Im α + X · Im(β − α))`
and observes that `F` admits no pole in `[0, 1]` because the denominator's vanishing would force the segment to cross ℝ — contradiction. From this it concludes `I_0^1(F) = 0` and hence `I_{[α,β]} = 0`. The continuity of the real-valued evaluation `Φ : x ↦ F̃(x)` on `(0, 1)` is the implicit sub-step needed to invoke the Cauchy-index machinery on `F̃` (which presupposes `F̃` continuous at every interior point of `[0, 1]`).

The sub-lemma `subq_4` here isolates exactly this sub-step. The corrigé reasoning, broken into named moves:

1. The numerator `Re α + x · Re(β − α)` is linear in `x`, hence continuous.
2. The denominator `Im α + x · Im(β − α)` is linear in `x`, hence continuous.
3. The denominator does not vanish on `[0, 1]` — and in particular at any `x ∈ (0, 1) ⊂ [0, 1]` — by the geometric hypothesis `hno_meet`.
4. The quotient of two functions continuous at `x`, with non-vanishing denominator at `x`, is continuous at `x`.

## Lean transcription

The script after `intro Φ x hx_lo hx_hi` is in bijection with these four moves:

```lean4
have h_num_cont : ContinuousAt (fun x : ℝ => α.re + x * (β - α).re) x := by
  exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
have h_den_cont : ContinuousAt (fun x : ℝ => α.im + x * (β - α).im) x := by
  exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
have h_den_ne : α.im + x * (β - α).im ≠ 0 :=
  hno_meet x hx_lo.le hx_hi.le
exact h_num_cont.div h_den_cont h_den_ne
```

Each `have` is a named corrigé move:

- `h_num_cont` (Move 1): "linear in `x`, hence continuous" — built explicitly as `continuous_const.add (continuous_id.mul continuous_const)`. `continuous_const` is the constant `α.re`; `continuous_id` is the identity `x ↦ x`; `continuous_const` is again `(β − α).re`. The linear shape `c + id · c'` is inscribed verbatim in the term, not solved for by automation.
- `h_den_cont` (Move 2): same explicit chain for `Im α + x · Im(β − α)`.
- `h_den_ne` (Move 3): the geometric non-vanishing hypothesis is invoked by name — `hno_meet x hx_lo.le hx_hi.le` — with the inclusion `(0, 1) ⊂ [0, 1]` realised by the two `.le` coercions.
- The closing `exact h_num_cont.div h_den_cont h_den_ne` (Move 4) is `ContinuousAt.div`, the named Mathlib lemma stating exactly the corrigé's conclusion.

## Self-classification

(a) — Faithful Myers transcription. The script's four steps are in bijection with the four named corrigé moves; the linearity of numerator and denominator is built explicitly from `continuous_const` / `continuous_id` / `.add` / `.mul`, not synthesized by `fun_prop` or `continuity`; the non-vanishing is invoked by name from `hno_meet`; the closing tactic is the named `ContinuousAt.div` lemma.

The structural shape is exactly the target skeleton.

## Vérification kernel + lean-lsp

- `mcp__lean-lsp__lean_diagnostic_messages` on `P9_subq_4_myers.lean`: **0 errors**, 3 warnings (all unused-variable on `hα`, `hβ`, `hαβ` — these are part of the theorem's stated signature but not consumed by the continuity sub-lemma; they are needed in the full `segmentIndex α β = 0` proof of which `subq_4` here is a sub-step).
- `mcp__lean-lsp__lean_goal` at line 26 (immediately before the closing `exact`):
  - `goals_before`: context with `h_num_cont`, `h_den_cont`, `h_den_ne` named, target `ContinuousAt Φ x`.
  - `goals_after`: `[]` — closed cleanly by `h_num_cont.div h_den_cont h_den_ne` operating on three named hypotheses, no automation hint, no unification search.

## Comparaison directe avec scripts ML générés sur P9.subq_4

### Goedel attempt 00 (PASS)

```lean4
intro Φ x hx1 hx2
have h_denom_ne_zero : α.im + x * (β - α).im ≠ 0 := by
  have h₁ : 0 ≤ x := by linarith
  have h₂ : x ≤ 1 := by linarith
  have h₃ : α.im + x * (β - α).im ≠ 0 := hno_meet x h₁ h₂
  exact h₃

have h_num_continuous : ContinuousAt (fun x : ℝ => (α.re + x * (β - α).re : ℝ)) x := by
  have h₁ : ContinuousAt (fun x : ℝ => (α.re + x * (β - α).re : ℝ)) x := by
    have h₂ : Continuous (fun x : ℝ => (α.re + x * (β - α).re : ℝ)) := by
      continuity
    exact h₂.continuousAt
  exact h₁

have h_denom_continuous : ContinuousAt (fun x : ℝ => (α.im + x * (β - α).im : ℝ)) x := by
  -- analogous nested have-chain
  ...

have h_main : ContinuousAt Φ x := by
  have h₁ : ... := h_num_continuous
  have h₂ : ... := h_denom_continuous
  have h₃ : ... := by simpa [Complex.ext_iff, Complex.im, Complex.re] using h_denom_ne_zero
  have h₄ : ContinuousAt (fun x : ℝ => ...) x := by
    apply ContinuousAt.div h₁ h₂
    exact h₃
  simpa [Φ] using h₄

exact h_main
```

Goedel reproduces the four-move structure (denominator non-vanishing, numerator continuous, denominator continuous, quotient continuous) but with characteristic syntactic noise:

- The non-vanishing step re-derives `0 ≤ x` and `x ≤ 1` via `linarith` instead of using `hx_lo.le` / `hx_hi.le` — same content, three extra lines.
- Continuity of numerator/denominator is closed by the automation tactic `continuity`, then re-wrapped through an outer `Continuous → ContinuousAt` step. The named lemma chain `continuous_const.add (continuous_id.mul continuous_const)` is replaced by a search.
- The closing step uses `simpa [Complex.ext_iff, Complex.im, Complex.re]` to massage the non-vanishing hypothesis (unnecessary — both forms are definitionally equal); and `simpa [Φ]` for the let-unfold (also unnecessary — `Φ` reduces by `rfl`).
- Five layers of nested `have` instead of one flat sequence of four.
- 45 lines, 2286 chars vs Myers' 26 lines, 1528 chars (4 named moves + comments).

Verdict: structure preserved (the four moves are still nameable), syntactically bloated. The `continuity` tactic absorbs the explicit `.add` / `.mul` linearity skeleton.

### Kimina attempt 02 (PASS)

```lean4
intro Φ x hx1 hx2
have h1 : α.im + x * (β - α).im ≠ 0 := by
  specialize hno_meet x (by linarith) (by linarith)
  simpa using hno_meet
have h2 : ContinuousAt (fun y : ℝ => α.re + y * (β - α).re) x := by
  fun_prop
have h3 : ContinuousAt (fun y : ℝ => α.im + y * (β - α).im) x := by
  fun_prop
have h4 : ContinuousAt (fun y : ℝ => (α.re + y * (β - α).re) / (α.im + y * (β - α).im)) x := by
  apply ContinuousAt.div
  · exact h2
  · exact h3
  all_goals
    exact h1
have h5 : Φ = fun y : ℝ => (α.re + y * (β - α).re) / (α.im + y * (β - α).im) := by
  rfl
rw [h5]
exact h4
```

Kimina also produces four `have` statements, but Moves 1 and 2 are both closed by `fun_prop` — the *shotgun* form. `fun_prop` is a domain-specific automation tactic that searches the registered continuity database for a closing chain. It works here, but the explicit linearity skeleton (`continuous_const.add (continuous_id.mul continuous_const)`) is *invisible* in the script: a reverse-reader sees `fun_prop` and cannot recover which Mathlib lemma chain was used.

Other issues:

- `specialize hno_meet x (by linarith) (by linarith)` followed by `simpa using hno_meet` is a destructive rewrite (`specialize` mutates the hypothesis) plus an unnecessary `simpa` — the named lemma is already in the right shape. Three lines for what `hno_meet x hx_lo.le hx_hi.le` does in one line.
- The closing uses `all_goals exact h1` after `apply ContinuousAt.div` — defensive coding against what `apply` might unfold, instead of the projection-form `h2.div h3 h1`.
- An explicit `rfl`-reduction `have h5 : Φ = ... := by rfl` followed by `rw [h5]` is added — unnecessary because `Φ` is a `let` and reduces by `rfl` in `exact`.
- 23 lines, 885 chars.

Verdict: structure superficially preserved (four `have`s are present), but Move 1 and Move 2 are *opaque* — the linearity argument is delegated to `fun_prop`'s search. A reverse-reader cannot recover from the script which Mathlib continuity primitives are being chained.

## Hiérarchie observée sur P9.subq_4

|                        | Move 1 (num cont)            | Move 2 (den cont)            | Move 3 (den ne 0)              | Move 4 (quotient)         | Classification |
|------------------------|------------------------------|------------------------------|--------------------------------|---------------------------|----------------|
| **Myers (Claude/lean-lsp)** | `continuous_const.add (continuous_id.mul continuous_const)` | same explicit chain          | `hno_meet x hx_lo.le hx_hi.le` | `h_num_cont.div h_den_cont h_den_ne` | (a) parfait    |
| **Goedel att00**       | `continuity`                 | `continuity`                 | `hno_meet` + `linarith` re-derivation | `apply ContinuousAt.div` + `simpa [Φ]` wrapper | (a) bruité     |
| **Kimina att02**       | `fun_prop`                   | `fun_prop`                   | `specialize hno_meet ... ; simpa` | `apply ContinuousAt.div` + `all_goals` + `rfl`-rewrite | (a) opaque sur Moves 1–2 |

Trois preuves kernel-équivalentes. Trois profils bidirectionnels distincts:

- **Myers**: each move has a named term. The linearity of `c + id · c'` is *inscribed*. A reverse-reader can name what the script does at each line.
- **Goedel**: the four-move skeleton is preserved at the `have` level, but Moves 1–2 collapse into the `continuity` automation, and Moves 3–4 are buried under `simpa` rewrites that erase the direct projection-form chain. Reverse-readability of *which* continuity primitives are at play is lost.
- **Kimina**: same `have` skeleton, but the linearity argument vanishes into `fun_prop`. The script is shorter than Goedel but more opaque — `fun_prop` is the most aggressive shotgun on this kind of goal because it *succeeds* without leaving a trace of the proof shape.

Note that on this theorem, neither model produces a single-tactic shotgun (e.g. `intro Φ x _ _; fun_prop`); the four-`have` structure is preserved by both Goedel and Kimina, presumably because the dependency on the geometric hypothesis `hno_meet` cannot be fully delegated to `fun_prop` (the non-vanishing step needs an explicit invocation). This is consistent with the P12 pattern: as the corrigé's named moves include a domain-specific hypothesis (here `hno_meet`, on P12 the algebraic identity), shotgun closures fail and the structure is forced.

## Implications

### Pour AITP v7

1. **The four-move corrigé is preserved by all three scripts at the `have` skeleton level.** The discriminant is *what closes each `have`*, not whether the `have`s are present. This refines the bidirectionality criterion: `n_have` count is necessary but not sufficient — the *closing tactic* of each `have` carries the bidirectional information.
2. **The shotgun gradient on P9.subq_4** is `continuity` (Goedel) < `fun_prop` (Kimina): both close the linearity sub-goal without leaving the linear-combination skeleton in the script, but `fun_prop` is broader and shorter.
3. **The non-vanishing step (Move 3) resists shotgun.** All three scripts name `hno_meet` and supply the two bound hypotheses explicitly. This is because the hypothesis is *geometric*, not generic — neither `continuity` nor `fun_prop` knows that `α.im + x · (β − α).im ≠ 0` is a corollary of segment-not-meeting-ℝ.

### Pour WDWFT

The P9.subq_4 artefact provides a *second data point* for the bidirectionality measurement, complementary to P12.subq_I_B_2_a:

- On P12 (algebraic identity + non-negativity + linarith), the discriminant was the *presence* of the named identity (Myers, Goedel ✓; Kimina ✗ — absorbed into `nlinarith` hint-list).
- On P9.subq_4 (linearity + non-vanishing + quotient), all three scripts name all four moves at the `have` level, but the discriminant is the *closure* of the linearity sub-goals: explicit Mathlib chain (Myers) vs `continuity` automation (Goedel) vs `fun_prop` shotgun (Kimina).

The two cases together show that bidirectionality is *gradable*, not binary:

1. *Move-level inscription* (presence of a `have` per named corrigé move) is the coarse criterion. P12 separates Kimina from the other two; P9.subq_4 does not separate any of them.
2. *Tactic-level inscription* (whether each `have` closes by an explicitly named lemma chain or by automation) is the fine criterion. P9.subq_4 separates all three.

Phrasing pour WDWFT (post-P9.subq_4 calibration):

> *The bidirectionality of a tactic script is measured at two levels: (i) whether the named moves of the corrigé appear as named `have` blocks; (ii) whether each block is closed by an explicitly named Mathlib lemma chain (e.g., `continuous_const.add (continuous_id.mul continuous_const)`) or by a domain-specific automation tactic (`continuity`, `fun_prop`, `nlinarith`-with-hints). On P9 sub-question 4 (`Φ = (a + bx)/(c + dx)` continuous on `(0, 1)`), the Myers-faithful script preserves both levels: four named moves, each closed by a named lemma. The Goedel script preserves (i) but degrades (ii) on Moves 1–2 via `continuity`. The Kimina script preserves (i) but degrades (ii) further via `fun_prop`. All three close the kernel; only the first satisfies the fine criterion.*
