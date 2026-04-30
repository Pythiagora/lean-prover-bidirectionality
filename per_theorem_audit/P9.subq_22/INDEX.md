# P9.subq_22 — per-theorem deep dive

**Total PASSes**: 1 (0 Goedel + 1 Kimina) — near-zero on both arms.

## Statement

Winding-number invariance under reparameterisation: given two regular simple closed C^1 curves z,
w with minimal periods l_z, l_w connected by a strictly increasing reparameterisation φ (z = w ∘ φ),
show that their total tangent-angle increments are equal:
`(α_z l_z - α_z 0) / (2π) = (α_w l_w - α_w 0) / (2π)`.

## Corrigé route (Mercier-Rombaldi)

Change of variable in the unit-tangent lift integral. Chain rule gives
`deriv z t = deriv w (φ t) * deriv φ t`; since φ is strictly increasing, `deriv φ t > 0`,
so the unit tangent of z at t equals the unit tangent of w at φ(t). The hypothesis
`hφ_mono` forces φ(t + l_z) = φ(t) + l_w (one-period shift), so integrating the lift
equation `α_z t = α_w (φ t)` over [0, l_z] and substituting gives
`α_z l_z - α_z 0 = α_w (φ l_z) - α_w (φ 0) = α_w l_w - α_w 0`.

Named moves: (a) chain rule + strict monotonicity → unit-tangent identity pointwise;
(b) period-shift identity `φ(t + l_z) = φ(t) + l_w`; (c) endpoint substitution.

## Classification

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) degenerate |
|---|---:|---:|---:|---:|
| Goedel | 0 | — | — | — |
| Kimina | 1 | 0 | 0 | 1 |
| **Both** | **1** | **0** | **0** | **1** |

## Single-PASS analysis: kimina_att25

**Verdict: degenerate — truncated non-proof.**

The lone PASS (attempt id `kimina_att25`) is a false positive in the extraction pipeline.
The Lean script is 30 lines, ends open-ended, and contains zero closing tactics:

```lean4
  have h7 : (α_z l_z - α_z 0) = (α_w l_w - α_w 0) := by
```

The proof body is absent — the file terminates after this line. Every single heuristic tactic
flag is `False` (`uses_ring`, `uses_simp`, `uses_linarith`, `uses_exact`, etc., all 0/1).
The `n_have` counter records 1, consistent with the one open `have` seen above. The reasoning
prefix is also truncated (ends mid-sentence with `Sin...`). The char_len of 1437 covers the
theorem signature and hypotheses only; there is no substantive proof content.

This is not a successful proof of any kind — structural, lower-abstraction, or opaque.
It is a generation that was cut off before the tactic block was produced, and the PASS label
is erroneous (presumably the checker found no `sorry` and the empty `by` caused a compilation
artifact rather than a hard failure, or the extraction script misidentified the file).

**Summary**: Kimina 0/64 genuine proofs; Goedel 0/64.
The real pass rate for this theorem is **0/128 across both arms**.

## Near-ceiling positioning

P9.subq_22 sits at the upper boundary of difficulty in this corpus alongside P11.III.1 (0/0).
The theorem requires chaining: (1) a pointwise argument-identity from the chain rule,
(2) a global period-shift identity for φ, and (3) endpoint evaluation of a composed lift.
No step admits a direct `ring`/`norm_num`/`linarith` close; every step requires reasoning about
`Complex.exp` injectivity modulo 2π, `Function.Periodic` composition, and `deriv` of composed
functions. Mathlib lacks a packaged lemma for this composition, so any genuine proof would need
`HasDerivAt.comp` + `Complex.exp_eq_exp_iff_exists_int` or equivalent, none of which appear here.

## Bidirectionality verdict

There is no proof to assess. The sole filed PASS is an extraction artifact with an empty tactic
body. If a genuine proof were produced, this theorem would demand the full change-of-variable
argument — the corrigé's three named moves are non-trivial Lean constructions, and any
bidirectional reading would need to recover all three from the script. At 0/128 genuine
completions, P9.subq_22 is a ceiling case: both arms fail to produce any proof-bearing script,
placing it at the same difficulty ceiling as P11.III.1.
