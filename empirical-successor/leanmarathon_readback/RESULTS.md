# LeanMarathon readback — statement-level bidirectionality (Erdős corpus)

Extends the bidirectionality / two-loci framework **one stratum up**, to autoformalization:
S_formal (Lean statement) → S_informal (the claim). Tests whether the informal claim is
recoverable from the (anonymized) Lean type — and whether LeanMarathon's blueprints are
"human-readable" by **structure** or by **naming**.

## Corpus & probe
- Source: `YuanheZ/{ErdosGraham, Erdos1196, Prim}` blueprints (LeanMarathon output). `@[blueprint]`
  nodes pair a Lean declaration with a **gold LaTeX `statement`** (and often a `proof`). 302 lemma/
  theorem nodes with statement golds (built-in gold pairing — no annotation needed).
- Probe (`lm_readback.py`): reader (DeepSeek) informalizes the Lean signature → claim; judge
  (DeepSeek, K=3) scores it 0–10 vs the gold LaTeX statement. Conditions: **named** (raw) vs
  **anon** (identifiers masked, type structure kept). Sample N=30 (stratified across repos).

## FULL RUN (n=302, both strata) — supersedes the n=30 pilot below

| readback | named | anon | Δ(named−anon) | structure-carried (Δ≤0) | name-dependent (Δ>2) |
|---|---|---|---|---|---|
| **statement** (Lean type → claim) | 8.03 | 5.97 | **+1.96** | 165/286 (58%) | 105 (37%) |
| **method** (Lean proof → method) | 9.80 | **9.04** | **+0.77** | **239/297 (80%)** | 37 (12%) |

**Cross-stratum finding (the headline):** the **method** of a proof is recovered from the *anonymized*
formal proof at near-ceiling (anon 9.04, Δ+0.77, 80% structure-carried) → at the proof stratum,
bidirectionality is **strongly structural at scale (n=302, research-level)**. The **statement** stratum is
markedly more name-dependent (anon 5.97, Δ+1.96, only 58% structure). I.e. *a proof's method lives in its
structure; a lemma's claim leans more on the concept-name.* This is the n=17 two-loci result corroborated
and scaled, plus a new cross-stratum contrast. **Honesty:** method-readback scores high in absolute terms
(the LaTeX proof gold is high-level → possible judge leniency); the robust claim is the **small Δ**
(name-invariance), and the **negative-control** (`lm_negctrl`) tests the leniency directly.

## Validity & application checks (2026-06-21)

**#1 Negative control (method-readback, anon, n=40)** — is the 9.04 real or judge leniency?
Judge the reader's method description against the CORRECT gold vs a WRONG (other node's) gold:
- correct-gold **9.44** · wrong-gold **0.16** · discrimination margin **+9.28** · **100%** correct>wrong.
→ The judge gives ~0 to wrong golds. **The method-recovery signal is real, not leniency.** (`lm_negctrl.py`)

**#2 Drift detector (statement, n=38)** — bidirectionality AS A TOOL. Inject one subtle meaningful
error into a Lean statement (flip a quantifier / inequality / constant), read it back, judge vs the
ORIGINAL gold:
- clean readback **9.17** · corrupted **0.62** · detection drop **+8.55** · **89% of drifts DETECTED** (drop ≥3).
→ The readback collapses on mis-formalized statements → it auto-flags autoformalization drift, the exact
failure LeanMarathon engineers against. A practical use of the criterion, not just a measurement. (`lm_drift.py`)
The 11% misses are the honest tail (corruptions too subtle for reader/judge).

**#3 Predictors of name-dependence (n=299, no API)** — NULL on syntax. # maskable identifiers vs Δ:
Spearman ρ=+0.077 (p=0.19, n.s.); signature length n.s. → name-dependence is **not** a function of how
many names or how long the statement is; it is **qualitative** — driven by whether a specific
semantically-loaded concept is named (von Mangoldt, Mertens). Confirms the §"Interpretation" reading.
(`lm_predictors.py`)

## #4 Cross-corpus replication — oseledets (n=60, `lm_oseledets.py`)
Same statement-readback probe on `lean4-oseledets` (ergodic theory, **independent team**, **leanblueprint**
format, 141 LaTeX↔Lean gold pairs):

| corpus | named | anon | Δ | structure (Δ≤0) | name-dep (Δ>2) |
|---|---|---|---|---|---|
| LeanMarathon (Erdős, n=302) | 8.03 | 5.97 | +1.96 | 58% | 37% |
| **oseledets (ergodic, n=60)** | **8.93** | **6.60** | **+2.33** | **59%** | **39%** |

→ **The statement-readback finding REPLICATES on an independent corpus** (different team, math area, blueprint
format). Same level, same Δ, same bimodal split. **Kills "narrow / LeanMarathon-specific corpus."**

## #5 Method-readback ablation — two-loci battery at scale (n=80, `lm_method_ablation.py`)
Conditions on the Lean PROOF given to the reader (judged vs gold LaTeX proof):

| condition | recovery | removes |
|---|---|---|
| named | 9.97 | nothing |
| anon | 9.40 | custom identifiers (types/tactics kept) |
| aggr | 7.73 | + types masked |
| **skel** | **7.21** | + lemma-argument lists `[..]` blanked (near-pure tactic sequence) |

- named→anon **−0.57**: names barely matter (method is not in the names).
- anon→aggr **−1.67** (largest drop): the **type vocabulary** (the objects manipulated) carries the most method signal.
- aggr→skel **−0.52**: *which* lemmas are invoked adds little.
- **Even skeletal (everything masked), method recovery stays 7.21/10** → well above floor.
→ **Two-loci at scale (method stratum): the method lives in STRUCTURE (control-flow + typed objects), not naming.**
Consistent with FLT (anon=10) but now graded and n=80. (Caveat: absolute level may be a bit lenient; the **drops** are the robust signal.)

## #6 Growing the discrimination corpus (search, read-only agent)
The "≥2 distinct proofs of one theorem" pattern is **structurally rare**. One solid NEW find:
**`FordUniver/thebook.lean`** (≠ FormalBook team) — infinitude of primes ×4 (Euclid/Mersenne/Furstenberg/Goldbach,
shared TFAE statement) + Mantel ×2 (AM-GM vs Cauchy-Schwarz). Lean4+Mathlib, buildable, created 2024-10.
→ ~6 new method-pairs, grows k-way discrimination n from 17 to ~23 on an independent corpus. Beyond this
(and the marginal, old `pythagoras4`), nothing new in the 2025–2026 window. **Conclusion: discrimination
scales modestly (corpus-limited); the readback family is where scale (n=302/141) lives.**

## Pilot (n=30) — original
| condition | mean recovery (0–10) | sd |
|---|---|---|
| named | **8.87** | 2.60 |
| anon | **6.68** | 3.36 |
| **Δ (named − anon)** | **+2.19** | — |

**But the mean hides a bimodal distribution** (the real finding):
- **16/30 nodes — Δ ≤ 0 (structure-carried).** Anonymization doesn't hurt; the type IS the claim
  (inequalities, limits, sums, e.g. `dyadic_tail_pseries_bound`: "∀ β>0 ∃C ... ∑ ... ≤ C/Q^β").
- **3/30 — mild (0 < Δ ≤ 2).**
- **11/30 — strong name-dependence (Δ > 2)**, with extremes (named 10 → anon **0.7**; 10 → 2.0).
  These invoke a **named domain concept** the bare type cannot express ("reciprocal von Mangoldt
  Mertens error", a constant existence over Mertens sums). Mask the name → the claim is unrecoverable.

## Interpretation
**Statement-level bidirectionality is mixed-locus, and the locus is *structural expressibility*:**
- A claim that is **structurally self-contained** (the proposition's logical/arithmetic form encodes it)
  survives anonymization → genuinely structure-carried readback.
- A claim that **names a domain concept** (von Mangoldt, Mertens, …) is an **extensional pointer**:
  the meaning lives in the name, not the type; anonymization collapses recovery.
  → directly analogous, one stratum up, to the proof-stratum case where a method = a single Mathlib
  lemma name (FLT-Binomial `add_pow_expChar`): name carries it, structure doesn't.

This is the autoformalization frontier of Bidi §7 ("a formal statement is bidirectional when the
informal claim is recoverable from it; statement-level failures produce verified proofs of the wrong
theorem") turned into a **measurement** — and a test of LeanMarathon's own "human-readable / guards
against drift" claim: the blueprint is statement-readable mostly by structure, but its readability of
**concept-named lemmas depends on naming hygiene**, which is exactly where silent drift could hide.

## Caveats (honest)
- n=30, single reader+judge family (DeepSeek), no human gold (same circularity caveat as the rest).
- **Statement-readback only.** Method-readback (anonymized Lean **proof** → gold LaTeX `proof`, ~302
  nodes have a proof field) is the natural next variant — closer to the core (method, not claim).
- Sample is stratified-by-stride, not random; the bimodality is robust to that but exact proportions
  are indicative.
- Judge scores are DeepSeek single-family; an Opus second judge + a human subset would harden it.

Data: `lm_readback.py`, `lm_readback_results.json`. Corpus clones gitignored (`MATHAI/external/{ErdosGraham,Erdos1196,Prim}`).
