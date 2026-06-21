# Empirical successor — method/statement recoverability from anonymized Lean

Code + data for the empirical study behind the bidirectionality program: can the *mathematical
method* of a proof (and the *claim* of a statement) be recovered from an anonymized formal Lean
artifact, and where does that identity live?

## Layout
- `exch_experiment/`, `multiproof_experiment/` — **discrimination probe** (k-way method confusion,
  n=17 across 5 theorems with multiple distinct proofs) + falsification battery (anon/aggr/sig/locus)
  → the **two-loci** result. See their `*RESULTS*.md`.
- `leanmarathon_readback/` — **readback probe** at scale with built-in gold (n=302 + 141 across two
  independent autoformalization-blueprint corpora) + negative control + drift detector +
  `compute_stats.py` (bootstrap CIs, Wilcoxon). See `RESULTS.md`.

## Reproduce
Corpora are public clones (not vendored): `cameronfreer/exchangeability`, `seewoo5/DifferentProofs`,
`YuanheZ/{ErdosGraham,Erdos1196,Prim}`, `marcmorningstar/lean4-oseledets`. Reader + judge =
DeepSeek-V4-Pro (a second judge, on the discrimination arm, via a separate Anthropic model). API keys
via environment; no keys are committed. `uv run <script>.py`.
