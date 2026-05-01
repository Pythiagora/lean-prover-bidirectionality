# Lean Prover Bidirectionality

Code, data, verdicts, per-PASS classifications, and Myers human-baseline scripts for *"Bidirectionality vs. the Corrigé: A Per-PASS, Per-Attempt, and Human-Baseline Audit of Two SOTA Lean Provers"* — extended abstract submitted to AITP 2026.

This repository contains a corrigé-grounded **bidirectionality metric** for Lean 4 proof scripts and the empirical study that applies it to two SOTA neural theorem provers (Goedel-Prover-V2-32B, Kimina-Prover-72B) on a contamination-controlled corpus of 20 theorems from the French agrégation interne 2005–2013.

## What this measures

Pass rate measures whether the kernel accepts a Lean script. It does not measure whether the script communicates a mathematical argument. The two come apart.

A *bidirectional* tactic script is one a Lean-literate mathematician can read back into informal mathematical content: case structure, named lemmas with their mathematical roles, proof strategy as informal prose. With a paired informal source (a corrigé), bidirectionality becomes per-PASS computable. Each named corrigé move appears in the script as a named operation (`have h : T := proof`, `apply <named_lemma>`, identity rewrite) or is absorbed into a closing automation chain (`nlinarith [shotgun]`, `<;> field_simp <;> ring_nf`).

Three discrimination levels emerge:

- **Level (i)** — move-level inscription (each corrigé move appears as `have`)
- **Level (ii)** — tactic-level inscription (closure by named lemma vs. `fun_prop` / `continuity` / `<;>` cascade)
- **Level (iii)** — inscription-uniqueness (one `have` per move, not duplicated across sub-goals)

Per-PASS classification: **(a)** route-preserving, **(b)** route-equivalent at lower abstraction, **(c)** opaque automation.

## Headline results

**Signed bidirectional gap, per-PASS hand-classified across all 805 verified scripts:**

| Arm | PASS | (a) | (b) | (c) | (a) per PASS |
|---|---:|---:|---:|---:|---:|
| Goedel-V2-32B | 520 | 102 | 418 | 0 | **19.6%** |
| Kimina-72B | 285 | 147 | 137 | 1 | **51.6%** |

Kimina preserves the corrigé route at 2.6× Goedel's rate, despite Goedel's 1.83× higher PASS rate.

**Paradigm signature, per-attempt:**

| Arm | total | PASS | FAIL with script | FAIL no script | truncated | empty | unclosed `<think>` |
|---|---:|---:|---:|---:|---:|---:|---:|
| Goedel | 1280 | 520 | 760 | **0** | 29 | 0 | 0 |
| Kimina | 1280 | 285 | 836 | **159** | 57 | 50 | 110 |

Goedel-RL always commits to a script. Kimina-SFT emits no usable script in 12.4% of attempts (50 empty, 110 unclosed `<think>` overrunning the 32K budget).

**Showcase theorem P12** (`x²+xy+y² ≥ (3/4)x²` via `(x/2+y)² ≥ 0`):

| Arm | PASS | (a) | (b) |
|---|---:|---:|---:|
| Goedel | 56 | 55 (98.2%) | 1 |
| Kimina | 63 | 9 (14.3%) | 54 |

The arm-quality ranking inverts on this theorem: Goedel inscribes the algebraic identity as a `have`, Kimina absorbs it into the `nlinarith` hint-list. Earlier regex-based estimates that counted `(x/2+y)` occurrences inside hint-lists as route-preserving overstated Kimina's score by ~70 percentage points.

**Two ceilings (0/128 PASSes both arms):** P11.subq_III_1 (`g` differentiable, `|g'| ≤ M` ⇒ finite limit at `q⁻`) and P9.subq_22 (winding number invariance under reparameterisation). The originally-reported single Kimina PASS on P9.subq_22 is a Lake false-positive: the proof body terminates at `:= by` with no closing tactic. The Myers baseline (see below) closes P11.subq_III_1 in one iteration via two named Mathlib lemmas — the Mathlib API is complete, the failure is premise-selection. The Myers baseline bounces P9.subq_22 with a structured diagnosis: the Lean statement does not fix `φ(0) = 0` and the period-shift invariance of the rotation index (Q21) is absent from Mathlib v4.30.0-rc2.

## Repository layout

```
.
├── README.md                            ← this file
├── LICENSE                              ← MIT (code only; corrigés not included)
├── corpus/
│   └── theorems_focal20.jsonl           ← 20 audited theorem statements (Lean 4)
├── lean_corpus/                         ← Lean 4 project with the 20 theorems
│   ├── lakefile.toml
│   ├── Common.lean
│   └── P{1..17}_concrete.lean
├── myers_baseline/                      ← Human-baseline transcriptions (NEW in v7)
│   ├── CROSS_MYERS_SYNTHESIS.md         ← cross-theorem synthesis + 3-axis gradation
│   ├── P{N}_subq_*_myers.lean           ← 20 kernel-verified Myers scripts
│   └── P{N}_subq_*_myers.md             ← 20 syntheses (corrigé mapping + ML comparison)
├── per_theorem_audit/                   ← Per-PASS hand-classified analysis (NEW in v7)
│   ├── CROSS_SYNTHESIS.md               ← per-theorem aggregate + 5 patterns
│   ├── CROSS_ATTEMPT_AGGREGATE.md       ← per-attempt failure-mode breakdown
│   └── P{N}.subq_*/INDEX.md             ← per-(theorem, arm) classification + sub-styles
├── analysis/                            ← Earlier regex-based analysis (superseded by per_theorem_audit/)
│   ├── corrige_moves.py
│   ├── bidirec_aggregate.py
│   ├── p12_strategies.py
│   ├── abstraction_level_verify.py
│   └── results/
├── verdicts/
│   ├── goedel.json                      ← 1280 lake env lean verdicts
│   └── kimina.json                      ← 1280 lake env lean verdicts
├── completions_goedel.tar.gz            ← 1280 .json completions (CoT + script)
├── completions_kimina.tar.gz            ← 1280 .json completions
└── corriges/
    └── README.md                        ← citation note (corrigés themselves not redistributed)
```

## Myers baseline

The `myers_baseline/` directory contains a Lean 4 script for each of the 20 theorems, written in the role of Myers from the WDWFT framework: faithful transcription of corrigé moves into named operations, no shotgun automation, no `<;>` cascades. Each script was drafted by Claude Opus 4.7 against an interactive Lean LSP server (`lean-lsp-mcp`), with proof-state inspection (`lean_goal`), multi-tactic probing (`lean_multi_attempt`), and Mathlib API search (`lean_leansearch`, `lean_loogle`).

Of 20 baseline scripts, 19 reach (a) classification on first or second iteration. The exception is P9.subq_22 (winding number ceiling), which is documented in `P9_subq_22_myers.md` with the structured failure diagnosis. All passing scripts are kernel-verified by `lean_diagnostic_messages` (0 errors, 0 warnings) and use only standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no `native_decide`).

The baseline serves three purposes: (i) calibration of the (a) upper bound for each theorem, (ii) per-theorem comparison anchor against the ML PASSes, (iii) diagnostic instrument for ceiling cases (where ML provers timeout, Myers either closes the proof or identifies the precise blocker).

## Per-theorem audit

The `per_theorem_audit/` directory contains an `INDEX.md` for each of the 19 theorems with at least one PASS (P11.subq_III_1 has zero PASSes and no INDEX). Each INDEX gives:

- One-line theorem description and corrigé route summary
- PASS counts per arm
- (a) / (b) / (c) classification table
- 2–4 sub-styles per non-empty bucket per arm with representative attempt IDs
- Cross-arm divergence (specific percentages)
- Bidirectionality verdict

The `CROSS_SYNTHESIS.md` aggregates across theorems, with five patterns (corrigé-bound / Kimina-clean / Goedel-clean / closure-rate-asymmetric / Kimina-ceiling) and the headline 51.6% vs 19.6% gap. `CROSS_ATTEMPT_AGGREGATE.md` extends to the 1,705 FAILs and reports the Goedel-always-emits vs Kimina-sometimes-truncates paradigm signature.

## Reproducing

### Prerequisites

- Python 3.11+
- Lean 4 with Mathlib v4.30.0-rc2 pinned (matching the experiment)
- `lake` CLI for kernel verification
- For Myers baseline interactive audit: `lean-lsp-mcp` v0.26.0 (`uvx --from lean-lsp-mcp lean-lsp-mcp --lean-project-path lean_corpus`)
- ~1 GB disk for completions

### Re-verify the Myers baseline

```bash
cd lean_corpus
# Copy a Myers script into the project and check it
cp ../myers_baseline/P12_subq_I_B_2_a_myers.lean LeanCorpus/
lake env lean LeanCorpus/P12_subq_I_B_2_a_myers.lean
# Expect: 0 errors, 0 warnings (some scripts have unused-variable warnings on signature parameters)
```

### Re-verify the PASSes against Mathlib

The `verdicts/{goedel,kimina}.json` files include the candidate Lean code returned by each prover for every attempt. To independently re-verify, decompress the corresponding completions, extract the last ` ```lean4 ` block from each, prepend the standard preamble (`import Mathlib`, `import Aesop`, `open BigOperators Real Nat Topology Function MeasureTheory`), and run `lake env lean` in the `lean_corpus/` project.

### Re-run the legacy regex analysis

The `analysis/` directory contains the original regex-based scoring used for v6 of the abstract. The v7 headline numbers are NOT derived from these scripts — they come from per-PASS hand-classification documented in `per_theorem_audit/`. The regex scripts are retained for reproducibility of the v6 numbers and for comparison.

```bash
cd analysis
uv run --script bidirec_aggregate.py
uv run --script p12_strategies.py
uv run --script abstraction_level_verify.py
```

## Experiment summary

| Item | Value |
|---|---|
| Provers | Goedel-Prover-V2-32B (Lin et al. 2025), Kimina-Prover-72B (Moonshot 2025) |
| Sampling | K = 64, max_tokens = 32,000 (matched to each model's published evaluation protocol); Goedel T=1.0, top_p=0.95; Kimina T=0.6, top_p=0.95; vLLM seed unset; per-attempt timeouts 900s inference / 90s verification |
| Verification | `lake env lean` against Mathlib v4.30.0-rc2 |
| Corpus | 20 focal theorems from agrégation interne 2005–2013; 7 algebra, 13 analysis; balanced across saturated, sweet-spot, low-PASS, and 0/8-baseline difficulty bands |
| Contamination control | Verified absent from Numina, Lean-Workbook, miniF2F, PutnamBench, ProofNet, AOPS by source enumeration; print-only French academic publication |
| Total samples | 2,560 attempts (1,280 Goedel + 1,280 Kimina); 805 PASS attempts (520 + 285) |
| Aggregate pass rate | Goedel 40.6%, Kimina 22.3% |
| Per-PASS classification | Hand-mediated through Sonnet sub-agents calibrated on representative samples; per-theorem INDEX.md cites specific attempt IDs |
| Myers baseline | Claude Opus 4.7 + interactive lean-lsp; 19/20 scripts reach (a); P9.subq_22 documented as failed with structured diagnosis |
| Lake false-positives detected | 2/805 surfaced via Myers audit (P9.subq_22 truncated PASS, P15.subq_I_2 PASS invoking lemma name absent from current Mathlib) |

## Corpus selection

The 20 focal theorems were chosen pre-experiment from 412 audited sub-questions of agrégation interne 2005–2013 by the following protocol:

1. **Audit step.** Each of the 412 sub-questions was reviewed against the Mercier-Rombaldi corrigé and tagged with: subject (algebra / analysis), difficulty (estimated lines of corrigé), self-containedness, Lean-formalisability.
2. **Pilot pass-rate stratification.** A K=8 pilot run on Goedel-V2-32B over a candidate set of ~80 self-contained Lean-formalisable sub-questions produced four difficulty bands (saturated, sweet-spot, low-PASS, 0/8-baseline); 5 theorems per band.
3. **Topic balance.** Within each band, selection enforced a 7-algebra / 13-analysis split.
4. **Output blinding.** Model outputs were not inspected during selection. The K=8 pilot produced binary PASS counts only; chain-of-thought, generated Lean scripts, and verdicts were sealed until the K=64 main run completed.
5. **Final list.** The 20 chosen theorem IDs are in `corpus/theorems_focal20.jsonl`.

The (a)/(b)/(c) classification scheme and the three discrimination levels are theorem-agnostic, defined before per-PASS inspection. The five cross-theorem patterns (`per_theorem_audit/CROSS_SYNTHESIS.md`) emerged from the per-PASS audit and are post-hoc.

## Citation

```bibtex
@misc{appadourai2026bidirectionality,
  title  = {Bidirectionality vs. the Corrig\'e: A Per-PASS, Per-Attempt,
            and Human-Baseline Audit of Two SOTA Lean Provers},
  author = {Appadourai, David},
  year   = {2026},
  note   = {Extended abstract, AITP 2026},
  url    = {https://github.com/Pythiagora/lean-prover-bidirectionality}
}
```

## Companion theoretical paper

Appadourai, D. (in submission). *Why Do We Formalize Theorems? Informal Proof, Tactic Script, Proof Term: A Three-Level Analysis of Mathematical Proof.* Defines the bidirectionality criterion at Stratum 2 of a three-strata ontology of formalisation. The present empirical work operationalises it.

## Limitations

- **Single-corpus.** Bidirectionality scores are computed relative to the agrégation interne corrigés, which follow a specific French pedagogical style. The metric is corpus-relative; whether the patterns generalise to other informal proof traditions is open.
- **Single-seed main run.** All PASSes from one run per prover at a single temperature. On a Goedel 3-theorem stratified subset (concrete, standard, abstract), two secondary vLLM seeds (12345, 67890) reproduce per-PASS route rates within ≤ 3.2 pp (P12: 75/76/73%, P11.I.3.b: 0/0/0%, P7: 0/0/0%). Kernel-PASS rates vary by 9–14 pp. The bidirectional ratio is seed-stable on this subset. Full multi-seed coverage and Kimina re-seeding deferred.
- **Per-PASS classification is sub-agent-mediated, but inter-rater agreement is high across model lineages.** The (a)/(b)/(c) call for each PASS was made by a Sonnet sub-agent calibrated on representative samples. A 3-rater protocol (Sonnet original, Gemini 3.1 Pro, GPT-5.5) on the 78 INDEX-enumerated PASSes achieves Fleiss' κ = 0.87 across 52 valid triples. Pairwise: Sonnet–Gemini κ = 0.81, Sonnet–GPT-5.5 κ = 0.81, Gemini–GPT-5.5 κ = 1.00. Excluding P16.subq_IV_3 (slope/multiplicative bound, n=37), all three raters agree on every PASS — the framework is unanimous across model lineages on every theorem except one with a genuinely fuzzy (a)/(b) boundary. Pipeline and raw verdicts: `analysis/kappa_3raters.{py,json}`.
- **Myers baseline is Claude-mediated, not pure-human.** The baseline scripts were written by Claude Opus 4.7 with interactive lean-lsp access and an explicit Myers-role prompt (faithful transcription, no shortcut). Comparison to genuinely human-written Mathlib tactic scripts (Myers-style by hand) remains future work.
- **Lake false-positive lower bound.** The Myers audit surfaced two PASSes the batch verifier accepted but that fail under interactive lean-lsp checking. The rerun4 false-positive rate is bounded below by 2/805. Audit of the remaining cleanest PASSes is in progress.
- **No causal training-distribution claim.** Earlier versions of this work explored a Lean-Workbook frequency analysis as evidence for a training-data signal. The per-PASS audit makes the empirical case independently of training-distribution counts; the Lean-Workbook scripts in `analysis/` are retained for reference but no longer load-bearing.

## License

The code in this repository is released under the MIT License. The Lean corpus files and Myers baseline scripts are derivative work licensed under MIT.

The corrigés themselves are NOT included in this repository — they are copyrighted by Mercier, Rombaldi, and Publibook (ISBN 978-2-342-00940-8). See `corriges/README.md`. Any quoted excerpt elsewhere in this repository falls under fair-use *courte citation* (Code de la Propriété Intellectuelle, Art. L.122-5).
