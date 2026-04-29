# Lean Prover Bidirectionality

Code, data, and verdicts for *"Bidirectionality vs. the Corrigé: An Empirical Bound on Kimina-Prover's Readability Claim, and an Abstraction-Level Mismatch Between Machine and Informal Proofs"* — extended abstract submitted to AITP 2026.

This repository contains a per-attempt corrigé-grounded **bidirectionality metric** for Lean 4 proof scripts and the empirical study that applies it to two SOTA neural theorem provers (Goedel-Prover-V2-32B, Kimina-Prover-72B) on a contamination-controlled corpus of 20 theorems from the French agrégation interne 2005–2013.

## What this measures

Pass rate measures whether the kernel accepts a Lean script. It does not measure whether the script communicates a mathematical argument. The two come apart.

A *bidirectional* tactic script is one a Lean-literate mathematician can read back into informal mathematical content: case structure, key lemmas with their mathematical roles, proof strategy as informal prose. With a paired informal source (a corrigé), bidirectionality becomes per-attempt computable:

```
score = (# named corrigé moves preserved in script) / (# total corrigé moves)
shotgun_rate = (does the closing tactic family hide the move?)
```

A "named corrigé move" is a structural step the corrigé makes (e.g. complete the square as $(y + x/2)^2$, apply the Cauchy criterion, factor block-matrix). The Lean script either preserves it as a named operation (`have h : T := proof`, `apply <named_lemma>`, an explicit identity rewrite) or absorbs it into a closing automation chain (`nlinarith [shotgun]`, `convert ... using 1 <;> field_simp <;> ring_nf`).

## Headline result

On P12.subq_I_B_2_a (corrigé: $x^2 + xy + y^2 = (y + x/2)^2 + (3/4)x^2$), 119 PASSes split as:

| Strategy | Goedel (n=56) | Kimina (n=63) |
|---|---:|---:|
| Named decomposition (`have h : ... = (y + x/2)²`) | **33 (59%)** | 3 (5%) |
| Single-square hint (`nlinarith [sq_nonneg (y + x/2)]`) | 19 (34%) | 0 |
| Shotgun (`nlinarith [≥3 sq_nonneg candidates]`) | 1 (2%) | **54 (86%)** |
| Black-box (`positivity`/`polyrith`) | 0 | 1 (2%) |
| Other | 3 (5%) | 5 (8%) |
| **Mean bidirectionality vs. corrigé** | **0.84** | **0.24** |

Same theorem, same kernel verdict (both close >87%), same mathematical content in the chain-of-thought. **Bidirectionality differs by 0.69.** Pass rate alone does not detect this.

## Repository layout

```
.
├── README.md                            ← this file
├── LICENSE                              ← MIT (code only; corrigés are not included, see corriges/)
├── corpus/
│   └── theorems_focal20.jsonl           ← 20 audited theorem statements (Lean 4)
├── lean_corpus/                         ← Lean 4 project with the 20 theorems
│   ├── lakefile.toml
│   ├── Common.lean
│   └── P{1..17}_concrete.lean
├── analysis/
│   ├── corrige_moves.py                 ← per-theorem move dictionary + regex patterns
│   ├── bidirec_aggregate.py             ← per-PASS aggregation
│   ├── p12_strategies.py                ← P12 strategy classifier
│   ├── abstraction_level_verify.py      ← per-theorem level × route preservation
│   ├── corrige_route_analysis.py        ← expansion ratio + route preservation
│   └── results/
│       ├── bidirec_scores.json          ← per-theorem-per-move counts
│       ├── bidirec_scores_aggregate.json← per-(theorem, prover) summary
│       ├── p12_strategy_distribution.json
│       ├── abstraction_level_verification.json
│       ├── corrige_route_findings.json
│       └── focal20_deepdive.json        ← per-PASS metrics + rep samples
├── verdicts/
│   ├── goedel.json                      ← 1280 lake env lean verdicts (Goedel-V2-32B)
│   └── kimina.json                      ← 1230 lake env lean verdicts (Kimina-72B)
├── completions_goedel.tar.gz            ← 1280 .json completions (CoT + script)
├── completions_kimina.tar.gz            ← 1230 .json completions
└── corriges/
    └── README.md                        ← citation note (corrigés themselves not redistributed)
```

## Reproducing

### Prerequisites

- Python 3.11+
- Lean 4 with Mathlib v4.30.0-rc2 pinned (matching the experiment)
- ~1 GB disk for completions

### Re-run the analysis from existing verdicts and completions

```bash
# 1. Decompress completions
tar -xzf completions_goedel.tar.gz -C completions/
tar -xzf completions_kimina.tar.gz -C completions/

# 2. Run the per-PASS bidirectionality scoring (regex-based)
cd analysis
uv run --script bidirec_aggregate.py

# 3. Run the P12 strategy classifier
uv run --script p12_strategies.py

# 4. Run the abstraction-level verification
uv run --script abstraction_level_verify.py

# 5. Optional: corrigé-route analysis
uv run --script corrige_route_analysis.py
```

Outputs land in `/tmp/` by default; redirect to `analysis/results/` to overwrite the included precomputed files.

### Re-verify the PASSes against Mathlib

The `verdicts/{goedel,kimina}.json` files include the candidate Lean code returned by each prover for every attempt. To independently re-verify, decompress the corresponding completions, extract the last ` ```lean4 ` block from each, prepend the standard preamble (`import Mathlib`, `import Aesop`, `open BigOperators Real Nat Topology Function MeasureTheory`), and run `lake env lean` in the `lean_corpus/` project.

## Experiment summary

| Item | Value |
|---|---|
| Provers | Goedel-Prover-V2-32B (Lin et al. 2025), Kimina-Prover-72B (Moonshot 2025) |
| Sampling | K = 64, max_tokens = 32,000 (matched to each model's published evaluation protocol) |
| Verification | `lake env lean` against Mathlib v4.30.0-rc2 |
| Corpus | 20 focal theorems from agrégation interne 2005–2013 (Mercier and Rombaldi 2013, ISBN 978-2-342-00940-8); 7 algebra, 13 analysis; balanced across saturated, sweet-spot, low-PASS, and 0/8-baseline difficulty bands |
| Contamination control | Verified absent from Numina, Lean-Workbook, miniF2F, PutnamBench, ProofNet, AOPS by source enumeration; print-only French academic publication |
| Total samples | 2,510 lake-verified attempts (1,280 Goedel + 1,230 Kimina); 805 PASS attempts (520 + 285) |
| Aggregate pass rate | Goedel 40.6%, Kimina 23.2% |
| Move detection | Regex patterns derived from the Mercier-Rombaldi corrigé text per theorem (see `analysis/corrige_moves.py`); spot-validated by manual inspection on 10 P12 PASSes |

## Citation

```bibtex
@misc{appadourai2026bidirectionality,
  title  = {Bidirectionality vs. the Corrig\'e: An Empirical Bound on
            Kimina-Prover's Readability Claim, and an Abstraction-Level
            Mismatch Between Machine and Informal Proofs},
  author = {Appadourai, David},
  year   = {2026},
  note   = {Extended abstract, AITP 2026},
  url    = {https://github.com/Pythiagora/lean-prover-bidirectionality}
}
```

## Companion theoretical paper

Appadourai, D. (in submission). *Why Do We Formalize Theorems? Informal Proof, Tactic Script, Proof Term: A Three-Level Analysis of Mathematical Proof.* Defines the bidirectionality criterion at Stratum 2 of a three-strata ontology of formalisation; the present empirical work operationalises it.

## Limitations

- **Single-corpus.** Bidirectionality scores are computed relative to the agrégation interne corrigés, which follow a specific French pedagogical style. The metric is corpus-relative; whether the abstraction-level pattern generalises to other informal proof traditions is open.
- **Single-seed.** All PASSes from one run per prover at a single temperature; tactic-search variance not measured across seeds. Strategy distributions reported as existence proofs rather than systematic claims.
- **Move-detection validation.** Regex patterns spot-checked manually on 10 P12 PASSes; no inter-annotator agreement study, no per-theorem-class validation reported.
- **Training-data correlation, not causation.** §4(b) of the abstract reports Lean-Workbook frequency patterns. This is one of three documented Goedel corpora (Numina, AOPS-Private inaccessible) and Kimina's training data is mostly undisclosed. Causal claims about training-distribution effects require the LoRA intervention proposed in §5 of the abstract, which has not been run.

## License

The code in this repository is released under the MIT License. The Lean corpus files are derivative work licensed under MIT.

The corrigés themselves are NOT included in this repository — they are copyrighted by Mercier, Rombaldi, and Publibook (ISBN 978-2-342-00940-8). See `corriges/README.md`. Any quoted excerpt elsewhere in this repository falls under fair-use *courte citation* (Code de la Propriété Intellectuelle, Art. L.122-5).
