# Corrigés — citation note

The bidirectionality metric in this repository is computed against informal proofs (corrigés) sourced from:

> Mercier, D.-J., and Rombaldi, J.-É. (2013). *Annales de l'agrégation interne de mathématiques 2005 à 2013 — 18 problèmes corrigés avec rappels de cours.* Publibook, Paris. ISBN 978-2-342-00940-8.

## What this directory does NOT contain

- The full text of any corrigé.
- The full Mercier-Rombaldi book.
- Any verbatim block longer than what falls under fair-use *courte citation* (Code de la Propriété Intellectuelle, Art. L.122-5).

The full corrigés are copyrighted by Mercier, Rombaldi, and Publibook. They are not redistributed here.

## What is here

- The *theorem statements* (énoncés) — these are official agrégation interne content from the French Ministère de l'Éducation nationale and are routinely reproduced for academic purposes.
- The Lean 4 formalisations of those statements (in `corpus/theorems_focal20.jsonl`).
- Per-theorem corrigé-move *patterns* in `analysis/corrige_moves.py` — these are regex signatures detecting the named structural moves the corrigé makes (e.g. `LinearIndependent`, `cos_two_mul`, `Metric.cauchySeq_iff`). The patterns describe the move at the Mathlib API level; they do not reproduce the corrigé's prose.
- Spot-quoted fragments of corrigé text in the AITP abstract and in code comments under fair-use citation, with attribution.

## How to access the full corrigés

Buy the book (Publibook print-on-demand, ISBN 978-2-342-00940-8) or consult it via an academic library.
