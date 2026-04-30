# P3.subq_P3_I_1_a — per-theorem deep dive

**Total PASSes**: 18 (12 Goedel + 6 Kimina)
**Verdict distribution**: {'route-preserving': 18}

## Statement

Let θ ∈ [0, π/2], t := tan(θ/2). Show:
- cos θ = (1 - t²) / (1 + t²)
- sin θ = 2t / (1 + t²)
- and: if t ∈ ℚ, then both cos θ and sin θ are in ℚ.

## Corrigé route (Mercier-Rombaldi)

Use cos(2α) = 2cos²α − 1 and sin(2α) = 2 sin α cos α with α = θ/2; combine with tan(θ/2) = sin/cos. Mathlib hooks: `Real.cos_two_mul`, `Real.sin_two_mul`, `Real.tan_eq_sin_div_cos`. Rationality clause follows by closure of ℚ.

## Per-PASS table

| arm | att | hooks | shotgun | gcsa | verdict | cot | script | s |
|---|---:|---|---:|---:|---|---:|---:|---:|
| goedel | 01 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 8623 | 7452 | 131 |
| goedel | 05 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 10966 | 8747 | 157 |
| goedel | 08 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 8569 | 6612 | 120 |
| goedel | 17 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 9759 | 6105 | 128 |
| goedel | 19 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 6070 | 7406 | 114 |
| goedel | 20 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 18660 | 9823 | 241 |
| goedel | 26 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 10907 | 8657 | 167 |
| goedel | 30 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 5938 | 4320 | 84 |
| goedel | 33 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 6566 | 8233 | 122 |
| goedel | 38 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 5863 | 7171 | 116 |
| goedel | 41 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 9831 | 4776 | 122 |
| goedel | 62 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 8777 | 8432 | 144 |
| kimina | 01 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 16577 | 9631 | 350 |
| kimina | 05 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 26892 | 20903 | 669 |
| kimina | 46 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 16164 | 5484 | 600 |
| kimina | 52 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 14846 | 7965 | 573 |
| kimina | 62 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 11682 | 3966 | 408 |
| kimina | 63 | cos_tw+sin_tw+tan_eq | 0 | 0 | route-preserving | 17302 | 5045 | 520 |


## Files

Each PASS has its own markdown file with full CoT + final Lean script:
- `goedel/attempt_NN.md` — 12 files
- `kimina/attempt_NN.md` — 6 files

## Verdict summary

- **(a) strictly stronger/shorter**: 0/18
- **(b) lower-abstraction equivalent**: 0/18
- **(c) opaque-automation**: 0/18
- **route-preserving**: 18/18

100% route preservation. The corrigé hooks (`cos_two_mul`, `sin_two_mul`, `tan_eq_sin_div_cos`) are invoked in every PASS on both arms. No automation bypass is available because `nlinarith`/`polyrith` do not know trigonometry — the model is structurally forced onto the corrigé route.
