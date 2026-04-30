# P4.subq_P4_III_1 — per-theorem deep dive

**Total PASSes**: 8 (4 Goedel + 4 Kimina)
**Verdict distribution**: {'(b) lower-abstraction (explicit AX-XA via raw LinearMap)': 8}

## Statement (informal)

Let A ∈ M_n(ℂ). Construct a ℂ-linear map d : M_n(ℂ) → M_n(ℂ) such that
  d(X) = A·X - X·A, and d satisfies Leibniz: d(X·Y) = d(X)·Y + X·d(Y).

## Lean 4 statement

```lean4
theorem subq_P4_III_1
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ d : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ,
      (∀ X, d X = A * X - X * A) ∧
      (∀ X Y, d (X * Y) = d X * Y + X * d Y) := by
  sorry
```

## Corrigé route (Mercier-Rombaldi)

Define d := X ↦ A*X - X*A as a `LinearMap` (or use a Mathlib `Derivation`).
The defining equation is by definition; Leibniz follows by direct algebraic
expansion: A(XY) - (XY)A = (AX-XA)Y + X(AY-YA) by adding/subtracting XAY.

The corrigé identifies the map as a **derivation** in the algebra-theoretic sense (Mathlib `Derivation`); the inner derivation `ad_A` is the canonical example. The named-hook expectation is `Derivation`, `LieDerivation`, or at minimum `LinearMap.mk` to construct the linear map cleanly.

## Per-PASS table

| arm | att | named hooks | explicit A*X-X*A | anon-struct | verdict | cot | script | s |
|---|---:|---|---:|---:|---|---:|---:|---:|
| goedel | 02 | LinearMap | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 6623 | 3275 | 74 |
| goedel | 14 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 3175 | 3458 | 47 |
| goedel | 15 | Derivation | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 17623 | 2281 | 126 |
| goedel | 55 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 3381 | 1102 | 28 |
| kimina | 24 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 2886 | 895 | 91 |
| kimina | 34 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 4544 | 1006 | 107 |
| kimina | 56 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 4225 | 818 | 108 |
| kimina | 63 | (none) | 1 | 0 | (b) lower-abstraction (explicit AX-XA via raw LinearMap) | 3517 | 958 | 116 |


## Files

Each PASS has its own markdown file with full CoT + final Lean script:
- `goedel/attempt_NN.md` — 4 files
- `kimina/attempt_NN.md` — 4 files

## Verdict summary

- **(a) strictly stronger/shorter**: 0/8 (none flagged automatically; manual review needed)
- **(b) lower-abstraction equivalent**: 8/8
- **(c) opaque-automation**: 0/8
- **route-preserving** (Derivation / LieDerivation / LinearMap.mk): 0/8
