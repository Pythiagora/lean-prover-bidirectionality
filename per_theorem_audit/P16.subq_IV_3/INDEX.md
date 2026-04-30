# P16.subq_IV_3 — per-theorem deep dive

**Total PASSes**: 42 (26 Goedel + 16 Kimina)

## Statement

For F = f − kx with k = (m+M)/2 and m ≤ (f y − f x)/(y − x) ≤ M for x ≠ y,
show |F y − F x| ≤ ((M − m)/2) |y − x|.

## Corrigé route summary

Case-split on x = y (trivial) vs x ≠ y. For x ≠ y: factor F y − F x = ((f y − f x)/(y − x) − k)·(y − x), observe |(f y − f x)/(y − x) − k| ≤ (M − m)/2 by the midpoint arithmetic m − k = −(M−m)/2, M − k = (M−m)/2, close with abs_le + linarith, then multiply by |y − x| via abs_mul and gcongr.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 26 | 23 (88%) | 3 (12%) | 0 (0%) |
| Kimina | 16 | 9 (56%) | 7 (44%) | 0 (0%) |
| **Both** | **42** | **32 (76%)** | **10 (24%)** | **0 (0%)** |

Route (a): single by_cases on x = y, factor via abs_mul + abs_le + linarith for |slope − k|, gcongr or nlinarith to conclude. Route (b): secondary by_cases on sign(y − x) to convert slope bounds to linear bounds on f y − f x before closing F y − F x bounds with nlinarith.

## Sub-styles per arm

### Goedel — (a) route-preserving (23/26)

All 26 Goedel PASSes wrap the proof body in `have h_main := by ...; exact h_main`. Within the 23 route-(a) files the inner structure is: `by_cases hxy : x = y` (x = y closes with `simp`), then the x ≠ y branch derives `F y − F x = ((f y − f x)/(y − x) − k) * (y − x)` via `field_simp + ring` or a `calc`, rewrites with `abs_mul`, and bounds the slope deviation via `abs_le; constructor <;> linarith`. Two sub-styles:

- **G-a1** (~19 files): compact close — `abs_le; constructor <;> linarith` for the slope bound, then `gcongr` or `nlinarith [abs_nonneg (y − x)]` for the product. Char-len 2299–2807. See `goedel_att22.md` (68 lines, 2351 chars), `goedel_att24.md`, `goedel_att31.md`, `goedel_att47.md`, `goedel_att48.md`.
- **G-a2** (~4 files): same backbone but the multiplication step uses a secondary `have` with `abs_mul` followed by `simp_all [abs_mul] <;> nlinarith` as a fallback arm. Char-len 2867–3240. See `goedel_att03.md` (92 lines, 3052 chars), `goedel_att06.md`, `goedel_att43.md`.

In all 26 files the midpoint (M − m)/2 appears as a named intermediate claim; none dissolve the whole proof into a bare nlinarith shotgun without it.

### Goedel — (b) lower-abstraction (3/26)

- **G-b1** (1 file): `goedel_att55.md` — four by_cases occurrences (x = y then y − x > 0). Each sign branch multiplies the slope bound through and closes F y − F x with nlinarith; |y − x| is eliminated via `abs_of_pos`/`abs_of_neg`. Does not factor through the midpoint.
- **G-b2** (2 files): `goedel_att30.md`, `goedel_att38.md` — two by_cases but use `abs_of_pos`/`abs_of_neg` on |y − x| inside the x ≠ y branch, deriving two-sided bounds on F y − F x with nlinarith per sign case. `abs_le` appears but applied to F y − F x after the sign branch, not to the slope.

### Kimina — (a) route-preserving (9/16)

Nine Kimina PASSes use a single by_cases on x = y, factor F y − F x as a product, apply `abs_le` with `constructor; linarith`/`nlinarith` to the slope, and close with `abs_mul + nlinarith`. No `have h_main` wrapper. Char-len 1887–2363. Two sub-styles:

- **K-a1** (7 files): factoring step is `have h_eq : F y − F x = ((f y − f x)/(y − x) − k) * (y − x)` via `field_simp + ring`; then `abs_mul; apply abs_le.mpr; constructor; nlinarith`. See `kimina_att33.md` (65 lines, 2320 chars), `kimina_att34.md`, `kimina_att35.md`, `kimina_att09.md` (53 lines, 1887 chars — shortest PASS in the corpus).
- **K-a2** (2 files): uses `rcases h4 with ⟨h4l, h4r⟩` destructuring plus `abs_le.mpr` with named bound before `nlinarith`. See `kimina_att23.md`, `kimina_att59.md`.

### Kimina — (b) lower-abstraction (7/16)

Seven Kimina PASSes add a sign split: `by_cases h : x = y` then `by_cases h8 : y − x > 0` (or `rcases h6 with h6 | h6` from `y − x > 0 ∨ y − x < 0`). Each branch multiplies through to m·(y−x) ≤ f y − f x ≤ M·(y−x), closes F y − F x bounds with nlinarith, uses `abs_of_pos`/`abs_of_neg` for |y − x|, and applies `abs_le.mpr` only at the F level. Char-len 3376–5574.

- **K-b1** (5 files): triple by_cases structure. See `kimina_att01.md` (141 lines, 5219 chars), `kimina_att03.md`, `kimina_att10.md`, `kimina_att22.md`, `kimina_att53.md`.
- **K-b2** (2 files): uses `rcases` + `push_neg` + `tauto` to handle the y − x = 0 contradiction arm before splitting. See `kimina_att29.md`, `kimina_att58.md`.

## Cross-arm divergence

Goedel chooses route (a) at 88% vs Kimina at 56%; Kimina's route-(b) rate is 44% vs Goedel's 12%. Char-len distributions diverge within route: Goedel (a) clusters at 2299–3240 (mean ~2700); Kimina (a) is 1887–2363 (more compact, no h_main wrapper overhead); Kimina (b) runs 3376–5574 (1.5–2.4× longer than Goedel (a)). No file in either arm uses `abs_sub_le_iff`, `polyrith`, `ring_nf`, or `simp_all` as a final closer. Goedel has `simp_all` in 13/26 files but only as a fallback arm inside a `try`-block; Kimina has 0/16. The divergence is quantitative, not categorical: both arms produce route-(a) PASSes at majority, unlike the perfectly disjoint splits seen on P6.

## Bidirectionality verdict

Route-(a) PASSes in both arms are fully bidirectional: the named tactic moves — factor as product, invoke abs_le with the two linarith-provable half-bounds derived from the midpoint, multiply by |y − x| — directly encode the corrigé's three-step argument and are recoverable by inspection. Route-(b) PASSes (10/42) are partially bidirectional: the case structure is legible but the key midpoint step |(slope − k)| ≤ (M−m)/2 is never stated as a standalone claim; it is instead implicit in two separate nlinarith calls per sign branch, making the corrigé reasoning opaque at that step.
