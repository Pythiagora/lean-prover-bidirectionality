# P12.subq_I_B_2_a — per-theorem deep dive (showcase: bidirectionality F1)

**Total PASSes**: 119 (56 Goedel + 63 Kimina)

## Statement

Show that `x^2 + x*y + y^2 ≥ (3/4) * x^2` for all `x y : ℝ`.

## Corrigé route (Mercier-Rombaldi)

Subtract: `x^2 + xy + y^2 − (3/4)x^2 = (1/4)x^2 + xy + y^2 = (x/2 + y)^2 ≥ 0`. The proof
reduces to a single complete-the-square identity and `sq_nonneg`.

## Classification criteria

- **(a) route-preserving**: script contains an explicit `have h : ... = (x/2 + y)^2` (or any
  notation-equivalent form: `(y + x/2)^2`, `((1/2)*x + y)^2`, `(1/4)*(x + 2*y)^2`), proved by
  `ring` or `ring_nf`, followed by `apply sq_nonneg` or `nlinarith [sq_nonneg ...]` on that exact
  term. The algebraic identity is *stated* in the script and delegated to the elaborator.
- **(b) lower-abstraction**: `nlinarith [sq_nonneg (x/2 + y), ...]` or
  `nlinarith [sq_nonneg (x + 2*y), ...]` used directly with the route term as one of several hints,
  but no explicit have for the identity. The square is chosen correctly but the identity itself is
  left implicit.
- **(c) opaque**: shotgun `nlinarith` with no recognisable route hint, or `polyrith`.
  **No file in either arm falls here.**

## PASS counts and classification table

| arm | total | (a) explicit identity | (b) nlinarith + route hint | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 56 | 55 (98.2%) | 1 (1.8%) | 0 (0%) |
| Kimina | 63 | 9 (14.3%) | 54 (85.7%) | 0 (0%) |
| **Both** | **119** | **64 (53.8%)** | **55 (46.2%)** | **0 (0%)** |

## Sub-styles per arm

### Goedel — (a) route-preserving (55/56)

Universal scaffold: `have h_main : (1/4)*x^2 + x*y + y^2 ≥ 0 := by ...` followed by
`have h_final := by ...; exact h_final`. The `have h_main` wrapper appears in 54/56 files
(only goedel_att09.md and goedel_att52.md diverge structurally). No Goedel file uses `suffices`.

Three sub-styles within (a), determined by how the algebraic identity is proved:

- **G-a1** (~25 files): identity proved by clean `ring` — `have h1 : ... = (route)^2 := by ring`.
  The algebraic step is fully symbolic with zero fallback. See `goedel_att20.md` (15 lines, 672 chars),
  `goedel_att04.md`, `goedel_att06.md`.

- **G-a2** (~29 files): identity proved by `ring_nf <;> field_simp <;> ring_nf <;> linarith`
  cascade — `ring_nf` normalises but needs arithmetic fallback to close the identity step.
  The square is named correctly but the elaboration requires a shotgun tactic chain.
  See `goedel_att01.md` (23 lines, 772 chars), `goedel_att07.md`, `goedel_att16.md`.

- **G-a3** (1 file): identity proved by `nlinarith` (not `ring`). The notation `(x + 2*y)^2`
  is established as a `have` but the identity proof defers to `nlinarith` rather than
  symbolic ring reduction. See `goedel_att39.md`.

Char-len range: 398–1229 (mean 830), n_lines 12–38 (mean 23), n_have 3–11 (mean 5–6).
All 56 use `nlinarith` and `linarith`; `exact` appears in 56/56 for the final wrapper close.

### Goedel — (b) hint-only (1/56)

- **goedel_att52.md**: `have h₁ : ... = (1/4)*x^2 + ... := by ring_nf <;> nlinarith`, then
  closes with `nlinarith [sq_nonneg (x + 2*y), sq_nonneg (x/2 + y), ..., 6 more terms]`.
  The route term `(x/2 + y)` appears in the hint list but no explicit identity have is stated;
  the shotgun is applied directly after the arithmetic simplification step.

### Kimina — (a) route-preserving (9/63)

All 9 use a two-step pattern: `have h1 : ... = (route)^2 := by ring_nf` (or `ring` or `nlinarith`),
`rw [h1]`, then `apply sq_nonneg` (or `nlinarith [sq_nonneg ...]` on the same term).
No `have h_main` wrapper; no `exact` at the end; 3–13 lines (mean 4), 160–492 chars (mean 213).

Two sub-styles within Kimina (a):

- **K-a1** (7 files): `suffices` or `have h : ... ≥ 0 := by ...` pattern; identity proved by
  `ring_nf` or `ring`; nonneg closed by `apply sq_nonneg` alone (no `nlinarith`). Cleanest scripts
  in the entire corpus, 7–10 lines. See `kimina_att12.md` (`ring`, 12 lines), `kimina_att32.md`
  (`ring_nf`, 11 lines), `kimina_att52.md` (`ring_nf` + `apply sq_nonneg`, 9 lines, 160 chars —
  shortest PASS in the corpus), `kimina_att11.md`, `kimina_att35.md`, `kimina_att56.md`.

- **K-a2** (2 files): identity proved by `nlinarith` (not `ring`); nonneg closed by `apply sq_nonneg`.
  See `kimina_att30.md` (4-have chain), `kimina_att43.md` (3-have chain with `nlinarith` for
  identity step, `apply sq_nonneg` close).

- **K-a3** (1 file): `have h1 : (x/2 + y)^2 ≥ 0 := by apply sq_nonneg` as a named `have`,
  then `nlinarith` closes the goal using `h1`. The square is named but the identity equality
  is not stated; borderline (a)/(b). See `kimina_att09.md`.

### Kimina — (b) lower-abstraction (54/63)

All 54 use `nlinarith [sq_nonneg (...), ...]` with 3–12 additional `sq_nonneg` hints.
The route square is present in every case but embedded in a hint list rather than named as
an identity. Two sub-variants:

- **K-b1** (33 files): hint list includes `sq_nonneg (x/2 + y)` or `sq_nonneg (y + x/2)` directly.
  Canonical form: `nlinarith [sq_nonneg (y + x/2), sq_nonneg (x - y), sq_nonneg (x + y)]` (3 hints).
  See `kimina_att06.md` (3 lines, 3 hints), `kimina_att40.md` (1 line, 4 hints).

- **K-b2** (21 files): hint list uses `sq_nonneg (x + 2*y)` without the `(x/2+y)` form;
  `(x + 2*y)` is a scaling of the route term (`4*(x/2+y)^2 = (x+2y)^2`) and suffices for
  `nlinarith` but does not name the corrigé's exact expression.
  Canonical form: `nlinarith [sq_nonneg (x + 2*y), sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y)]`.
  See `kimina_att00.md`, `kimina_att01.md`, `kimina_att02.md` (all 1 line, 4–5 hints).

## Cross-arm divergence — verification of the v6 ~75/86% claim

**The v6 claim is inverted and partially miscounted.** The v6 abstract reported ~75% Goedel
route-preserving and ~86% Kimina route-preserving. The actual data reverses this:

| metric | Goedel | Kimina |
|---|---:|---:|
| (a) explicit complete-square | 55/56 = **98.2%** | 9/63 = **14.3%** |
| (b) hint-only (route term present but not named) | 1/56 | 54/63 |
| v6 regex replication `(y+x/2)\|(x/2+y)` | 43/56 = 76.8% | 37/63 = 58.7% |

The v6 regex (matching `(y+x/2)` or `(x/2+y)` anywhere in the file) gave 43/56 for Goedel
and 37/63 for Kimina — neither matches the claimed 75%/86%. Three errors compound:

1. **Notation gap in Goedel**: the regex missed 12 Goedel files that write the route term as
   `(1/2 : ℝ) * x + y` or `(x + 2*y)^2`; extended matching raises Goedel to 55/56 = 98.2%.

2. **Wrong arm labelled "higher"**: Goedel (98.2%) is the arm with near-universal explicit
   completion of square; Kimina (14.3% explicit) overwhelmingly uses hint-only nlinarith.
   The v6 claim that Kimina was higher is wrong.

3. **Hint ≠ explicit**: the Kimina regex hits (37/63 = 58.7%) are (b)-class files where
   `(x/2+y)` appears in an `nlinarith` hint list alongside 3–11 other `sq_nonneg` terms,
   not as an explicitly stated identity. Counting those as "route-preserving" inflates the
   Kimina figure and conflates (a) and (b).

The corrected arm comparison: Goedel 98.2% (a), Kimina 14.3% (a) / 85.7% (b).

## Bidirectionality verdict

Goedel is the bidirectionally transparent arm on this theorem, not Kimina. In 55/56 Goedel
PASSes the identity `(1/4)x^2 + xy + y^2 = (x/2 + y)^2` is inscribed as a named `have` whose
right-hand side is the exact corrigé expression; a reader can extract the mathematical move
directly from the proof term. In 54/63 Kimina PASSes the route square is present only as a hint
to `nlinarith`, which means the algebraic identity is *used* but not *stated* — the script is
not a literal encoding of the corrigé step. For the bidirectionality criterion (can the tactic
script be read back into informal mathematical content?), Goedel achieves strong bidirectionality
on P12 while Kimina achieves only weak bidirectionality; the F1 showcase claim must be corrected
to reflect this reversal.
