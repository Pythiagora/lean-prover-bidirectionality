# P17.subq_II_2 — per-theorem deep dive

**Total PASSes**: 58 (35 Goedel + 23 Kimina)

## Statement

Tent map rationality iff: for `f(x) = 1 − |2x − 1|` on `[0, 1]`, show
`(∃ q : ℚ, x = q) ↔ (∃ q : ℚ, f x = q)`.

## Corrigé route

On [0, 1/2], `f(x) = 2x`; on [1/2, 1], `f(x) = 2 − 2x`. Both are linear with rational
coefficients. Forward: `x ∈ ℚ ⇒ f(x) = 2x` or `2 − 2x ∈ ℚ`. Backward: `f(x) = r ∈ ℚ ⇒ x = r/2`
or `(2 − r)/2 ∈ ℚ`. Named moves: (1) case-split on `x ≤ 1/2` / `x ≥ 1/2`, (2) rewrite
`|2x − 1|` via `abs_of_nonpos` / `abs_of_nonneg`, (3) close each direction by linear arithmetic.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 35 | 0 (0%) | 35 (100%) | 0 (0%) |
| Kimina | 23 | 23 (100%) | 0 (0%) | 0 (0%) |
| **Both** | **58** | **23 (40%)** | **35 (60%)** | **0 (0%)** |

Both arms use an explicit case-split; divergence lies in scaffold depth, closing-tactic
verbosity, and the presence of the `have h_main` indirection.

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (35/35)

Every Goedel PASS wraps the body in a `have h_main := by ...; exact h_main` scaffold (33/35
files), `by_cases h : x ≤ 1 / 2` to split, then applies `abs_of_nonneg` and `abs_of_nonpos`
to rewrite `|2x − 1|` in each branch. Both iff directions are handled inside the wrapper.
The closing chain is invariably a multi-tactic shotgun: `ring_nf <;> simp_all [...] <;>
field_simp <;> norm_num <;> linarith`, with all five tactics firing in 31/35 files. Char-len
range: 2775–7746 (mean 4507). Script lines: 74–241 (mean 133).

Three sub-styles:

- **G-b1** (33 files): `abs_of_nonneg` + `abs_of_nonpos` for both branches, `have h_main`
  wrapper. Canonical form. See `goedel_att01.md` (118 lines), `goedel_att34.md` (115 lines),
  `goedel_att19.md` (106 lines), `goedel_att40.md` (102 lines).

- **G-b2** (1 file): `abs_of_nonneg` + `abs_of_neg` variant (strict instead of non-strict sign
  condition in one branch). See `goedel_att12.md`.

- **G-b3** (1 file): backward direction handled via `eq_or_eq_neg_of_abs_eq`, decomposing
  `|2x − 1| = r` into a disjunction, avoiding `abs_of_nonneg`/`abs_of_nonpos` entirely.
  Longest script at 144 lines (5119 chars). See `goedel_att30.md`.

In all three sub-styles the `have h_main` wrapper, `by_cases` on `x ≤ 1/2`, and the arithmetic
shotgun close are structurally identical. No Goedel PASS uses `abs_cases` or `abs_eq` as the
primary backward-direction lemma.

### Kimina — all (a) route-preserving (23/23)

Kimina scripts perform the same logical case-split but without the `h_main` wrapper (0/23 files)
and with cleaner arithmetic closes. Scripts run 41–104 lines (mean 73) and 1397–3549 chars
(mean 2411). The piecewise formulas `f x = 2 * x` and `f x = 2 - 2 * x` are stated as named
`have` steps; backward witnesses `x = q / 2` or `x = 1 - q / 2` are given as explicit rational
terms. No 4–5-tactic shotgun: `simp_all` appears in only 2/23 files and `field_simp` in 1/23.

Four sub-styles:

- **K-a1** (15 files): `by_cases h : x ≤ 1 / 2` + `abs_of_nonneg`/`abs_of_nonpos` (or
  `abs_of_nonneg`/`abs_of_neg` for strict split). Backward via `use (q / 2)` or
  `use (1 - q / 2)`, closed by `linarith` or `norm_num`. See `kimina_att15.md` (78 lines),
  `kimina_att16.md` (66 lines), `kimina_att48.md` (65 lines), `kimina_att33.md` (80 lines).

- **K-a2** (3 files): `by_cases` + `abs_of_*` for forward direction; backward direction
  additionally invokes `abs_eq` to decompose `|2x − 1| = r` into disjunction before solving for
  `x`. Mixed strategy, slightly longer. See `kimina_att30.md` (94 lines), `kimina_att52.md`
  (67 lines), `kimina_att63.md` (63 lines).

- **K-b** (2 files): `abs_cases` (Lean 4 case-splitter on sign of `2x − 1`) as the primary
  absolute-value eliminator in the backward direction; no `abs_of_*` rewrites. Shortest Kimina
  scripts. See `kimina_att00.md` (53 lines, 1648 chars), `kimina_att08.md` (73 lines).

- **K-c** (3 files): backward direction uses `abs_eq` alone (decomposes `|2x − 1| = 1 − r` into
  `2x − 1 = 1 − r ∨ 2x − 1 = r − 1`), without naming sign conditions via `abs_of_*`. Forward
  direction still uses a `by_cases` split. See `kimina_att18.md` (91 lines), `kimina_att21.md`
  (61 lines), `kimina_att28.md` (55 lines).

## Cross-arm divergence

The arms share the same proof skeleton (case-split on sign of `2x − 1`, two linear computations,
two backward witness constructions) but diverge sharply in execution:

- **Scaffold**: `have h_main` wrapper in 33/35 Goedel (94%) vs 0/23 Kimina (0%).
- **Closing tactics**: Goedel uses a 4–5-tactic shotgun cascade in 31/35 files (89%). Kimina
  uses `linarith` or `norm_num` alone in 21/23 files (91%); `simp_all` fires in 31/35 Goedel
  (89%) vs 2/23 Kimina (9%); `field_simp` in 33/35 Goedel (94%) vs 1/23 Kimina (4%).
- **Script length**: Goedel mean 133 lines / 4507 chars vs Kimina mean 73 lines / 2411 chars —
  Goedel scripts average 1.8× longer, and up to 5.5× longer at the extreme
  (goedel_att56: 241 lines vs kimina_att00: 53 lines).
- **by_cases rate**: 27/35 Goedel (77%) vs 18/23 Kimina (78%) — nearly identical, confirming
  the case-split structure is shared; verbosity divergence is entirely in the closing steps.
- **Abs lemma diversity**: Goedel is uniform — `abs_of_nonneg`+`abs_of_nonpos` in 33/35 (94%).
  Kimina splits across four sub-styles; only 15/23 (65%) use the same combination.

## Bidirectionality verdict

Both arms use an explicit case-split that directly mirrors the corrigé's identification of
`f(x) = 2x` vs `f(x) = 2 − 2x`, so the structural content (two linear regimes, witness formulas
`x = r/2` and `x = (2 − r)/2`) is recoverable from every PASS. Kimina scripts are fully
bidirectional: piecewise formulas are stated as named steps and witnesses are explicit rational
terms, with no automation hiding the calculation. Goedel scripts are structurally bidirectional
but epistemically opaque in the arithmetic close: the cascaded shotgun does not inscribe the
specific inversions `x = r/2` or `x = (2 − r)/2` as legible steps, so a reader cannot
reconstruct the corrigé's backward reasoning from the script alone without executing it — a
clean instance of shared route structure with divergent epistemic transparency.

---

## Goedel flag tally
| flag | n_true / mean |
|---|---|
| uses_ext | 0/35 |
| uses_funext | 0/35 |
| uses_intro | 35/35 |
| uses_intros | 0/35 |
| uses_rcases | 34/35 |
| uses_by_cases | 27/35 |
| uses_split_ifs | 1/35 |
| uses_induction | 0/35 |
| uses_cases | 32/35 |
| uses_use | 5/35 |
| uses_refine | 32/35 |
| uses_constructor | 35/35 |
| uses_exact | 35/35 |
| uses_ring | 2/35 |
| uses_ring_nf | 35/35 |
| uses_nlinarith | 8/35 |
| uses_polyrith | 0/35 |
| uses_linarith | 35/35 |
| uses_linear_combination | 0/35 |
| uses_decide | 0/35 |
| uses_simp_all | 31/35 |
| uses_simp_only | 0/35 |
| uses_simp | 26/35 |
| uses_field_simp | 33/35 |
| uses_norm_num | 31/35 |
| uses_omega | 0/35 |
| uses_aesop | 0/35 |
| uses_tauto | 0/35 |
| uses_rfl | 14/35 |
| uses_native_decide | 0/35 |
| n_have | mean=31 (min=19 max=50) |
| n_show | mean=0 (min=0 max=0) |
| n_calc | mean=0 (min=0 max=3) |
| n_lines | mean=133 (min=74 max=241) |
| char_len | mean=4507 (min=2775 max=7746) |
| uses_HasDerivAt | 0/35 |
| uses_ContinuousAt | 0/35 |
| uses_Continuous | 0/35 |
| uses_Function_Periodic | 0/35 |
| uses_Periodic | 0/35 |
| uses_Polynomial | 0/35 |
| uses_Matrix | 0/35 |
| uses_Real_sin | 0/35 |
| uses_Real_pi | 0/35 |
| uses_Complex | 0/35 |

## Kimina flag tally
| flag | n_true / mean |
|---|---|
| uses_ext | 0/23 |
| uses_funext | 0/23 |
| uses_intro | 9/23 |
| uses_intros | 0/23 |
| uses_rcases | 19/23 |
| uses_by_cases | 18/23 |
| uses_split_ifs | 0/23 |
| uses_induction | 0/23 |
| uses_cases | 21/23 |
| uses_use | 8/23 |
| uses_refine | 20/23 |
| uses_constructor | 23/23 |
| uses_exact | 19/23 |
| uses_ring | 4/23 |
| uses_ring_nf | 7/23 |
| uses_nlinarith | 12/23 |
| uses_polyrith | 0/23 |
| uses_linarith | 23/23 |
| uses_linear_combination | 0/23 |
| uses_decide | 0/23 |
| uses_simp_all | 2/23 |
| uses_simp_only | 0/23 |
| uses_simp | 11/23 |
| uses_field_simp | 1/23 |
| uses_norm_num | 18/23 |
| uses_omega | 0/23 |
| uses_aesop | 0/23 |
| uses_tauto | 4/23 |
| uses_rfl | 1/23 |
| uses_native_decide | 0/23 |
| n_have | mean=22 (min=9 max=36) |
| n_show | mean=0 (min=0 max=0) |
| n_calc | mean=0 (min=0 max=0) |
| n_lines | mean=73 (min=41 max=104) |
| char_len | mean=2411 (min=1397 max=3549) |
| uses_HasDerivAt | 0/23 |
| uses_ContinuousAt | 0/23 |
| uses_Continuous | 0/23 |
| uses_Function_Periodic | 0/23 |
| uses_Periodic | 0/23 |
| uses_Polynomial | 0/23 |
| uses_Matrix | 0/23 |
| uses_Real_sin | 0/23 |
| uses_Real_pi | 0/23 |
| uses_Complex | 0/23 |

## Per-PASS files
- [goedel_att01.md](goedel_att01.md)
- [goedel_att02.md](goedel_att02.md)
- [goedel_att10.md](goedel_att10.md)
- [goedel_att11.md](goedel_att11.md)
- [goedel_att12.md](goedel_att12.md)
- [goedel_att13.md](goedel_att13.md)
- [goedel_att14.md](goedel_att14.md)
- [goedel_att15.md](goedel_att15.md)
- [goedel_att16.md](goedel_att16.md)
- [goedel_att17.md](goedel_att17.md)
- [goedel_att18.md](goedel_att18.md)
- [goedel_att19.md](goedel_att19.md)
- [goedel_att20.md](goedel_att20.md)
- [goedel_att21.md](goedel_att21.md)
- [goedel_att23.md](goedel_att23.md)
- [goedel_att24.md](goedel_att24.md)
- [goedel_att25.md](goedel_att25.md)
- [goedel_att26.md](goedel_att26.md)
- [goedel_att28.md](goedel_att28.md)
- [goedel_att30.md](goedel_att30.md)
- [goedel_att34.md](goedel_att34.md)
- [goedel_att35.md](goedel_att35.md)
- [goedel_att37.md](goedel_att37.md)
- [goedel_att38.md](goedel_att38.md)
- [goedel_att40.md](goedel_att40.md)
- [goedel_att41.md](goedel_att41.md)
- [goedel_att42.md](goedel_att42.md)
- [goedel_att43.md](goedel_att43.md)
- [goedel_att46.md](goedel_att46.md)
- [goedel_att48.md](goedel_att48.md)
- [goedel_att52.md](goedel_att52.md)
- [goedel_att53.md](goedel_att53.md)
- [goedel_att56.md](goedel_att56.md)
- [goedel_att60.md](goedel_att60.md)
- [goedel_att63.md](goedel_att63.md)
- [kimina_att00.md](kimina_att00.md)
- [kimina_att03.md](kimina_att03.md)
- [kimina_att08.md](kimina_att08.md)
- [kimina_att15.md](kimina_att15.md)
- [kimina_att16.md](kimina_att16.md)
- [kimina_att18.md](kimina_att18.md)
- [kimina_att19.md](kimina_att19.md)
- [kimina_att21.md](kimina_att21.md)
- [kimina_att26.md](kimina_att26.md)
- [kimina_att27.md](kimina_att27.md)
- [kimina_att28.md](kimina_att28.md)
- [kimina_att30.md](kimina_att30.md)
- [kimina_att31.md](kimina_att31.md)
- [kimina_att33.md](kimina_att33.md)
- [kimina_att35.md](kimina_att35.md)
- [kimina_att38.md](kimina_att38.md)
- [kimina_att43.md](kimina_att43.md)
- [kimina_att45.md](kimina_att45.md)
- [kimina_att48.md](kimina_att48.md)
- [kimina_att51.md](kimina_att51.md)
- [kimina_att52.md](kimina_att52.md)
- [kimina_att62.md](kimina_att62.md)
- [kimina_att63.md](kimina_att63.md)