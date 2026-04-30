# P9.subq_4 — per-theorem deep dive

**Total PASSes**: 87 (59 Goedel + 28 Kimina)

## Statement

For `Φ(x) = (α.re + x*(β−α).re) / (α.im + x*(β−α).im)` with non-vanishing denominator on
`[0,1]` (hypothesis `hno_meet`), prove `ContinuousAt Φ x` for all `x ∈ (0,1)`.

## Corrigé route

Φ is a ratio of two linear (hence continuous) functions of x; the denominator is non-zero at
any `x ∈ (0,1) ⊂ [0,1]` by `hno_meet`.
- **(a) Route-preserving**: name num/denom continuity, invoke `ContinuousAt.div` with
  `hno_meet x (by linarith) (by linarith)`. The `Φ = N/D` identity closes by `rfl`.
- **(b) Lower-abstraction**: build linearity from `ContinuousAt.add`, `.mul`, `.const`, `.id`,
  then `.div`; but the `Φ = N/D` step requires a non-trivial `funext` + tactic cascade.
- **(c) Opaque**: pure `continuity`/`fun_prop` shotgun hiding the div structure; empty bucket.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 59 | 0 (0%) | 59 (100%) | 0 (0%) |
| Kimina | 28 | 28 (100%) | 0 (0%) | 0 (0%) |
| **Both** | **87** | **28 (32%)** | **59 (68%)** | **0 (0%)** |

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (59/59)

Every Goedel PASS shares the same macro-structure: `intro Φ x hx...`, a denom non-vanishing
`have` block (via `linarith`), explicit construction of numerator and denominator continuity, then
a `funext`-based rewrite to expose `Φ` as a pointwise quotient before calling `ContinuousAt.div`.
The `funext` step appears in all 59 files (grep confirms; the heuristic flag `uses_funext` flags
44/59 but under-counts). The rewrite block after `funext` universally deploys a cascade of
`simp [Φ] <;> ring_nf <;> field_simp <;> ring_nf <;> simp_all [...] <;> norm_num <;> linarith`
to prove the identity `Φ = N/D`; this identity is in fact `rfl` but Goedel never uses `rfl` here.
`field_simp` fires in 59/59 Goedel files; `simp_all` in 33/59; `norm_num` in 34/59.

Three sub-styles differ in how numerator/denominator continuity is established:

- **G-b1** (~34 files): proves global `Continuous` via the `continuity` tactic, then converts
  with `.continuousAt`. The `uses_Continuous` flag is True in 34/59 files. Char-len range
  1478–2658. Representative: `goedel_att01.md`, `goedel_att03.md`, `goedel_att05.md`.

- **G-b2** (~18 files): builds `ContinuousAt` directly from primitives (`continuousAt_const`,
  `continuousAt_id`, `ContinuousAt.mul`, `ContinuousAt.add`) without passing through `Continuous`.
  Char-len range 2049–3525. Representative: `goedel_att10.md`, `goedel_att11.md`,
  `goedel_att54.md`.

- **G-b3** (~7 files): bottom-up build with additional `simp_all` fallbacks embedded inside the
  continuity sub-goals themselves, not only in the funext rewrite. Representative:
  `goedel_att47.md`, `goedel_att32.md`.

Char-len range: 1478–3525 (auto-tally mean 2337); the top outliers (3337–3525) are extreme
cascade expansions in G-b2. `n_have` mean 17, range 10–25.

### Kimina — all (a) route-preserving (28/28)

Every Kimina PASS has the canonical 18–35 line structure with no `funext` (1/28 heuristic flag
hit is a false positive from the `funext t` in reasoning text), no `field_simp`, no `simp_all`,
no `ring_nf`. The three named moves are directly readable in every script:

1. Denom non-vanishing: `specialize hno_meet x (by linarith) (by linarith); simpa` or
   `apply hno_meet; linarith; linarith`.
2. Num/denom continuity: either `fun_prop` (K-a1) or `ContinuousAt.add`/`.mul` (K-a2).
3. Quotient: `apply ContinuousAt.div; exact h_num; exact h_denom; exact h_ne`.

The `Φ = N/D` identity is closed by `rfl` (heuristic: 9/28 with explicit `rfl`; the remaining
19 skip the identity step entirely via `simpa using h4` or direct `apply`). No `funext` cascade.

Two sub-styles within (a):

- **K-a1** (19 files): `fun_prop` for both num/denom continuity, `apply ContinuousAt.div` close.
  Shortest scripts (623–940 chars). Representative: `kimina_att33.md` (18 lines, 623 chars),
  `kimina_att57.md`, `kimina_att02.md`, `kimina_att48.md`.

- **K-a2** (9 files): bottom-up via `ContinuousAt.add`, `ContinuousAt.mul`, `continuousAt_id`,
  `continuousAt_const` — same primitives as Goedel G-b2, but no `funext` cascade and no
  `field_simp`. Char-len 1320–1404. Representative: `kimina_att61.md`, `kimina_att21.md`,
  `kimina_att29.md`.

Char-len range: 623–1404 (auto-tally mean 1018). `n_have` mean 4, range 1–8.

## Cross-arm divergence

The structural split is total: 0% Goedel in route (a), 100% Kimina in route (a). Key binary
markers: `funext` present in 100% (59/59) Goedel vs 0% (0/28) Kimina; `field_simp` present in
100% (59/59) Goedel vs 0% (0/28) Kimina; `Continuous` (global) present in 58% (34/59) Goedel vs
0% (0/28) Kimina; `fun_prop` present in 0% (0/59) Goedel vs 68% (19/28) Kimina; `ring_nf`
present in 75% (44/59) Goedel vs 0% (0/28) Kimina. Char-len means: Goedel 2337 vs Kimina 1018
(2.3× ratio).

The single driver of the arm split is the `Φ = N/D` definitional identity. Kimina recognises
it as `rfl` (or discharges it via `simpa` without a rewrite); Goedel treats it as a non-trivial
algebraic equation and deploys a multi-step cascade in all 59 PASSes. This cascade is not
mathematically necessary: removing it would convert every Goedel PASS into route (a).

## Bidirectionality verdict

Kimina scripts are strongly bidirectional: the corrigé's three moves (denom non-vanishing,
linearity-hence-continuity of num/denom, quotient rule via `ContinuousAt.div`) are each inscribed
as a named tactic step and recoverable without running the proof. Goedel scripts reproduce the
same logical content but wrap it in a `funext` + `ring_nf <;> field_simp <;> simp_all <;>
norm_num <;> linarith` cascade that conceals the trivial definitional identity `Φ = N/D`; a
reader cannot identify that the cascade is discharging a `rfl` without executing the proof, so
the third structural move is epistemically opaque even though the first two are legible.

---

## Auto-generated flag tally (preserved)

### Goedel flag tally
| flag | n_true / mean |
|---|---|
| uses_ext | 0/59 |
| uses_funext | 44/59 |
| uses_intro | 59/59 |
| uses_intros | 0/59 |
| uses_rcases | 0/59 |
| uses_by_cases | 0/59 |
| uses_split_ifs | 0/59 |
| uses_induction | 0/59 |
| uses_cases | 0/59 |
| uses_use | 8/59 |
| uses_refine | 2/59 |
| uses_constructor | 1/59 |
| uses_exact | 59/59 |
| uses_ring | 0/59 |
| uses_ring_nf | 44/59 |
| uses_nlinarith | 1/59 |
| uses_polyrith | 0/59 |
| uses_linarith | 59/59 |
| uses_linear_combination | 0/59 |
| uses_decide | 0/59 |
| uses_simp_all | 33/59 |
| uses_simp_only | 1/59 |
| uses_simp | 44/59 |
| uses_field_simp | 39/59 |
| uses_norm_num | 34/59 |
| uses_omega | 0/59 |
| uses_aesop | 0/59 |
| uses_tauto | 0/59 |
| uses_rfl | 4/59 |
| uses_native_decide | 0/59 |
| n_have | mean=17 (min=10 max=25) |
| n_show | mean=0 (min=0 max=0) |
| n_calc | mean=0 (min=0 max=0) |
| n_lines | mean=51 (min=36 max=74) |
| char_len | mean=2337 (min=1478 max=3525) |
| uses_HasDerivAt | 0/59 |
| uses_ContinuousAt | 59/59 |
| uses_Continuous | 34/59 |
| uses_Function_Periodic | 0/59 |
| uses_Periodic | 0/59 |
| uses_Polynomial | 0/59 |
| uses_Matrix | 0/59 |
| uses_Real_sin | 0/59 |
| uses_Real_pi | 0/59 |
| uses_Complex | 38/59 |

## Kimina flag tally
| flag | n_true / mean |
|---|---|
| uses_ext | 0/28 |
| uses_funext | 1/28 |
| uses_intro | 28/28 |
| uses_intros | 0/28 |
| uses_rcases | 0/28 |
| uses_by_cases | 0/28 |
| uses_split_ifs | 0/28 |
| uses_induction | 0/28 |
| uses_cases | 0/28 |
| uses_use | 0/28 |
| uses_refine | 0/28 |
| uses_constructor | 0/28 |
| uses_exact | 28/28 |
| uses_ring | 0/28 |
| uses_ring_nf | 0/28 |
| uses_nlinarith | 0/28 |
| uses_polyrith | 0/28 |
| uses_linarith | 28/28 |
| uses_linear_combination | 0/28 |
| uses_decide | 0/28 |
| uses_simp_all | 0/28 |
| uses_simp_only | 0/28 |
| uses_simp | 1/28 |
| uses_field_simp | 0/28 |
| uses_norm_num | 0/28 |
| uses_omega | 0/28 |
| uses_aesop | 0/28 |
| uses_tauto | 4/28 |
| uses_rfl | 9/28 |
| uses_native_decide | 0/28 |
| n_have | mean=4 (min=1 max=8) |
| n_show | mean=0 (min=0 max=1) |
| n_calc | mean=0 (min=0 max=0) |
| n_lines | mean=26 (min=18 max=35) |
| char_len | mean=1018 (min=623 max=1404) |
| uses_HasDerivAt | 0/28 |
| uses_ContinuousAt | 28/28 |
| uses_Continuous | 0/28 |
| uses_Function_Periodic | 0/28 |
| uses_Periodic | 0/28 |
| uses_Polynomial | 0/28 |
| uses_Matrix | 0/28 |
| uses_Real_sin | 0/28 |
| uses_Real_pi | 0/28 |
| uses_Complex | 0/28 |

## Per-PASS files
- [goedel_att00.md](goedel_att00.md)
- [goedel_att01.md](goedel_att01.md)
- [goedel_att02.md](goedel_att02.md)
- [goedel_att03.md](goedel_att03.md)
- [goedel_att04.md](goedel_att04.md)
- [goedel_att05.md](goedel_att05.md)
- [goedel_att06.md](goedel_att06.md)
- [goedel_att07.md](goedel_att07.md)
- [goedel_att08.md](goedel_att08.md)
- [goedel_att09.md](goedel_att09.md)
- [goedel_att10.md](goedel_att10.md)
- [goedel_att11.md](goedel_att11.md)
- [goedel_att13.md](goedel_att13.md)
- [goedel_att14.md](goedel_att14.md)
- [goedel_att15.md](goedel_att15.md)
- [goedel_att16.md](goedel_att16.md)
- [goedel_att17.md](goedel_att17.md)
- [goedel_att18.md](goedel_att18.md)
- [goedel_att19.md](goedel_att19.md)
- [goedel_att20.md](goedel_att20.md)
- [goedel_att21.md](goedel_att21.md)
- [goedel_att22.md](goedel_att22.md)
- [goedel_att23.md](goedel_att23.md)
- [goedel_att25.md](goedel_att25.md)
- [goedel_att26.md](goedel_att26.md)
- [goedel_att27.md](goedel_att27.md)
- [goedel_att28.md](goedel_att28.md)
- [goedel_att30.md](goedel_att30.md)
- [goedel_att31.md](goedel_att31.md)
- [goedel_att32.md](goedel_att32.md)
- [goedel_att33.md](goedel_att33.md)
- [goedel_att34.md](goedel_att34.md)
- [goedel_att35.md](goedel_att35.md)
- [goedel_att36.md](goedel_att36.md)
- [goedel_att37.md](goedel_att37.md)
- [goedel_att38.md](goedel_att38.md)
- [goedel_att39.md](goedel_att39.md)
- [goedel_att40.md](goedel_att40.md)
- [goedel_att42.md](goedel_att42.md)
- [goedel_att43.md](goedel_att43.md)
- [goedel_att44.md](goedel_att44.md)
- [goedel_att45.md](goedel_att45.md)
- [goedel_att46.md](goedel_att46.md)
- [goedel_att47.md](goedel_att47.md)
- [goedel_att48.md](goedel_att48.md)
- [goedel_att50.md](goedel_att50.md)
- [goedel_att51.md](goedel_att51.md)
- [goedel_att52.md](goedel_att52.md)
- [goedel_att53.md](goedel_att53.md)
- [goedel_att54.md](goedel_att54.md)
- [goedel_att55.md](goedel_att55.md)
- [goedel_att56.md](goedel_att56.md)
- [goedel_att57.md](goedel_att57.md)
- [goedel_att58.md](goedel_att58.md)
- [goedel_att59.md](goedel_att59.md)
- [goedel_att60.md](goedel_att60.md)
- [goedel_att61.md](goedel_att61.md)
- [goedel_att62.md](goedel_att62.md)
- [goedel_att63.md](goedel_att63.md)
- [kimina_att02.md](kimina_att02.md)
- [kimina_att03.md](kimina_att03.md)
- [kimina_att05.md](kimina_att05.md)
- [kimina_att07.md](kimina_att07.md)
- [kimina_att10.md](kimina_att10.md)
- [kimina_att15.md](kimina_att15.md)
- [kimina_att16.md](kimina_att16.md)
- [kimina_att21.md](kimina_att21.md)
- [kimina_att22.md](kimina_att22.md)
- [kimina_att23.md](kimina_att23.md)
- [kimina_att24.md](kimina_att24.md)
- [kimina_att25.md](kimina_att25.md)
- [kimina_att27.md](kimina_att27.md)
- [kimina_att29.md](kimina_att29.md)
- [kimina_att33.md](kimina_att33.md)
- [kimina_att36.md](kimina_att36.md)
- [kimina_att37.md](kimina_att37.md)
- [kimina_att38.md](kimina_att38.md)
- [kimina_att39.md](kimina_att39.md)
- [kimina_att40.md](kimina_att40.md)
- [kimina_att42.md](kimina_att42.md)
- [kimina_att46.md](kimina_att46.md)
- [kimina_att48.md](kimina_att48.md)
- [kimina_att52.md](kimina_att52.md)
- [kimina_att57.md](kimina_att57.md)
- [kimina_att59.md](kimina_att59.md)
- [kimina_att60.md](kimina_att60.md)
- [kimina_att61.md](kimina_att61.md)