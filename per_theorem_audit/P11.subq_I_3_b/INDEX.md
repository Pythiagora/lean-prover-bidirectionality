# P11.subq_I_3_b — per-theorem deep dive

**Total PASSes**: 114 (55 Goedel + 59 Kimina)

## Statement and corrigé

Show `p ≥ 0` and `p = 0 → ∀ t, u₁ t = 0 ∧ u₂ t = 0`, given
`(u₁ t)² + (q/2)(u₁ t)⁴ + (u₂ t)² = p` for all `t : ℝ` with `q > 0`.
Corrigé route: each term is non-negative (squares + q/2 > 0 times a fourth power); their sum is p,
so p ≥ 0. If p = 0, each term must individually be 0, giving u₁ t = 0 and u₂ t = 0 for all t.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 55 | 0 (0%) | 55 (100%) | 0 (0%) |
| Kimina | 59 | 0 (0%) | 59 (100%) | 0 (0%) |
| **Both** | **114** | **0 (0%)** | **114 (100%)** | **0 (0%)** |

Route (a) would require named calls to `add_eq_zero_iff` or `sq_eq_zero_iff`/`pow_eq_zero_iff`
to decompose the sum-equals-zero step; no such call appears in any Lean script across either arm.
Route (c) would require polyrith or bare `nlinarith` with no per-term scaffolding; polyrith
appears in CoT reasoning prefixes only. All 114 PASSes land in (b).

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (55/55)

Every Goedel PASS shares the same macro-structure: a `have h_nonneg : 0 ≤ p := by ...` block that
specialises `hp` at `t = 0`, establishes per-term non-negativity, and combines with `linarith`.
The `p = 0` branch then names each per-term bound with `have h : 0 ≤ term := by positivity`,
deduces `(u₁ t)^2 = 0` and `(u₂ t)^2 = 0` by bare `nlinarith`, and closes `u₁ t = 0` and
`u₂ t = 0` by two further bare `nlinarith` calls. No file names `sq_eq_zero_iff` or any
Mathlib lemma for squaring-to-zero. n_have range 19–34 (mean 26), char-len 1405–2539 (mean 1820).

Two sub-styles differ in how the `p ≥ 0` block is closed:

- **G-b1** (35 files): explicit per-term `have h : 0 ≤ (u₁ 0)^2 := by positivity`,
  `have h : 0 ≤ (q/2)*(u₁ 0)^4 := by ... nlinarith`, then `linarith` to combine with `hp 0`.
  The fourth-power term requires a nested `nlinarith [hq]`. More verbose but structurally parallel
  to the corrigé chain.
  See `goedel_att00.md` (n_have=24, 1838 chars), `goedel_att07.md`, `goedel_att16.md`.

- **G-b2** (20 files): collapses the `p ≥ 0` step to a single
  `nlinarith [sq_nonneg (u₁ 0), sq_nonneg (u₂ 0), sq_nonneg ((u₁ 0)^2), mul_nonneg ...]`
  one-liner after specialising `hp 0`. The `p = 0` branch retains explicit per-term `have`
  statements before bare `nlinarith` closers.
  See `goedel_att08.md`, `goedel_att11.md`, `goedel_att46.md`, `goedel_att14.md`.

In both sub-styles, the `u₁ t = 0` deduction from `(u₁ t)^2 = 0` is handled by bare `nlinarith`
alone, typically with two nested `have` steps. No Goedel PASS uses `pow_eq_zero_iff`.

### Kimina — all (b) lower-abstraction (59/59)

Kimina's macro-structure parallels Goedel's but is leaner: no outer wrapper, median n_have = 13
(vs 25 for Goedel), char-len 808–1769 (mean 1163). The invariant skeleton is:
`have h1 : 0 ≤ p`, `constructor`, `· exact h1`, `· intro hp0`, `intro t`, per-term nonneg chain,
`have h : (u₁ t)^2 = 0 := by nlinarith`, `have h : u₁ t = 0 := by nlinarith`.

Three sub-styles:

- **K-b1** (48 files): `p ≥ 0` closed by a one-liner
  `nlinarith [sq_nonneg (u₁ 0), sq_nonneg (u₂ 0), sq_nonneg ((u₁ 0)^2), mul_nonneg (show 0 ≤ q/2 by nlinarith) (show 0 ≤ (u₁ 0)^4 by positivity)]`.
  The `p = 0` branch uses explicit per-term positivity. Dominant Kimina pattern.
  See `kimina_att01.md`, `kimina_att04.md`, `kimina_att05.md`, `kimina_att13.md`.

- **K-b2** (11 files): `p ≥ 0` closed via explicit per-term `have h : (u₁ 0)^2 ≥ 0 := by positivity`,
  `have h : (q/2)*(u₁ 0)^4 ≥ 0 := by positivity`, then `linarith`. In a compact variant
  (`kimina_att20.md`), `positivity` fires on the entire LHS sum in one call, then `linarith`.
  See `kimina_att08.md`, `kimina_att10.md`, `kimina_att20.md`, `kimina_att28.md`.

- **K-b3** (0 files): empty. Polyrith appears in CoT for `kimina_att02.md`, `kimina_att10.md`,
  `kimina_att23.md`, `kimina_att36.md`, `kimina_att47.md` but is absent from their compiled scripts.

## Cross-arm divergence

Both arms land uniformly in route (b): the same two-conjunct structure (`p ≥ 0` via nonneg sum;
`p = 0` via per-term zero-forcing) is identical across all 114 files. The arms diverge on
shotgun density and verbosity. Kimina applies the `nlinarith [sq_nonneg...]` hint-list one-liner
for `p ≥ 0` in 81% of files (48/59); Goedel does so in only 36% (20/55). Goedel uses explicit
per-term `have` chains for `p ≥ 0` in 64% of files (35/55) vs 19% for Kimina (11/59). This
reverses the usual direction: here Kimina is the more compressed shotgun arm and Goedel the more
verbose explicit arm.

Char-len: Goedel mean 1820 vs Kimina mean 1163 (1.57× ratio). The gap traces almost entirely to
n_have: Goedel mean 26, Kimina mean 14. Both arms use `constructor · exact · intro` universally.
Neither uses `ring`, `simp`, `field_simp`, `omega`, or `calc`. The `u₁ t = 0` deduction step is
handled identically: bare `nlinarith` after establishing `(u₁ t)^2 = 0`; no arm invokes
`pow_eq_zero_iff` or `Real.sqrt`.

## Bidirectionality verdict

Neither arm encodes the corrigé's named move structure. The key mathematical step — "each of
three non-negative terms in a zero sum must individually be zero" — is subsumed in `nlinarith`
calls that verify it numerically without inscribing the `add_eq_zero_iff` reasoning. The further
step `(u₁ t)^2 = 0 → u₁ t = 0` (injectivity of squaring at zero) is similarly opaque in both
arms. A reader can recover the two-conjunct proof shape from either script but cannot reconstruct
the term-by-term zero-forcing argument without running the solver. Both arms are weakly
bidirectional at the conjunct level and opaque at the decomposition level; neither satisfies the
bidirectionality criterion. P11.I.3.b confirms the shotgun-prone prediction: the theorem is
simple enough that `nlinarith` with hints closes all goals, leaving no route for the
explicit Mathlib lemma chain the corrigé calls for.

---

## Goedel flag tally (auto-generated)
| flag | n_true / mean |
|---|---|
| uses_ext | 0/55 |
| uses_funext | 0/55 |
| uses_intro | 55/55 |
| uses_intros | 0/55 |
| uses_rcases | 4/55 |
| uses_by_cases | 0/55 |
| uses_split_ifs | 0/55 |
| uses_induction | 0/55 |
| uses_cases | 0/55 |
| uses_use | 6/55 |
| uses_refine | 1/55 |
| uses_constructor | 55/55 |
| uses_exact | 55/55 |
| uses_ring | 0/55 |
| uses_ring_nf | 0/55 |
| uses_nlinarith | 55/55 |
| uses_polyrith | 0/55 |
| uses_linarith | 52/55 |
| uses_linear_combination | 0/55 |
| uses_decide | 0/55 |
| uses_simp_all | 0/55 |
| uses_simp_only | 0/55 |
| uses_simp | 0/55 |
| uses_field_simp | 0/55 |
| uses_norm_num | 0/55 |
| uses_omega | 0/55 |
| uses_aesop | 0/55 |
| uses_tauto | 0/55 |
| uses_rfl | 0/55 |
| uses_native_decide | 0/55 |
| n_have | mean=26 (min=19 max=34) |
| n_show | mean=0 (min=0 max=0) |
| n_calc | mean=0 (min=0 max=0) |
| n_lines | mean=51 (min=40 max=65) |
| char_len | mean=1820 (min=1405 max=2539) |
| uses_HasDerivAt | 0/55 |
| uses_ContinuousAt | 0/55 |
| uses_Continuous | 0/55 |
| uses_Function_Periodic | 0/55 |
| uses_Periodic | 0/55 |
| uses_Polynomial | 0/55 |
| uses_Matrix | 0/55 |
| uses_Real_sin | 0/55 |
| uses_Real_pi | 0/55 |
| uses_Complex | 0/55 |

## Kimina flag tally
| flag | n_true / mean |
|---|---|
| uses_ext | 0/59 |
| uses_funext | 0/59 |
| uses_intro | 59/59 |
| uses_intros | 0/59 |
| uses_rcases | 0/59 |
| uses_by_cases | 0/59 |
| uses_split_ifs | 0/59 |
| uses_induction | 0/59 |
| uses_cases | 0/59 |
| uses_use | 0/59 |
| uses_refine | 0/59 |
| uses_constructor | 59/59 |
| uses_exact | 59/59 |
| uses_ring | 0/59 |
| uses_ring_nf | 0/59 |
| uses_nlinarith | 59/59 |
| uses_polyrith | 0/59 |
| uses_linarith | 56/59 |
| uses_linear_combination | 0/59 |
| uses_decide | 0/59 |
| uses_simp_all | 0/59 |
| uses_simp_only | 0/59 |
| uses_simp | 0/59 |
| uses_field_simp | 0/59 |
| uses_norm_num | 2/59 |
| uses_omega | 0/59 |
| uses_aesop | 0/59 |
| uses_tauto | 0/59 |
| uses_rfl | 0/59 |
| uses_native_decide | 0/59 |
| n_have | mean=14 (min=8 max=22) |
| n_show | mean=0 (min=0 max=0) |
| n_calc | mean=0 (min=0 max=0) |
| n_lines | mean=35 (min=27 max=45) |
| char_len | mean=1163 (min=808 max=1769) |
| uses_HasDerivAt | 0/59 |
| uses_ContinuousAt | 0/59 |
| uses_Continuous | 0/59 |
| uses_Function_Periodic | 0/59 |
| uses_Periodic | 0/59 |
| uses_Polynomial | 0/59 |
| uses_Matrix | 0/59 |
| uses_Real_sin | 0/59 |
| uses_Real_pi | 0/59 |
| uses_Complex | 0/59 |

## Per-PASS files
- [goedel_att00.md](goedel_att00.md)
- [goedel_att01.md](goedel_att01.md)
- [goedel_att02.md](goedel_att02.md)
- [goedel_att04.md](goedel_att04.md)
- [goedel_att05.md](goedel_att05.md)
- [goedel_att06.md](goedel_att06.md)
- [goedel_att07.md](goedel_att07.md)
- [goedel_att08.md](goedel_att08.md)
- [goedel_att09.md](goedel_att09.md)
- [goedel_att11.md](goedel_att11.md)
- [goedel_att13.md](goedel_att13.md)
- [goedel_att14.md](goedel_att14.md)
- [goedel_att15.md](goedel_att15.md)
- [goedel_att16.md](goedel_att16.md)
- [goedel_att17.md](goedel_att17.md)
- [goedel_att18.md](goedel_att18.md)
- [goedel_att19.md](goedel_att19.md)
- [goedel_att21.md](goedel_att21.md)
- [goedel_att22.md](goedel_att22.md)
- [goedel_att23.md](goedel_att23.md)
- [goedel_att24.md](goedel_att24.md)
- [goedel_att25.md](goedel_att25.md)
- [goedel_att26.md](goedel_att26.md)
- [goedel_att27.md](goedel_att27.md)
- [goedel_att29.md](goedel_att29.md)
- [goedel_att30.md](goedel_att30.md)
- [goedel_att31.md](goedel_att31.md)
- [goedel_att32.md](goedel_att32.md)
- [goedel_att33.md](goedel_att33.md)
- [goedel_att34.md](goedel_att34.md)
- [goedel_att36.md](goedel_att36.md)
- [goedel_att38.md](goedel_att38.md)
- [goedel_att39.md](goedel_att39.md)
- [goedel_att40.md](goedel_att40.md)
- [goedel_att41.md](goedel_att41.md)
- [goedel_att43.md](goedel_att43.md)
- [goedel_att44.md](goedel_att44.md)
- [goedel_att45.md](goedel_att45.md)
- [goedel_att46.md](goedel_att46.md)
- [goedel_att47.md](goedel_att47.md)
- [goedel_att48.md](goedel_att48.md)
- [goedel_att49.md](goedel_att49.md)
- [goedel_att50.md](goedel_att50.md)
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
- [kimina_att00.md](kimina_att00.md)
- [kimina_att01.md](kimina_att01.md)
- [kimina_att02.md](kimina_att02.md)
- [kimina_att03.md](kimina_att03.md)
- [kimina_att04.md](kimina_att04.md)
- [kimina_att05.md](kimina_att05.md)
- [kimina_att06.md](kimina_att06.md)
- [kimina_att07.md](kimina_att07.md)
- [kimina_att08.md](kimina_att08.md)
- [kimina_att09.md](kimina_att09.md)
- [kimina_att10.md](kimina_att10.md)
- [kimina_att11.md](kimina_att11.md)
- [kimina_att12.md](kimina_att12.md)
- [kimina_att13.md](kimina_att13.md)
- [kimina_att14.md](kimina_att14.md)
- [kimina_att16.md](kimina_att16.md)
- [kimina_att17.md](kimina_att17.md)
- [kimina_att19.md](kimina_att19.md)
- [kimina_att20.md](kimina_att20.md)
- [kimina_att21.md](kimina_att21.md)
- [kimina_att22.md](kimina_att22.md)
- [kimina_att23.md](kimina_att23.md)
- [kimina_att24.md](kimina_att24.md)
- [kimina_att25.md](kimina_att25.md)
- [kimina_att26.md](kimina_att26.md)
- [kimina_att28.md](kimina_att28.md)
- [kimina_att29.md](kimina_att29.md)
- [kimina_att30.md](kimina_att30.md)
- [kimina_att32.md](kimina_att32.md)
- [kimina_att33.md](kimina_att33.md)
- [kimina_att34.md](kimina_att34.md)
- [kimina_att35.md](kimina_att35.md)
- [kimina_att36.md](kimina_att36.md)
- [kimina_att37.md](kimina_att37.md)
- [kimina_att38.md](kimina_att38.md)
- [kimina_att39.md](kimina_att39.md)
- [kimina_att40.md](kimina_att40.md)
- [kimina_att41.md](kimina_att41.md)
- [kimina_att42.md](kimina_att42.md)
- [kimina_att43.md](kimina_att43.md)
- [kimina_att44.md](kimina_att44.md)
- [kimina_att45.md](kimina_att45.md)
- [kimina_att46.md](kimina_att46.md)
- [kimina_att47.md](kimina_att47.md)
- [kimina_att48.md](kimina_att48.md)
- [kimina_att49.md](kimina_att49.md)
- [kimina_att50.md](kimina_att50.md)
- [kimina_att51.md](kimina_att51.md)
- [kimina_att52.md](kimina_att52.md)
- [kimina_att53.md](kimina_att53.md)
- [kimina_att54.md](kimina_att54.md)
- [kimina_att55.md](kimina_att55.md)
- [kimina_att56.md](kimina_att56.md)
- [kimina_att57.md](kimina_att57.md)
- [kimina_att58.md](kimina_att58.md)
- [kimina_att59.md](kimina_att59.md)
- [kimina_att60.md](kimina_att60.md)
- [kimina_att61.md](kimina_att61.md)
- [kimina_att62.md](kimina_att62.md)