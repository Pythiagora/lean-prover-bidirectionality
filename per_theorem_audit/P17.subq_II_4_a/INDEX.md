# P17.subq_II_4_a — per-theorem deep dive

**Total PASSes**: 55 (48 Goedel + 7 Kimina) — arm asymmetry: Kimina PASS rate ~7/64 vs Goedel 48/64.

## Statement

Iterated tent map. For `f(x) = 1 − |2x − 1|` and `x ∈ [0, 1]`, show that for every `n : ℕ`
there exist `a b : ℤ` such that `f^[n] x = (a : ℝ) * x + (b : ℝ)`.

## Corrigé route summary

Induction on `n`. Base: `f^[0] x = 1·x + 0`. Step: given `f^[n] x = a·x + b` with `a b : ℤ`,
apply `f` and split on sign of `2(ax + b) − 1`: yields witnesses `(2a, 2b)` (case `≤ 0`) or
`(−2a, 2 − 2b)` (case `≥ 0`). Slope doubles in absolute value at each step (±2^n), intercept
stays integer. No Icc-preservation lemma required by the existential goal.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 48 | 0 (0%) | 48 (100%) | 0 (0%) |
| Kimina | 7 | 6 (86%) | 1 (14%) | 0 (0%) |
| **Both** | **55** | **6 (11%)** | **49 (89%)** | **0 (0%)** |

**Degeneracy check**: the statement is existential and `x`-fixed, but the integer-cast constraint
`b : ℤ` rules out the trivial witness `(0, f^[n] x)` since `f^[n] x` is generically irrational.
All 55 PASSes correctly use induction. No PASS collapses the problem at `n = 0` only.

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (48/48)

Every Goedel PASS shares the macro structure: outer `have h_main := by ...; exact h_main`
wrapper (46/48; 2 omit it but are otherwise identical), inner `have h : ∀ n, ∃ a b : ℤ, ...`
universalised over `n`, `induction n with`, `Function.iterate_succ_apply'` to unfold the
successor, `by_cases` on sign of the abs argument, `abs_of_nonneg` / `abs_of_nonpos` rewrites,
witnesses `use 2*a, 2*b` / `use -2*a, 2-2*b`, then a cascaded arithmetic close. All 48 use
`ring_nf`; 47/48 use `norm_num`; 35/48 use `simp_all`; 48/48 use `linarith`. Char-len range
2018–6182 (mean 3347), n_lines 56–151 (mean 88).

Four sub-styles:

- **G-b1** (~28 files): substitute `h : f^[n] x = a·x + b` immediately, split on
  `2((a:ℝ)·x + b) − 1 ≥ 0`, close with `simp [mul_assoc] <;> ring_nf <;> norm_cast <;>
  simp_all [Int.cast_mul, ...] <;> linarith`. See `goedel_att00.md`, `goedel_att05.md`,
  `goedel_att45.md`.

- **G-b2** (~12 files): adds a preliminary nested induction `have h_iter_in_Icc : ∀ n, f^[n] x
  ∈ Set.Icc 0 1` before the main induction; the Icc guard is not logically required but appears
  as a defensive step. More verbose (100+ lines). See `goedel_att21.md`, `goedel_att49.md`.

- **G-b3** (~6 files): splits `by_cases` directly on `f^[n] x ≥ 1 / 2` (the iterate, not the
  substituted form), then rewrites using `h_eq` after unfolding `f`. See `goedel_att04.md`,
  `goedel_att53.md`, `goedel_att58.md`.

- **G-b4** (~9 files): separates `have h_base` and `have h_inductive_step` as two named lemmas
  before combining; the step lemma takes the IH as an explicit argument rather than via tactic
  `induction`. See `goedel_att55.md`, `goedel_att16.md`.

### Kimina — (a) route-preserving (6/7)

Six Kimina PASSes use 40–65 line scripts with no outer wrapper: `have h1 : ∀ n, ... ; intro n ;
induction n with`, `Function.iterate_succ_apply'`, `rw [h_eq]` to substitute, `by_cases` on
sign, `abs_of_nonneg` / `abs_of_nonpos`, then `use` with witnesses and a single `ring_nf` (or
`ring`) close. `simp_all` absent in 5/6; `norm_num` absent in 6/6. Char-len 1635–2413 (mean
1918 excluding att51).

Two sub-styles within (a):

- **K-a1** (5 files): split on `2·((a:ℝ)·x + b) − 1 ≥ 0`, close with `ring_nf` alone or
  `simp; ring_nf`. No `simp_all`. See `kimina_att12.md` (51 lines), `kimina_att21.md` (40
  lines, shortest in cohort), `kimina_att23.md`, `kimina_att40.md`.

- **K-a2** (1 file): includes nested `have h2 : ∀ k, 0 ≤ f^[k] x ∧ f^[k] x ≤ 1` sub-proof
  (mirrors Goedel's G-b2 Icc guard), splits on `f^[n] x ≥ 1/2` (iterate form), then rewrites
  and closes with `ring_nf`. More verbose (95 lines, char_len 3373) but witnesses are still
  explicitly named and close is a single `ring_nf`. See `kimina_att51.md`.

### Kimina — (b) lower-abstraction (1/7)

- **K-b1** (`kimina_att04.md`, 65 lines, char_len 2405): correct witnesses `(-2*a, 2-2*b)` and
  `(2*a, 2*b)` but closes with `all_goals simp; all_goals ring_nf` shotgun rather than a direct
  `ring_nf`. An intermediate `linarith [eq1]` rewrites the linear form instead of `ring`. Cast
  normalisation is submerged in `all_goals simp`. Structurally isomorphic to K-a1 but closing
  tactic obscures the ring identity.

## Cross-arm divergence

Goedel (100% (b)) and Kimina (86% (a)) occupy opposite primary buckets. Both arms share the
identical proof skeleton — `induction`, `iterate_succ_apply'`, `by_cases`, `abs_of_nonneg` /
`abs_of_nonpos` — but diverge at the `use`-goal close. Goedel appends `ring_nf <;> norm_cast
<;> simp_all <;> linarith` (or longer cascades: 2–4 extra tactics in every file); Kimina closes
with `ring_nf` alone or at most `simp; ring_nf`. Char-len: Goedel mean 3347 vs Kimina mean 2201
(1.5× ratio). The defensive Icc sub-proof appears in ~25% of Goedel files (G-b2) vs 14% of
Kimina (K-a2 only). Key tactic-flag divergences: `simp_all` 35/48 Goedel vs 1/7 Kimina;
standalone `ring` 7/48 Goedel vs 3/7 Kimina; `norm_num` 47/48 Goedel vs 1/7 Kimina.

## Bidirectionality verdict

Kimina's (a) scripts are strongly bidirectional: witnesses `(2a, 2b)` and `(−2a, 2−2b)` appear
as explicit `use` arguments, and `ring_nf` closes by a single transparent ring identity that
encodes the corrigé's "slope doubles, intercept transforms by ±2." Goedel's (b) scripts carry
the same witnesses but bury the final equality in `simp_all <;> norm_cast <;> linarith` cascades
where no single step corresponds to a named mathematical operation; a reader cannot verify
witness correctness without running the tactic engine. The arm split (Goedel 100% (b), Kimina
86% (a)) on a theorem whose proof structure is uniquely determined by a two-case induction
replicates the epistemic divergence seen in P6: both arms find the correct mathematical objects
but differ sharply on whether the proof term encodes or merely verifies the corrigé reasoning.