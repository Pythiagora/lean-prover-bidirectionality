# P7.subq_A_2_a — per-theorem deep dive

**Total PASSes**: 56 (54 Goedel + 2 Kimina)

## Statement

For `n ≥ 2`, show that the `n × n` matrix `L` with diagonal entries `1` and off-diagonal entries
`−1/(n−1)` equals `(n/(n−1)) • I − (1/(n−1)) • J`, where `I` is the identity and `J` is the
all-ones matrix. The RHS is a `Matrix.smul` decomposition: scaling `I` by `n/(n−1)` gives
`n/(n−1)` on the diagonal and `0` off it; subtracting `(1/(n−1)) • J` yields `1` on the diagonal
and `−1/(n−1)` off it.

## Corrigé routes

**(a) Abstract (smul-decomposition)**: observe that the RHS applied at `(i,j)` is
`(n/(n−1)) · I_{ij} − (1/(n−1)) · 1` and close symbolically using `Matrix.smul_apply`,
`Matrix.one_apply`, and a single field/ring step — without descending to per-cell cases first.

**(b) Lower-abstraction (ext + case split)**: `Matrix.ext` / `ext i j`, then
`by_cases h : i = j` (or `split_ifs`), then arithmetic per cell — diagonal:
`n/(n−1) − 1/(n−1) = 1`; off-diagonal: `0 − 1/(n−1) = −1/(n−1)`.

**(c) Opaque**: `decide`, pure `simp`/`rfl` chains, or any closure that hides the split.

## Classification table

| arm | total | (a) abstract smul-decomp | (b) ext + case split | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 54 | 0 (0%) | 54 (100%) | 0 (0%) |
| Kimina | 2 | 0 (0%) | 2 (100%) | 0 (0%) |
| **Both** | **56** | **0 (0%)** | **56 (100%)** | **0 (0%)** |

**The abstract (a)-route is absent in every PASS.** The v6 abstract's reported `route_rate=0.00`
for Goedel is empirically confirmed across all 54 files; Kimina's 2 PASSes also land in (b).

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (54/54)

Every Goedel PASS shares an identical macro-structure: an outer `have h_main := by ...;
exact h_main` wrapper, `ext i j` for extensionality, a prefixed `have h₁ : (n : ℝ) - 1 ≠ 0`
lemma, then `by_cases h : i = j` splitting into two symmetric tactic branches. None go directly
to a smul-level equation; the `Matrix.smul_apply` and `Matrix.one_apply` lemmas appear only
inside `simp` call lists as unfolding hints, not as the primary rewrite step. The heuristic flag
`uses_matrix_smul` firing in 52/54 files reflects inclusion in a `simp [...]` list, not a
standalone named rewrite.

Three closing-tactic sub-styles occur within the same outer scaffold:

- **G-b1** (~35 files): `simp [h, Matrix.one_apply, Matrix.smul_apply] <;> field_simp [h₁]
  <;> ring_nf <;> field_simp [h₁] <;> ring_nf` optionally chained with `norm_num <;> linarith`.
  Compact, symmetric across both cases. See `goedel_att46.md`, `goedel_att50.md`.

- **G-b2** (~12 files): same backbone extended with `norm_num at hn ⊢` and a `cases n with
  | zero => contradiction | succ n => ...` induction fallback, indicating uncertainty about
  whether `linarith` alone closes the arithmetic goal after `ring_nf`. See `goedel_att05.md`,
  `goedel_att32.md`.

- **G-b3** (1 file): `split_ifs with h` instead of `by_cases`, followed by explicit intermediate
  `have` statements computing `n/(n−1) − 1/(n−1) = 1` and `n/(n−1) · 0 − 1/(n−1) = −1/(n−1)`
  before closing with `simp_all <;> nlinarith`. See `goedel_att47.md`.

- **G-b4** (1 file): a `calc` block per case explicitly stepping through RHS unfolding
  (`Matrix.one_apply`, `Pi.smul_apply`, `Matrix.sub_apply`) before a `field_simp <;> linarith`
  close. Most verbose variant (3844 chars). See `goedel_att28.md`.

Char-len range: 934–3844 (mean 1453 per auto-generated tally). All 54 use `field_simp`, `ring`,
and `linarith`; all 54 invoke `Matrix.one_apply` and `Matrix.smul_apply` as simp arguments.

### Kimina — all (b) lower-abstraction (2/2)

Both Kimina PASSes use `funext i j` + case split + arithmetic automation, but differ internally:

- **K-b1** (`kimina_att36.md`): `funext i j` + `simp only [Matrix.smul_apply, Matrix.sub_apply,
  Matrix.one_apply, L, J]` + `split_ifs with h` + symmetric `field_simp [h_ne] <;> ring`
  close for both cases. 1111 chars; closes with `ring`, no `nlinarith`.

- **K-b2** (`kimina_att54.md`): `funext i j` + leading `have h1 : (n:ℝ) - 1 > 0` block +
  `by_cases h : i = j` + `simp [Matrix.mul_apply, Matrix.one_apply, ...] <;> field_simp
  <;> nlinarith` close. 1115 chars; closes with `nlinarith`, no `ring`.

Both Kimina scripts omit the `have h_main` wrapper that appears in 54/54 Goedel PASSes.

## Cross-arm divergence

Both arms land in route (b) — the macro structure of `ext` + diagonal case split is the same.
Differences are at the scaffold level: Goedel uses `have h_main := by ...; exact h_main`
indirection universally, which Kimina does not. Goedel closes with `field_simp <;> ring_nf <;>
linarith` cascades (sometimes extended with induction); Kimina uses cleaner single-step closers
(`ring` or `nlinarith`). Goedel's char-len range (934–3844) is much wider than Kimina's
(1111–1115), pointing to repetitive shotgun fallback growth in some seeds.

The arm asymmetry in PASS counts — 54/64 for Goedel vs 2/64 for Kimina — is a primary finding.
Since both arms that do PASS choose route (b), the asymmetry does not trace to route divergence.
Kimina's failures presumably arise from tactic errors in the arithmetic close or in handling the
`(n : ℝ) − 1 ≠ 0` side condition, not from choosing a structurally wrong proof shape.

## Specific question: does any PASS reach the abstract (a)-route?

No. Zero of 56 PASSes use the smul-decomposition as a primary proof step. Every PASS reduces
the matrix equality to per-cell arithmetic by `ext`/`funext` before invoking any smul lemma.
The heuristic `uses_matrix_smul` flag is not a reliable indicator of route (a): it fires when
`Matrix.smul_apply` appears in a `simp [...]` list used to unfold after `ext`, not when it is
the main rewrite. The v6 abstract's `route_rate=0.00` is correct.

## Bidirectionality verdict

All 56 PASSes are weakly bidirectional at the structural level: the diagonal/off-diagonal split
is visible in every script, and a reader can recover the case structure. The arithmetic close
(`field_simp <;> ring_nf <;> linarith` or `nlinarith`) is opaque — the specific cancellation
`n/(n−1) − 1/(n−1) = 1` is not inscribed as a named step but subsumed in the automation. The
scripts are not fully bidirectional in the corrigé sense: the smul-decomposition reasoning that
the RHS is structurally the sum of a diagonal and a constant matrix is never stated; it is only
verified numerically, per entry.
