# P8.subq_A_1_a — per-theorem deep dive

**Total PASSes**: 14 (12 Goedel + 2 Kimina)

## Statement and corrigé

For `M : Matrix.GeneralLinearGroup (Fin n) ℤ`, show `det M = 1 ∨ det M = -1`.
The corrigé route: `M` invertible over ℤ implies `det M · det M⁻¹ = 1` in ℤ, so `det M` is a unit in ℤ, and the only units in ℤ are ±1.

- **(a) Route-preserving**: invoke `IsUnit (det M)` from the GL membership directly — via `Matrix.isUnit_iff_isUnit_det` applied to `M.isUnit`/`M.property` or via `Units.isUnit M` — then close with `Int.isUnit_iff` + `tauto`.
- **(b) Lower-abstraction**: either explicitly compute `det M · det M⁻¹ = 1` via `Matrix.det_mul` and convert divisibility through a `natAbs` chain, or reach `IsUnit (det M)` but close by bound-squeezing (`IsUnit.dvd_one` + `Int.le_of_dvd` + `interval_cases`) rather than the direct `Int.isUnit_iff` application.
- **(c) Opaque**: pure `decide`/`simp_all`/mass shotgun with no named corrigé steps.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 12 | 5 (42%) | 7 (58%) | 0 (0%) |
| Kimina | 2 | 0 (0%) | 2 (100%) | 0 (0%) |
| **Both** | **14** | **5 (36%)** | **9 (64%)** | **0 (0%)** |

## Sub-styles per arm

### Goedel — (a) route-preserving (5/12)

Every (a)-route Goedel script reaches `IsUnit (det M)` in 2–3 named steps and closes with `Int.isUnit_iff` + `tauto`. Three entry points appear:

- **G-a1** (2 files): `M.isUnit` → `Matrix.isUnit_iff_isUnit_det _ |>.mp` → `Int.isUnit_iff` → `tauto`. Each lemma name corresponds to a named corrigé step. See `goedel_att26.md` (835 chars, 5 `have`s) and `goedel_att42.md` (1268 chars).
- **G-a2** (2 files): `simpa [Matrix.det_fin_zero] using M.property` to discharge `IsUnit (det M)` in one step, then `Int.isUnit_iff` + `tauto`. The `simpa` hides the isUnit-of-units coercion. See `goedel_att15.md` (1147 chars) and `goedel_att46.md` (1107 chars).
- **G-a3** (1 file): `Units.isUnit M` + `Matrix.isUnit_iff_isUnit_det` + `Int.isUnit_iff` + `tauto`, wrapped in outer `have` scaffold and closed with trailing `aesop`. See `goedel_att60.md` (1393 chars).

All five G-a scripts are compact (835–1393 chars, 5–8 `have`s) relative to the G-b scripts.

### Goedel — (b) lower-abstraction (7/12)

Every G-b script explicitly proves `det M · det M⁻¹ = 1` via `Matrix.det_mul` and then converts divisibility to `natAbs = 1` to recover `det M = ±1`. The macro-structure is: (i) establish `M * M⁻¹ = 1`; (ii) calc `det M * det M⁻¹ = (M * M⁻¹).det` by `det_mul`, `= 1` by `det_one`; (iii) divisibility chain via `natAbs_dvd_natAbs` + `Nat.dvd_one`; (iv) `Int.natAbs_eq_iff` + `tauto`.

Two sub-styles:

- **G-b1** (4 files): `M * M⁻¹ = 1` discharged via `simpa using M.mul_inv` or `simpa using M.inv_mul`, using the `GeneralLinearGroup` field accessor cleanly. See `goedel_att08.md` (1602 chars) and `goedel_att18.md` (2203 chars).
- **G-b2** (3 files): `M * M⁻¹ = 1` discharged via a shotgun (`simp [mul_eq_one_comm] <;> simp_all <;> aesop`), reflecting uncertainty about the coercion API. Scripts are 2892–4413 chars with 15–27 `have`s. See `goedel_att38.md` (4413 chars, 27 `have`s), `goedel_att45.md` (3224 chars), `goedel_att50.md` (2892 chars).

The `natAbs` detour is absent from all (a)-route scripts, which bypass it entirely via `Int.isUnit_iff`.

### Goedel — (c) opaque

Empty. No Goedel PASS uses a pure-automation close.

### Kimina — (b) lower-abstraction (2/2)

Both Kimina scripts reach `IsUnit (det M)` compactly but close by bound-squeezing rather than `Int.isUnit_iff`:

- **K-b1** (`kimina_att38.md`, 1163 chars): `Matrix.isUnit_det` + `M.2` → `IsUnit (det M)` → `rcases` for dvd → `Int.le_of_dvd` for upper bound → `Int.neg_dvd` + `Int.le_of_dvd` for lower bound → `interval_cases` + `tauto`.
- **K-b2** (`kimina_att59.md`, 947 chars): `M.2` directly → `IsUnit.dvd_one` → `Int.le_of_dvd` (upper + negated lower bound) → `interval_cases` + `tauto`. Most compact PASS in the set.

Neither Kimina PASS uses `Int.isUnit_iff`. Both reach the unit property at the correct abstraction level but then descend into explicit bound arithmetic to extract the two-case disjunction.

### Kimina — (a) and (c)

Both empty.

## Cross-arm divergence

The arms agree structurally in one respect: zero (c)-opaque proofs appear in either arm, reflecting that both models exploit the GL-membership-to-unit inference rather than firing blind automation. The divergence is in (a) vs (b). Goedel produces (a)-route scripts at 42% vs 0% for Kimina. The Goedel (a)-scripts use `Int.isUnit_iff` to close the unit-to-disjunction step in a single rewrite; both Kimina PASSes bypass this lemma and instead derive the ±1 range via `Int.le_of_dvd` + `interval_cases`, an operationally equivalent but more verbose route (bound computation rather than direct unit characterization). Char-length: Kimina 947–1163 chars vs Goedel 835–4413 chars; the Goedel (b2) tail (shotgun `aesop`/`simp_all` for `M * M⁻¹ = 1`) drives the Goedel maximum. A second divergence: Goedel (b) scripts descend further by proving `det M · det M⁻¹ = 1` explicitly via `det_mul` (7/12 files), a step Kimina skips by accessing `IsUnit (det M)` directly through `M.2`.

## Bidirectionality verdict

The five Goedel (a)-route scripts are the most bidirectional: `M.isUnit → isUnit_iff_isUnit_det → Int.isUnit_iff → tauto` encodes the corrigé argument step-for-step, and a reader can reconstruct "det M is a unit in ℤ, hence ±1" without running the proof. The Goedel (b) and Kimina scripts are partially bidirectional — the GL-to-unit inference is present but the unit-to-disjunction step is discharged by arithmetic automation (`natAbs` chain or `interval_cases`) that obscures the direct identification of ℤ-units as a named mathematical fact; a reader sees that the bound is squeezed to ±1 but not that this follows from a characterisation of ℤ-units.
