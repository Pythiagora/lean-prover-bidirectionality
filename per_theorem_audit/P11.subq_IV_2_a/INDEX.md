# P11.subq_IV_2_a — per-theorem deep dive

**Total PASSes**: 40 (35 Goedel + 5 Kimina) — strong arm asymmetry in absolute count; both arms converge on the same route.

## Statement

Show that `v(s) = u(s + T)` again solves the T-periodic ODE: `HasDerivAt (fun s => u (s + T)) (f τ (u (τ + T))) τ` for all `τ`, given `∀ t, HasDerivAt u (f t (u t)) t` and `f_periodic : f (t + T) x = f t x`.

## Corrigé route

Three named moves: (1) chain rule — `v'(τ) = u'(τ + T) · 1` via `HasDerivAt.comp` applied to `u` and `s ↦ s + T`; (2) evaluate `hu` at `τ + T` to get `u'(τ + T) = f(τ + T, u(τ + T))`; (3) apply `f_periodic τ` to convert `f(τ + T, -)` to `f(τ, -)`.

- **(a) Route-preserving**: single `HasDerivAt.comp`-chained pipeline with `f_periodic` rewrite inline — no intermediate `have` for the periodicity substitution.
- **(b) Lower-abstraction**: explicit `have` blocks staging each move; `f_periodic` equality extracted separately and substituted via `rw` or `convert`.
- **(c) Opaque**: pure `simp [f_periodic, hu]` or differentiability shotgun.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 35 | 0 (0%) | 35 (100%) | 0 (0%) |
| Kimina | 5 | 0 (0%) | 5 (100%) | 0 (0%) |
| **Both** | **40** | **0 (0%)** | **40 (100%)** | **0 (0%)** |

**The (a)-route is absent in every PASS.** No attempt closes the goal as a single composition pipeline that mirrors the corrigé directly.

## Sub-styles per arm

### Goedel — all (b) lower-abstraction (35/35)

Every Goedel PASS uses a fixed four-block `have` scaffold: h1 (shift derivative), h2 (evaluate `hu` at `τ + T`), h3 (compose and clear `* 1`), h4 (extract periodicity equality), h5 (substitute and close). Mean 14 `have` steps per proof (min 9, max 21), mean char_len 1737. Shift derivative is universally `simpa using (hasDerivAt_id τ).add_const T`. The chain rule fires in explicit term-mode: `HasDerivAt.comp τ h h` or `h.comp τ h`.

Three sub-styles diverge in closing tactics for the `* 1` artifact and the periodicity substitution:

- **G-b1** (~28 files): `convert h_comp using 1 <;> ring` clears `* 1`; `f_periodic τ (u (τ + T))` extracted as a named `have`, equality closed by `linarith`; final substitution `convert h_chain using 1 <;> rw [h_eq]`. See `goedel_att01.md`, `goedel_att05.md`, `goedel_att07.md`, `goedel_att19.md`, `goedel_att21.md`, `goedel_att29.md`, `goedel_att34.md`, `goedel_att39.md`, `goedel_att40.md`, `goedel_att47.md`, `goedel_att49.md`.

- **G-b2** (~5 files): `convert h_comp using 1 <;> simp [mul_one]` (or `simp_all [mul_one]`) replaces `ring` for the `* 1` step; otherwise identical. See `goedel_att11.md`, `goedel_att13.md`, `goedel_att57.md`, `goedel_att61.md`.

- **G-b3** (~2 files): `convert h using 1 <;> simp [h_eq]` collapses the periodicity substitution into a single `simp` instead of a `rw`-after-linarith pair. `goedel_att03.md` additionally wraps the body in an outer `have h_main : ∀ τ, ... := by ...; exact h_main`. See `goedel_att03.md`, `goedel_att54.md`.

Across all sub-styles: `ring_nf` fires in 34/35 (flag tally); `linarith` in 33/35; `simp_all` in only 6/35 (G-b2 files). No Goedel PASS uses `specialize`, `simpa using f_periodic`, or `apply HasDerivAt.comp`.

### Kimina — all (b) lower-abstraction (5/5)

Kimina PASSes follow the same three-move logical structure but differ from Goedel at every tactic choice point. Mean 5 `have` steps per proof (min 5, max 6), mean char_len 903 — roughly half the Goedel char-len, despite similar logical content. Kimina CoT files are longer (196–222 lines vs ~143–198 for Goedel) due to reasoning verbosity, but the final proofs are tighter.

Two variants:

- **K-b1** (3 files: `kimina_att08.md`, `kimina_att14.md`, `kimina_att24.md`): shift via `simp [hasDerivAt_id', add_left_inj]`; `apply HasDerivAt.comp` in tactic mode; `specialize f_periodic τ (u (τ + T)); ring_nf at ...; linarith` (att08, att14) or `specialize; simpa using f_periodic` (att24); final substitution `rw [h9] at h2`.

- **K-b2** (2 files: `kimina_att49.md`, `kimina_att55.md`): shift via `simp [hasDerivAt_id']` without `add_left_inj`; `apply HasDerivAt.comp`; `specialize f_periodic τ (u (τ + T)); simpa using f_periodic`; `rw [h] at h`. No `linarith` in either.

In all 5 Kimina PASSes: `simp` fires (5/5); `linarith` fires in only 2/5 (K-b1 only); `ring_nf` in 2/5; no `simp_all`, no `field_simp`, no `add_const`.

## Cross-arm divergence

Both arms land in route (b) — macro-level structure is identical. Divergence is entirely at tactic idiom. Three fully disjoint patterns:

| step | Goedel (35/35) | Kimina (5/5) |
|---|---|---|
| shift derivative | `simpa using (hasDerivAt_id τ).add_const T` | `simp [hasDerivAt_id', add_left_inj]` or `simp [hasDerivAt_id']` |
| chain rule | `HasDerivAt.comp τ h h` (term mode) | `apply HasDerivAt.comp` (tactic mode) |
| f_periodic discharge | `have h := f_periodic τ _; linarith; rw [h]` | `specialize f_periodic τ _; simpa using f_periodic; rw [h] at h` |

No Goedel PASS uses `specialize` or `simpa using f_periodic`; no Kimina PASS uses `.add_const` or `linarith` on the periodicity step. The PASS count asymmetry (35 vs 5) is large; since both arms that PASS choose the same route, Kimina failures likely trace to tactic-level execution errors in the `apply HasDerivAt.comp` block or the `simpa` discharge, not to a wrong proof shape. Proof compactness diverges: Kimina scripts are ~48% shorter in char_len (903 vs 1737 mean) despite equivalent logical depth, reflecting cleaner tactic selection rather than fewer proof steps.

## Bidirectionality verdict

All 40 PASSes are structurally readable at the corrigé level: the three moves (chain rule, `hu` application, `f_periodic` conversion) appear as distinct named `have` blocks and can be traced back to informal reasoning without running the proof. However, the route (a) pipeline — assembling these moves in a single composition expression — is absent; every script stages them separately and closes sub-goals with automation. Scripts are partially bidirectional: the corrigé skeleton is recoverable, but the connecting equations (`f(τ+T,-)*1 = f(τ+T,-)` and `f(τ+T,-) = f(τ,-)`) are discharged by `ring`/`linarith`/`simpa` rather than named as explicit steps. The complete absence of route (a) across both arms — on a theorem where that pipeline is concise and natural — suggests that both model families default to defensive staging over compact proof assembly when the goal requires a derivative equality with a non-trivial value substitution.
