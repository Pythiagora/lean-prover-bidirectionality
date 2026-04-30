# P11.subq_III_5_a — per-theorem deep dive

**Total PASSes**: 7 (7 Goedel + 0 Kimina)

**Arm asymmetry**: Goedel 7/64 (11%), Kimina 0/64 (0%). Kimina ceiling — zero PASSes from 64
attempts. The 7 Goedel PASSes are a thin tail; this theorem sits at the high end of difficulty
for both arms.

## Statement

Time-reversal equivalence for ODEs. Show that `∀ t, HasDerivAt u (f t (u t)) t` iff
`∀ τ, HasDerivAt (fun s => u (-s)) (-f (-τ) (u (-τ))) τ`. Both directions rely on the
chain rule applied to `s ↦ -s`, which has derivative `-1`.

## Corrigé route

- **(a) Route-preserving**: explicit `HasDerivAt.comp` with the negation map; inner derivative
  established via `(hasDerivAt_id τ).neg`; arithmetic close by `ring`.
- **(b) Lower-abstraction**: `HasDerivAt.scomp` / explicit limit definition + `simp` lemmas.
- **(c) Opaque**: pure shotgun.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 7 | 5 (71%) | 2 (29%) | 0 (0%) |
| Kimina | 0 | — | — | — |
| **Both** | **7** | **5 (71%)** | **2 (29%)** | **0 (0%)** |

## Sub-styles per arm

### Goedel — (a) route-preserving (5/7): att10, att22, att27, att37, att49

All five use `HasDerivAt.comp` for both directions. The forward direction is uniform across all
seven files: establish `HasDerivAt (fun s => -s) (-1) τ` via
`simpa using (hasDerivAt_id τ).neg`, instantiate `h (-τ)`, apply `HasDerivAt.comp τ h₂ h₁`,
close the arithmetic goal with `ring` or `convert ... using 1 <;> ring`. This is a direct
transcription of the corrigé's chain-rule move.

The backward direction recovers `u` as the double composition
`(fun s => u (-s)) ∘ (fun s => -s)`, proved equal to `u` by `funext s; simp [neg_neg]`, then
applies `HasDerivAt.comp t h₁₉ h₁₈` and closes `(-f t (u t)) * (-1) = f t (u t)` by `ring`.

Two sub-styles within (a):

- **G-a1** (4 files: att10, att22, att27, att49): backward uses `funext`/`simp [neg_neg]` to
  rewrite `u` as the double composition, then `HasDerivAt.comp` + `convert ... using 1` with a
  `ring_nf`/`simp_all`/`linarith` cascade on the derivative equation. Deep `have`-nesting
  (26–44 `have` statements); char-len 3435–4939. The shotgun close (`ring_nf <;> simp_all
  [neg_neg] <;> linarith`) signals uncertainty about which tactic alone closes the `neg_neg`
  rewrite goal after `convert`.

- **G-a2** (1 file: att37): same double-composition backward strategy but adds `norm_num`,
  `field_simp`, and `linarith` in the close for the `neg_neg` simplification. 27 `have`
  statements, 3455 chars. Minor variant of G-a1.

### Goedel — (b) lower-abstraction (2/7): att45, att60

Both files step below the `HasDerivAt.comp` level for the backward direction.

- **G-b1** (att45): backward introduces `deriv u` via `DifferentiableAt.hasDerivAt`, then uses
  `HasDerivAt.unique` to equate the two derivative values (`deriv u t * (-1) = -f t (u t)`),
  and concludes with `linarith` to extract `deriv u t = f t (u t)`. Forward direction still uses
  `HasDerivAt.comp`. Divergence localised to the backward direction and traces to applying
  `HasDerivAt.unique` as the primary closing move rather than a second `HasDerivAt.comp`. 31
  `have` statements, 3550 chars.

- **G-b2** (att60): backward unpacks `HasDerivAt` to `Filter.Tendsto` via
  `h₃.tendsto_slope_zero`, performs manual variable substitutions (`t - h` vs `t + h`), invokes
  `tendsto_neg_nhds_zero` for the sign flip, and reconstructs `HasDerivAt` from the limit via
  `hasDerivAt_iff_tendsto_slope.mpr`. Uses `by_cases h₁₆ : h = 0` to handle division by zero in
  one sub-step. Lowest-abstraction PASS in this corpus: the proof descends to epsilon-delta filter
  machinery absent from all other files. 28 `have` statements, 4720 chars.

## Cross-arm summary

Within Goedel, the forward direction is uniform and route-preserving across all 7 files.
The backward direction splits: 5/7 use `HasDerivAt.comp` via double-composition (route (a),
with heavy `have`-nesting and shotgun arithmetic closes), while 2/7 step below — one to
`HasDerivAt.unique` (att45) and one to filter tendencies (att60). No file uses `HasDerivAt.scomp`
or a standalone `hasDerivAt_neg` call on the composed function. Kimina 0/64 leaves the cross-arm
comparison structurally absent; the asymmetry is the primary quantitative finding.

## Bidirectionality verdict

The 5 route-(a) scripts are partially bidirectional: the chain-rule move (`HasDerivAt.comp` with
inner derivative `-1`) is named and recoverable in both directions, and the double-composition
identity `u = (fun s => u (-s)) ∘ (fun s => -s)` makes the backward argument explicit. The
arithmetic close for the backward direction is a cascade (`ring_nf <;> simp_all [neg_neg] <;>
linarith`) whose individual steps do not correspond to named mathematical operations, so full
bidirectionality does not hold. The two route-(b) scripts are not bidirectional: att45 encodes the
derivative value via `HasDerivAt.unique` without inscribing the algebraic identity, and att60
buries the argument in filter infrastructure with no informal counterpart in the corrigé.
