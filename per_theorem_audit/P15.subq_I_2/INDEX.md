# P15.subq_I_2 — per-theorem deep dive

**Total PASSes**: 8 (4 Goedel + 4 Kimina) — both arms low (4/64 each)

## Statement

ΔP = P(X+1) − P(X). Show (1) ker Δ = {constants}, i.e. ΔP = 0 iff ∃c, P = C c;
(2) Δ is not injective.

## Corrigé routes

**(a) Route-preserving**: kernel via `comp_X_add_C` structure — either invoke a named
Mathlib lemma (`Polynomial.eq_C_of_comp_X_add_C_eq_self`) or use the (n−1)-coefficient
argument directly on `P.comp (X + C 1)` to show n·leadingCoeff = 0 hence natDegree = 0.
Non-injectivity via two distinct constants (both in ker Δ).

**(b) Lower-abstraction**: kernel via evaluation at infinitely many points (induction on ℕ
or ℤ, then `Polynomial.finite_setOf_isRoot` or `eq_zero_of_infinite_eval_eq_zero` to
conclude P − C(P(0)) = 0). The algebraic structure of Δ as a composition operator is not
used directly; the argument goes through the function-value side.

**(c) Opaque**: no PASSes observed.

## Classification table

| arm | total | (a) route-preserving | (b) lower-abstraction | (c) opaque |
|---|---:|---:|---:|---:|
| Goedel | 4 | 0 (0%) | 4 (100%) | 0 (0%) |
| Kimina | 4 | 2 (50%) | 2 (50%) | 0 (0%) |
| **Both** | **8** | **2 (25%)** | **6 (75%)** | **0 (0%)** |

## Per-PASS analysis

### Goedel — all (b) lower-abstraction

All four Goedel PASSes share the `have h_main := by ...; exact h_main` outer wrapper and a
multi-step shotgun close (`simp_all / ring_nf / norm_num / linarith / aesop`).

- **goedel_att00** (6188 chars, 137 lines): kernel via nat induction — shows P(n) = P(0) for
  all n : ℕ by induction using `Polynomial.eval_comp`; then `Polynomial.finite_setOf_isRoot`
  on P − C(P(0)) to conclude it is zero. Non-injectivity: X vs X + C 1 with evaluation
  argument. Close: `ring_nf <;> simp_all <;> norm_num <;> linarith`.
- **goedel_att36** (9336 chars, 191 lines): kernel via `natDegree` degree argument — attempts
  to compute coeff (P.natDegree − 1) of `P.comp (X + C 1) − P` using `Polynomial.coeff_comp`
  inside a four-layer `try { ... }` cascade. Uses a `calc` block for the coefficient
  subtraction. Non-injectivity: C 0 vs C 1. This PASS attempts the coefficient route but
  buries `Polynomial.coeff_comp` in an opaque cascade rather than using it as a named step.
- **goedel_att47** (6395 chars, 155 lines): kernel via nat induction, same route as att00.
  Non-injectivity: C 0 vs C 1. Close: `ring_nf <;> simp_all <;> norm_num`.
- **goedel_att57** (10389 chars, 244 lines): kernel via `natDegree` argument — explicitly
  constructs `Finset.Icc (P.natDegree − 1) P.natDegree`, decomposes into `{P.natDegree − 1,
  P.natDegree}`, and computes the (n−1) coefficient via `Nat.choose`. The coefficient
  computation is structurally corrigé-aligned, but each sub-step close is a four-layer
  cascade (`ring_nf <;> simp_all <;> norm_num <;> linarith`). Non-injectivity: C 0 vs C 1.
  Most verbose Goedel PASS (244 lines, 10389 chars).

### Kimina — (a) route-preserving (2/4) and (b) lower-abstraction (2/4)

- **kimina_att02** (4858 chars, 106 lines): **(a)** Kernel via `natDegree` + explicit
  `Polynomial.coeff_comp` + `Nat.choose (P.natDegree) 1 = P.natDegree` to show
  leadingCoeff = 0, contradiction. Each step is a named `have` without shotgun fallback;
  the `linarith` close is single-purpose. Non-injectivity: X² vs X² + C 1 with
  `simp [pow_two, Polynomial.comp_add] <;> ring_nf`.
- **kimina_att03** (6414 chars, 124 lines): **(b)** Kernel via ℤ-induction on evaluation
  (`Int.induction_on`) + infinite roots. Non-injectivity: C 0 vs C 1.
- **kimina_att18** (3128 chars, 58 lines): **(a)** Kernel closed in a single line:
  `Polynomial.eq_C_of_comp_X_add_C_eq_self`. The only PASS across all 8 that invokes a
  named Mathlib lemma directly encoding the structural invariant of Δ. After establishing
  `P.comp (X + C 1) = P`, the entire constantness argument reduces to one named application.
  Shortest PASS (58 lines, 3128 chars). Non-injectivity: C(1)·X vs C(1)·X + C 1 via
  `comp_add / add_comp / comp_mul / mul_comp <;> ring_nf`.
- **kimina_att28** (6196 chars, 135 lines): **(b)** Kernel via nat induction + separate
  negative-nat induction, then `Polynomial.eq_zero_of_infinite_eval_eq_zero` on P − C(P(0)).
  Uses `Polynomial.funext` to reduce to evaluation equality. Non-injectivity: X vs X + C 1.

## Cross-arm comparison

Goedel is 100% route (b); Kimina splits 50/50 between (a) and (b). Both arms that land in
(b) share the same macro-strategy — evaluate at naturals or integers, show infinite roots,
conclude zero — but Goedel universally wraps in `have h_main`, Kimina does not. Within route
(a), the two Kimina PASSes diverge: kimina_att18 invokes `eq_C_of_comp_X_add_C_eq_self` (the
most condensed possible corrigé transcription), while kimina_att02 spells out the coefficient
calculation with `Polynomial.coeff_comp` and `Nat.choose` at full detail. Goedel's att36 and
att57 attempt the coefficient route but bury the key step in shotgun cascades, remaining in
(b). No Goedel PASS invokes `Polynomial.eq_C_of_comp_X_add_C_eq_self` or produces a clean
named rewrite for the compositional structure of Δ.

A sharp heuristic marker: `simp_all` fires 4/4 in Goedel and 0/4 in Kimina; `ring` fires
1/4 in Goedel and 4/4 in Kimina. Kimina also uses `calc` blocks (mean 3 per PASS) where
Goedel averages 0.25. Char-len range: Goedel 6188–10389 (mean 8077); Kimina 3128–6414
(mean 5149).

Non-injectivity witnesses are heterogeneous: four use C 0 vs C 1, two use X vs X + C 1, one
uses X² vs X² + C 1, one uses C(1)·X vs C(1)·X + C 1. All exploit ker Δ = constants.

## Bidirectionality verdict

The two Kimina (a) PASSes are strongly bidirectional: kimina_att18 names the entire kernel
argument in one Mathlib lemma (`Polynomial.eq_C_of_comp_X_add_C_eq_self`), and kimina_att02
inscribes the (n−1)-coefficient step with `Polynomial.coeff_comp` and `Nat.choose` in a
sequence a reader can follow without running the proof. All six (b) PASSes are weakly
bidirectional at best: the induction structure is visible, but the infinite-roots closure
and arithmetic cascade steps are opaque — the specific corrigé reasoning (degree drops by 1
under Δ, n·leadingCoeff ≠ 0) is not recoverable from the script without execution.
