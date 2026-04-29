# /// script
# requires-python = ">=3.11"
# ///
"""Verify the abstraction-level claim precisely.

CLAIM: theorems whose corrigés use abstract structural arguments (free families,
block-matrix algebra, abstract algebra invariants, completeness arguments)
systematically push SOTA Lean provers toward lower-abstraction-level closure
routes.

METHOD:
1. Classify each of 20 focal theorems by corrigé abstraction level, based on the
   corrigé text *alone* (not on PASS data — to avoid post-hoc bias).
2. For each theorem, build a per-corrigé route detection pattern AND a "lower-level
   detour" detection pattern.
3. Compute route preservation rate, detour rate, both.
4. Aggregate by abstraction level. Report sample size honestly.
"""

import json, re
from pathlib import Path
from collections import defaultdict

ROOT = Path("/home/dxwoo/Code/AITP/rerun4")
OUT = Path("/tmp/abstraction_level_verification.json")


# Classification by corrigé text ALONE — no peeking at PASS data.
# Three buckets:
#   "concrete": algebraic identity, direct computation, finite case enumeration
#   "standard": application of one named Mathlib lemma (MVT, IVT, ContinuousAt.div, etc.)
#   "abstract": structural argument at the algebra/topology/category level
#               (free family, block-matrix algebra, completeness, unique factorization)

THEOREMS = {
    "P3.subq_P3_I_1_a": {
        "level": "concrete",
        "corrige_route": "double-angle identities cos_two_mul, sin_two_mul",
        "route_pattern": [r"\bcos_two_mul\b", r"\bsin_two_mul\b", r"\btan_eq_sin_div_cos\b"],
        "lower_level_pattern": [],  # there is no lower level — this IS the algebraic level
    },
    "P4.subq_P4_III_1": {
        "level": "abstract",
        "corrige_route": "define d(X) := AX - XA, verify Leibniz law structurally",
        "route_pattern": [r"\bderivation\b", r"\bLieDerivation\b", r"\bLinearMap\.mk\b"],
        "lower_level_pattern": [r"\bA\s*\*\s*X\s*-\s*X\s*\*\s*A"],  # explicit subtraction
    },
    "P6.subq_I_3_a_recurrent": {
        "level": "concrete",
        "corrige_route": "compute characteristic polynomial roots → coefficients (1,-5,6)",
        "route_pattern": [r"\(2\s*:\s*ℝ\)\s*\^.*\(3\s*:\s*ℝ\)\s*\^"],
        "lower_level_pattern": [],
    },
    "P7.subq_A_2_a": {
        "level": "abstract",
        "corrige_route": "block-matrix algebra: factor -1/(n-1) from L",
        "route_pattern": [
            r"\bMatrix\.smul\b.*-1\s*/\s*\(?n\s*-\s*1",  # block-level factoring
        ],
        "lower_level_pattern": [r"\bext\s+i\s+j\b.*\bby_cases\b|\bfunext\s+i\s+j\b.*\bby_cases\b"],
    },
    "P8.subq_A_1_a": {
        "level": "standard",
        "corrige_route": "det invertible in ℤ ⇒ det is unit ⇒ ±1 (Int.isUnit_iff)",
        "route_pattern": [r"\bInt\.isUnit_iff\b", r"\bisUnit_int_iff\b"],
        "lower_level_pattern": [],
    },
    "P9.subq_4": {
        "level": "standard",
        "corrige_route": "ContinuousAt.div composition",
        "route_pattern": [r"\bContinuousAt\.div\b|\bContinuous\.div\b"],
        "lower_level_pattern": [],
    },
    "P9.subq_22": {
        "level": "abstract",
        "corrige_route": "unique factorization in ℤ[i√2] yields cube representation",
        "route_pattern": [r"\bUniqueFactorizationMonoid\b"],
        "lower_level_pattern": [],
    },
    "P10.subq_II_B_1": {
        "level": "concrete",
        "corrige_route": "geometric decay |z_n - 1| = |z_0 - 1|/2^n",
        "route_pattern": [r"\btendsto_pow_atTop_nhds_zero\b|\b1\s*/\s*2\s*\^"],
        "lower_level_pattern": [],
    },
    "P10.subq_III_A_3_c": {
        "level": "concrete",
        "corrige_route": "Finset.sum_range_succ rewriting",
        "route_pattern": [r"\bFinset\.sum_range_succ\b"],
        "lower_level_pattern": [],
    },
    "P11.subq_I_3_b": {
        "level": "standard",
        "corrige_route": "continuity of θ from polar decomposition + Real.arctan",
        "route_pattern": [r"\bReal\.arctan\b|\bReal\.tan_arctan\b|\bReal\.atan2\b"],
        "lower_level_pattern": [],
    },
    "P11.subq_II_3_a": {
        "level": "standard",
        "corrige_route": "chain rule on (λ-s)⁻¹ via HasDerivAt.div + sin² ≥ 0",
        "route_pattern": [r"\bapply\s+HasDerivAt\.div\b|\bHasDerivAt\.inv\b"],
        "lower_level_pattern": [r"\bconvert\s+HasDerivAt\.div\b"],  # via convert (chain-rule erasure)
    },
    "P11.subq_III_1": {
        "level": "abstract",
        "corrige_route": "MVT + Cauchy criterion (completeness of ℝ)",
        "route_pattern": [r"\bcauchySeq\b|\bMetric\.cauchySeq_iff\b"],
        "lower_level_pattern": [],
    },
    "P11.subq_III_5_a": {
        "level": "standard",
        "corrige_route": "Function.Periodic + Cauchy-Lipschitz",
        "route_pattern": [r"\bFunction\.Periodic\b"],
        "lower_level_pattern": [],
    },
    "P11.subq_IV_2_a": {
        "level": "standard",
        "corrige_route": "HasDerivAt.comp (chain rule) + f-periodicity",
        "route_pattern": [r"\bHasDerivAt\.comp\b"],
        "lower_level_pattern": [],
    },
    "P12.subq_I_B_2_a": {
        "level": "concrete",
        "corrige_route": "complete the square (y + x/2)²",
        "route_pattern": [
            r"\(y\s*\+\s*x\s*/\s*2\)\s*\^\s*2",
            r"\(x\s*/\s*2\s*\+\s*y\)\s*\^\s*2",
        ],
        "lower_level_pattern": [
            r"nlinarith\s*\[\s*sq_nonneg[^\]]*sq_nonneg[^\]]*sq_nonneg",
        ],
    },
    "P13.subq_I_1": {
        "level": "standard",
        "corrige_route": "continuity + monotonicity + IVT",
        "route_pattern": [
            r"\bintermediate_value_\w+|\bContinuous\.exists_eq_of_le_of_le\b|\bIntermediateValue\b",
        ],
        "lower_level_pattern": [],
    },
    "P15.subq_I_2": {
        "level": "abstract",
        "corrige_route": "free family of (Δe_k) by degree drop ⇒ ker(Δ) = constants",
        "route_pattern": [r"\bLinearIndependent\b|\bisLinearIndependent\b"],
        "lower_level_pattern": [r"\bnatDegree\b", r"\beval\s+\(↑\(?\s*n\b"],
    },
    "P16.subq_IV_3": {
        "level": "standard",
        "corrige_route": "MVT bound for Lipschitz constant",
        "route_pattern": [r"\bexists_deriv_in\b|\bMVT\b|\bMeanValueTheorem\b"],
        "lower_level_pattern": [],
    },
    "P17.subq_II_2": {
        "level": "concrete",
        "corrige_route": "induction on sequence index",
        "route_pattern": [r"\binduction\s+\w+\s+with"],
        "lower_level_pattern": [],
    },
    "P17.subq_II_4_a": {
        "level": "concrete",
        "corrige_route": "induction on sequence index + bound",
        "route_pattern": [r"\binduction\s+\w+\s+with"],
        "lower_level_pattern": [],
    },
}


LEAN_BLOCK_RE = re.compile(r"```lean4?\s*\n(.*?)```", re.DOTALL)
THEOREM_RE = re.compile(r"^theorem\b", re.MULTILINE)


def extract_proof(completion):
    if not completion: return ""
    blocks = LEAN_BLOCK_RE.findall(completion)
    if not blocks: return ""
    last = blocks[-1].strip()
    if "import Mathlib" in last or "open BigOperators" in last:
        m = THEOREM_RE.search(last)
        if m: last = last[m.start():].strip()
    return last


def matches_any(text, patterns):
    return any(re.search(p, text, re.DOTALL) for p in patterns) if patterns else False


def load_passes(arm):
    verdicts = json.load(open(ROOT / arm / "verdicts.json"))
    completions_dir = ROOT / arm / "completions"
    by_theorem = defaultdict(list)
    for v in verdicts:
        if not v["passed"]: continue
        tid = v["theorem_id"]
        att = v["attempt"]
        comp_path = completions_dir / f"{tid}_{att:02d}.json"
        completion = ""
        if comp_path.exists():
            try:
                completion = json.load(open(comp_path)).get("completion", "") or ""
            except Exception:
                completion = ""
        proof = extract_proof(completion) or v.get("candidate", "") or ""
        by_theorem[tid].append({"attempt": att, "proof": proof})
    return by_theorem


def main():
    g = load_passes("goedel")
    k = load_passes("kimina")

    rows = []
    for tid, info in THEOREMS.items():
        gs = g.get(tid, [])
        ks = k.get(tid, [])
        def stats(samples):
            n = len(samples)
            if n == 0: return None
            n_route = sum(1 for s in samples if matches_any(s["proof"], info["route_pattern"]))
            n_lower = sum(1 for s in samples if matches_any(s["proof"], info["lower_level_pattern"]))
            return {"n_pass": n, "route_rate": round(n_route/n, 2), "lower_rate": round(n_lower/n, 2)}
        rows.append({"tid": tid, **info, "goedel": stats(gs), "kimina": stats(ks)})

    # Group by level
    by_level = defaultdict(list)
    for r in rows:
        by_level[r["level"]].append(r)

    # Report
    print(f'\n{"="*120}')
    print('PER-THEOREM (corrigé level → route preservation, lower-level detour)')
    print(f'{"="*120}\n')
    print(f'{"Theorem":30} {"Level":11} {"Goedel n":>8} {"GRoute%":>8} {"GLower%":>8} {"Kimina n":>8} {"KRoute%":>8} {"KLower%":>8}')
    print('-' * 110)
    for level in ["concrete", "standard", "abstract"]:
        for r in by_level[level]:
            gs = r["goedel"]; ks = r["kimina"]
            def fmt(s, k):
                if not s: return "—"
                return f'{s[k]*100:.0f}%'
            print(f'{r["tid"]:30} {r["level"]:11} '
                  f'{(gs["n_pass"] if gs else 0):>8} {fmt(gs, "route_rate"):>8} {fmt(gs, "lower_rate"):>8} '
                  f'{(ks["n_pass"] if ks else 0):>8} {fmt(ks, "route_rate"):>8} {fmt(ks, "lower_rate"):>8}')
        print()

    # Aggregate by level (only theorems with PASSes on the relevant arm)
    print(f'\n{"="*100}')
    print('AGGREGATE BY ABSTRACTION LEVEL (mean route-preservation rate, weighted by theorem; arms separate)')
    print(f'{"="*100}\n')
    print(f'{"Level":12} {"# theorems":>12} {"# G theorems w/ PASS":>22} {"Mean G route":>14} {"# K theorems w/ PASS":>22} {"Mean K route":>14}')
    print('-' * 110)
    for level in ["concrete", "standard", "abstract"]:
        rs = by_level[level]
        n_theorems = len(rs)
        g_rates = [r["goedel"]["route_rate"] for r in rs if r["goedel"]]
        k_rates = [r["kimina"]["route_rate"] for r in rs if r["kimina"]]
        gmean = sum(g_rates)/len(g_rates) if g_rates else None
        kmean = sum(k_rates)/len(k_rates) if k_rates else None
        print(f'{level:12} {n_theorems:>12} {len(g_rates):>22} '
              f'{(f"{gmean*100:.0f}%" if gmean is not None else "—"):>14} '
              f'{len(k_rates):>22} '
              f'{(f"{kmean*100:.0f}%" if kmean is not None else "—"):>14}')

    json.dump({"rows": rows, "by_level": {k: [r["tid"] for r in v] for k, v in by_level.items()}},
              open(OUT, "w"), indent=1)
    print(f'\nWrote {OUT}')


if __name__ == "__main__":
    main()
