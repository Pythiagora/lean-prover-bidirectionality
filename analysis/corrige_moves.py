# /// script
# requires-python = ">=3.11"
# ///
"""Corrigé-grounded bidirectionality scoring.

For each of 20 focal theorems, the corrigé contains a small number of named
mathematical moves. A passing Lean script either (a) preserves the move as a
named Lean operation (`have h : ... := ...`, an `apply <named_lemma>`, an
explicit identity rewrite), or (b) hides the move inside a closing automation
chain (`<;> field_simp <;> ring_nf <;> linarith`, `nlinarith [shotgun]`,
`convert ... using 1`).

This script string-matches each PASS attempt against per-theorem move signatures
and outputs preservation rates per (theorem × prover).

Output: /tmp/bidirec_scores.json
"""

import json
import re
from pathlib import Path
from collections import defaultdict

ROOT = Path("/home/dxwoo/Code/AITP/rerun4")
OUT = Path("/tmp/bidirec_scores.json")

# ---------------------------------------------------------------------------
# Per-theorem corrigé moves with detection patterns
#
# Each move is: (name, [list of regex patterns that match its presence as a
# named Lean operation]). Patterns are case-sensitive and target named have/apply
# usages, NOT the goal itself (which is verbatim from the lemma signature).
# ---------------------------------------------------------------------------

MOVES = {
    "P3.subq_P3_I_1_a": [
        ("cos_two_mul (double-angle for cosine)", [
            r"\bReal\.cos_two_mul\b",
            r"\bcos_two_mul\b",
        ]),
        ("sin_two_mul (double-angle for sine)", [
            r"\bReal\.sin_two_mul\b",
            r"\bsin_two_mul\b",
        ]),
        ("tan = sin/cos identity", [
            r"\bReal\.tan_eq_sin_div_cos\b",
            r"\btan_eq_sin_div_cos\b",
        ]),
    ],
    "P4.subq_P4_III_1": [
        ("d(X) = AX - XA defined explicitly", [
            r"A\s*\*\s*X\s*-\s*X\s*\*\s*A",
            r"fun\s+X\s*=>\s*A\s*\*\s*X\s*-",
        ]),
    ],
    "P6.subq_I_3_a_recurrent": [
        ("characteristic polynomial coefficients (1, -5, 6)", [
            r"\b-\s*5\b",
            r"\bMatrix\.charpoly\b",
        ]),
        ("uses fact 2^n + 3^n closed form", [
            r"\(2\s*:\s*ℝ\)\s*\^",
            r"\(3\s*:\s*ℝ\)\s*\^",
        ]),
    ],
    "P7.subq_A_2_a": [
        ("block-matrix algebra (corrigé route)", [
            r"\bMatrix\.smul_apply\b.*\bMatrix\.sub_apply\b",
        ]),
        ("DETOUR: case-split via ext + by_cases", [
            r"\bext\s+i\s+j\b.*\bby_cases\b",
            r"\bfunext\s+i\s+j\b.*\bby_cases\b",
        ], "detour"),
    ],
    "P8.subq_A_1_a": [
        ("Int.isUnit_iff (∈{±1} extraction)", [
            r"\bInt\.isUnit_iff\b",
            r"\bisUnit_int_iff\b",
        ]),
    ],
    "P9.subq_4": [
        ("ContinuousAt.div composition", [
            r"\bContinuousAt\.div\b",
            r"\bContinuous\.div\b",
        ]),
    ],
    "P10.subq_II_B_1": [
        ("geometric decay |z_n - 1| = |z_0 - 1|/2^n", [
            r"\btendsto_pow_atTop_nhds_zero\b",
            r"\b1\s*/\s*2\s*\^\s*n\b",
        ]),
    ],
    "P10.subq_III_A_3_c": [
        ("Finset.sum_range_succ rewriting", [
            r"\bFinset\.sum_range_succ\b",
        ]),
    ],
    "P11.subq_I_3_b": [
        ("polar coordinates / continuity of theta", [
            r"\bReal\.arctan\b",
            r"\bReal\.tan_arctan\b",
        ]),
    ],
    "P11.subq_II_3_a": [
        ("explicit α' = 1/(λ-t)² via chain rule (named)", [
            r"\bapply\s+HasDerivAt\.div\b",
            r"\bHasDerivAt\.inv\b",
        ]),
        ("HIDDEN: chain rule via convert", [
            r"\bconvert\s+HasDerivAt\.div\b",
        ], "hidden"),
        ("sin² ≥ 0 used explicitly", [
            r"\bsq_nonneg\b.*\bsin\b",
            r"\bReal\.sin_sq_le\b",
            r"\bsin_sq_nonneg\b",
            r"Real\.sin\s*\([^)]+\)\s*\^\s*2",
        ]),
    ],
    "P11.subq_III_5_a": [
        ("Function.Periodic usage", [
            r"\bFunction\.Periodic\b",
        ]),
    ],
    "P11.subq_IV_2_a": [
        ("HasDerivAt.comp (chain rule for u(s+T))", [
            r"\bHasDerivAt\.comp\b",
        ]),
        ("f-periodicity invoked explicitly", [
            r"\bf_periodic\b",
        ]),
    ],
    "P11.subq_III_1": [
        ("Cauchy criterion / cauchy seq", [
            r"\bcauchySeq\b",
            r"\bMetric\.cauchySeq_iff\b",
        ]),
        ("MeanValueTheorem / accroissements finis", [
            r"\bMeanValueTheorem\b",
            r"\bexists_deriv_in\b",
        ]),
    ],
    "P12.subq_I_B_2_a": [
        ("(y + x/2)² identity NAMED in script", [
            r"\(y\s*\+\s*x\s*/\s*2\)\s*\^\s*2",
            r"\(x\s*/\s*2\s*\+\s*y\)\s*\^\s*2",
            r"\(y\s*\+\s*x\s*/\s*\(?\s*2\s*\)?\)\s*\^\s*2",
        ]),
        ("HIDDEN: shotgun nlinarith with multiple sq_nonneg candidates", [
            # 3+ sq_nonneg candidates in a single nlinarith call
            r"nlinarith\s*\[\s*sq_nonneg[^\]]*sq_nonneg[^\]]*sq_nonneg",
        ], "hidden"),
    ],
    "P13.subq_I_1": [
        ("continuity of f_n", [
            r"\bcontinuity\b",
            r"\bContinuous\.\w+",
        ]),
        ("strict monotonicity on [0,1]", [
            r"\bStrictMono\b",
            r"\bstrictMono\b",
            r"\bpow_lt_pow\b",
        ]),
        ("IVT / intermediate_value", [
            r"\bintermediate_value_\w+",
            r"\bContinuous\.exists_eq_of_le_of_le\b",
            r"\bIntermediateValue\b",
        ]),
    ],
    "P15.subq_I_2": [
        ("Δ linearity used explicitly", [
            r"\bLinearMap\b",
            r"\bAddHom\b",
        ]),
        ("free family / polynomial degree argument", [
            r"\bnatDegree\b",
            r"\bPolynomial\.natDegree\b",
        ]),
        ("evaluation-at-integers route", [
            r"\bP\.eval\s+\(↑n\b",
            r"\beval\s+\(↑\(?\s*n\b",
        ]),
    ],
    "P16.subq_IV_3": [
        ("MVT / accroissements finis bound", [
            r"\bexists_deriv_in\b",
            r"\bMVT\b",
            r"\bMeanValueTheorem\b",
        ]),
    ],
    "P17.subq_II_2": [
        ("induction on sequence index", [
            r"\binduction\s+\w+\s+with",
        ]),
    ],
    "P17.subq_II_4_a": [
        ("induction on sequence index + bound", [
            r"\binduction\s+\w+\s+with",
        ]),
    ],
    "P9.subq_22": [
        ("cube representation in ℤ[i√2]", [
            r"\^\s*3",
        ]),
    ],
}


# ---------------------------------------------------------------------------
# Loaders
# ---------------------------------------------------------------------------

LEAN_BLOCK_RE = re.compile(r"```lean4?\s*\n(.*?)```", re.DOTALL)
THEOREM_RE = re.compile(r"^theorem\b", re.MULTILINE)


def extract_proof(completion: str) -> str:
    if not completion:
        return ""
    blocks = LEAN_BLOCK_RE.findall(completion)
    if not blocks:
        return ""
    last = blocks[-1].strip()
    if "import Mathlib" in last or "open BigOperators" in last:
        m = THEOREM_RE.search(last)
        if m:
            last = last[m.start():].strip()
    return last


def load_arm(arm: str):
    verdicts = json.load(open(ROOT / arm / "verdicts.json"))
    completions_dir = ROOT / arm / "completions"
    out = defaultdict(list)
    for v in verdicts:
        if not v["passed"]:
            continue
        tid = v["theorem_id"]
        att = v["attempt"]
        comp_path = completions_dir / f"{tid}_{att:02d}.json"
        if not comp_path.exists():
            # fall back to candidate from verdicts (already extracted)
            proof = v.get("candidate", "") or ""
            completion = ""
        else:
            try:
                completion = json.load(open(comp_path)).get("completion", "") or ""
            except Exception:
                completion = ""
            proof = extract_proof(completion) or v.get("candidate", "") or ""
        out[tid].append({"attempt": att, "proof": proof, "completion": completion})
    return out


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------

def score_pass(proof: str, moves: list) -> dict:
    """Return per-move presence (preserved/hidden/detour/absent) for one PASS."""
    result = {}
    for entry in moves:
        if len(entry) == 2:
            name, patterns = entry
            kind = "preserved"
        else:
            name, patterns, kind = entry  # 'hidden' or 'detour'
        found = any(re.search(p, proof) for p in patterns)
        result[name] = (kind if found else "absent")
    return result


def aggregate(arm_results: dict) -> dict:
    """Per-theorem: count, preservation rate of each NAMED move (not hidden/detour)."""
    table = {}
    for tid, samples in arm_results.items():
        moves = MOVES.get(tid, [])
        if not moves:
            continue
        n_pass = len(samples)
        if n_pass == 0:
            continue
        # for each move, count presence
        per_move = {}
        for entry in moves:
            name = entry[0]
            kind_target = entry[2] if len(entry) == 3 else "preserved"
            count = sum(
                1 for s in samples if score_pass(s["proof"], moves)[name] == kind_target
            )
            per_move[name] = {
                "kind": kind_target,
                "count": count,
                "rate": round(count / n_pass, 3),
            }
        table[tid] = {"n_pass": n_pass, "moves": per_move}
    return table


def main():
    print("Loading Goedel PASSes…")
    g = load_arm("goedel")
    print(f"  Goedel theorems with PASSes: {len(g)}, total {sum(len(v) for v in g.values())}")
    print("Loading Kimina PASSes…")
    k = load_arm("kimina")
    print(f"  Kimina theorems with PASSes: {len(k)}, total {sum(len(v) for v in k.values())}")

    g_table = aggregate(g)
    k_table = aggregate(k)

    out = {
        "goedel": g_table,
        "kimina": k_table,
        "moves_definition": {
            tid: [{"name": e[0], "kind": (e[2] if len(e) == 3 else "preserved")} for e in moves]
            for tid, moves in MOVES.items()
        },
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(f"\nWrote {OUT}")

    # Pretty-print summary
    print(f"\n{'Theorem':35} {'Move':60} {'G':>4} {'K':>4}")
    print("-" * 110)
    for tid in sorted(set(list(g_table.keys()) + list(k_table.keys()))):
        for entry in MOVES.get(tid, []):
            name = entry[0]
            kind = entry[2] if len(entry) == 3 else "preserved"
            g_rec = g_table.get(tid, {}).get("moves", {}).get(name, {"rate": None})
            k_rec = k_table.get(tid, {}).get("moves", {}).get(name, {"rate": None})
            g_str = f"{g_rec['rate']:.2f}" if g_rec.get("rate") is not None else "—"
            k_str = f"{k_rec['rate']:.2f}" if k_rec.get("rate") is not None else "—"
            tag = "" if kind == "preserved" else f"({kind})"
            print(f"{tid:35} {name[:55]+tag:60} {g_str:>4} {k_str:>4}")


if __name__ == "__main__":
    main()
