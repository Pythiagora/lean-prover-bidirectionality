# /// script
# requires-python = ">=3.11"
# ///
"""More findings from corrigé vs PASS comparison.

Beyond "is the move named", three further angles:

A. CORRIGÉ-ROUTE-NEVER-FOUND. The corrigé proceeds via a specific named argument
   (e.g. free family, block-matrix factoring). Do the prover PASSes use that
   argument, or do they take a different valid route?

B. EXPANSION RATIO (informal De Bruijn factor). chars(PASS) / chars(corrigé excerpt).
   Bidirectional Goedel S1 vs shotgun Kimina S3 differ in compression direction.

C. CROSS-PROVER ROUTE CONVERGENCE. When both arms close, do they converge on the
   same closure tactic family, and is that family aligned with or away from the
   corrigé?

Output: /tmp/corrige_route_findings.json + printed table.
"""

import json, re
from pathlib import Path
from collections import Counter

ROOT = Path("/home/dxwoo/Code/AITP/rerun4")
OUT = Path("/tmp/corrige_route_findings.json")

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


# Per-theorem corrigé length (rough char count from corrigé excerpt) and corrigé route signature
CORRIGE_INFO = {
    "P3.subq_P3_I_1_a": {
        "chars": 220,
        "route": "double-angle identities",
        "route_pattern": [r"\bcos_two_mul\b", r"\bsin_two_mul\b", r"\btan_eq_sin_div_cos\b"],
    },
    "P11.subq_II_3_a": {
        "chars": 130,
        "route": "chain rule on (λ-s)⁻¹ + sin² ≥ 0",
        "route_pattern": [r"\bapply\s+HasDerivAt\.div\b"],
    },
    "P11.subq_III_1": {
        "chars": 200,
        "route": "MVT + Cauchy criterion",
        "route_pattern": [r"\bcauchySeq\b|\bMetric\.cauchySeq_iff\b"],
    },
    "P11.subq_IV_2_a": {
        "chars": 60,
        "route": "chain rule + f-periodicity",
        "route_pattern": [r"\bHasDerivAt\.comp\b"],
    },
    "P12.subq_I_B_2_a": {
        "chars": 80,
        "route": "completing the square (y+x/2)²",
        "route_pattern": [r"\(y\s*\+\s*x\s*/\s*2\)\s*\^\s*2|\(x\s*/\s*2\s*\+\s*y\)\s*\^\s*2"],
    },
    "P13.subq_I_1": {
        "chars": 260,
        "route": "continuity + monotonicity + IVT",
        "route_pattern": [r"\bintermediate_value_\w+|\bContinuous\.exists_eq_of_le_of_le\b"],
    },
    "P15.subq_I_2": {
        "chars": 400,
        "route": "free family of (Δe_k) by degree drop",
        "route_pattern": [r"\bLinearIndependent\b|\bisLinearIndependent\b|\bfree_family\b"],
    },
    "P7.subq_A_2_a": {
        "chars": 150,
        "route": "block-matrix factoring of L",
        "route_pattern": [r"\bMatrix\.smul_apply\b.*\bMatrix\.sub_apply\b(?!.*ext\s+i\s+j)"],
    },
    "P9.subq_4": {
        "chars": 120,
        "route": "ContinuousAt.div composition",
        "route_pattern": [r"\bContinuousAt\.div\b|\bContinuous\.div\b"],
    },
    "P6.subq_I_3_a_recurrent": {
        "chars": 140,
        "route": "characteristic polynomial x²-5x+6 → coeffs (1,-5,6)",
        "route_pattern": [r"\(2\s*:\s*ℝ\)\s*\^.*\(3\s*:\s*ℝ\)\s*\^"],
    },
}


def has_corrige_route(proof, patterns):
    return any(re.search(p, proof, re.DOTALL) for p in patterns)


def load_passes(arm):
    verdicts = json.load(open(ROOT / arm / "verdicts.json"))
    completions_dir = ROOT / arm / "completions"
    by_theorem = {}
    for v in verdicts:
        if not v["passed"]: continue
        tid = v["theorem_id"]
        att = v["attempt"]
        comp_path = completions_dir / f"{tid}_{att:02d}.json"
        if comp_path.exists():
            try:
                completion = json.load(open(comp_path)).get("completion", "") or ""
            except Exception:
                completion = ""
            proof = extract_proof(completion) or v.get("candidate", "") or ""
        else:
            proof = v.get("candidate", "") or ""
        by_theorem.setdefault(tid, []).append({"attempt": att, "proof": proof})
    return by_theorem


def main():
    g = load_passes("goedel")
    k = load_passes("kimina")

    rows = []
    for tid, info in CORRIGE_INFO.items():
        g_samples = g.get(tid, [])
        k_samples = k.get(tid, [])

        def stats(samples):
            n = len(samples)
            if n == 0: return None
            chars = [len(s["proof"]) for s in samples]
            mean_chars = sum(chars) / n
            n_route = sum(1 for s in samples if has_corrige_route(s["proof"], info["route_pattern"]))
            return {
                "n_pass": n,
                "mean_chars": round(mean_chars, 0),
                "expansion_ratio": round(mean_chars / info["chars"], 1),
                "route_preservation_rate": round(n_route / n, 2),
                "n_route_preserved": n_route,
            }

        gs = stats(g_samples)
        ks = stats(k_samples)
        rows.append({
            "tid": tid,
            "corrige_route": info["route"],
            "corrige_chars": info["chars"],
            "goedel": gs,
            "kimina": ks,
        })

    # Print
    print(f'\n{"Theorem":30} {"Corrigé route":40}\n')
    print(f'{"":30} {"Cor#":>5} {"G_n":>4} {"G_chars":>8} {"G_exp":>6} {"G_route%":>9}    {"K_n":>4} {"K_chars":>8} {"K_exp":>6} {"K_route%":>9}')
    print('-' * 130)
    for r in rows:
        gs = r["goedel"]; ks = r["kimina"]
        gc, gx, gr_ = (gs["mean_chars"], gs["expansion_ratio"], gs["route_preservation_rate"]) if gs else (0,0,0)
        gn = gs["n_pass"] if gs else 0
        kc, kx, kr_ = (ks["mean_chars"], ks["expansion_ratio"], ks["route_preservation_rate"]) if ks else (0,0,0)
        kn = ks["n_pass"] if ks else 0
        print(f'{r["tid"]:30} {r["corrige_route"][:38]:40}')
        print(f'{"":30} {r["corrige_chars"]:>5} {gn:>4} {gc:>8.0f} {gx:>5.1f}× {f"{gr_*100:.0f}%":>9}    {kn:>4} {kc:>8.0f} {kx:>5.1f}× {f"{kr_*100:.0f}%":>9}')

    json.dump({"rows": rows}, open(OUT, "w"), indent=1)
    print(f'\nWrote {OUT}')


if __name__ == "__main__":
    main()
