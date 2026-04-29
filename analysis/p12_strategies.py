# /// script
# requires-python = ">=3.11"
# ///
"""How many distinct proof strategies emerge in the 119 PASSes on P12?

Theorem: ∀ x y : ℝ, x² + xy + y² ≥ (3/4) x².

Mathematical strategy space (closure-equivalent):
  S1. Square decomposition (corrigé): x² + xy + y² = (y + x/2)² + (3/4)x².
      Closure pattern: have h : (1/4)x² + xy + y² = (y + x/2)² := by ring; nlinarith [sq_nonneg (y + x/2)].
  S2. Single-square nlinarith hint: nlinarith [sq_nonneg (y + x/2)] OR equivalent (e.g. sq_nonneg (x + 2y)).
      The square is named as a single candidate; reader can recover it.
  S3. Shotgun nlinarith hint: nlinarith [sq_nonneg (a), sq_nonneg (b), ...] with 3+ candidates.
      Reader cannot tell which candidate is load-bearing without redoing the algebra.
  S4. positivity / polyrith / black-box automation.
      Pure tactic; reader recovers nothing.
  S5. Other: novel routes (calculus, eigenvalues, etc.) — likely none.

For each PASS, classify into S1-S5 and grade bidirectionality:
  S1 → 1.0   (named identity preserved)
  S2 → 0.6   (square present in single candidate, recoverable but not narrated)
  S3 → 0.2   (load-bearing candidate hidden among others)
  S4 → 0.0   (no informal content recoverable)
  S5 → manually graded
"""

import json
import re
from pathlib import Path
from collections import Counter

ROOT = Path("/home/dxwoo/Code/AITP/rerun4")
OUT = Path("/tmp/p12_strategy_distribution.json")

# Strategy patterns (ordered by specificity; first match wins)

NAMED_SQ_DECOMP_RE = re.compile(
    r"have\s+\w+\s*:[^=]*=\s*\([^)]*y\s*\+\s*x\s*/\s*2[^)]*\)\s*\^\s*2"
    r"|have\s+\w+\s*:[^=]*=\s*\([^)]*x\s*/\s*2\s*\+\s*y[^)]*\)\s*\^\s*2"
)

# nlinarith with sq_nonneg candidates
NLINARITH_SQ_RE = re.compile(r"nlinarith\s*\[([^\]]+)\]", re.DOTALL)
SQ_CAND_RE = re.compile(r"sq_nonneg\s*\(([^)]+)\)|sq_nonneg\s+([^,\]]+)")

POSITIVITY_RE = re.compile(r"\bpositivity\b")
POLYRITH_RE = re.compile(r"\bpolyrith\b")
NORM_NUM_ALONE_RE = re.compile(r"^\s*norm_num\s*$", re.MULTILINE)


def classify(proof: str) -> tuple[str, float, dict]:
    """Return (strategy_id, bidirec_score, details)."""
    info = {}

    # S1: Named square decomposition
    if NAMED_SQ_DECOMP_RE.search(proof):
        info["named_have"] = NAMED_SQ_DECOMP_RE.search(proof).group(0)[:100]
        return ("S1_named_decomp", 1.0, info)

    # Look for nlinarith[…] candidates
    m = NLINARITH_SQ_RE.search(proof)
    if m:
        candidates_str = m.group(1)
        candidates = []
        for cm in SQ_CAND_RE.finditer(candidates_str):
            cand = (cm.group(1) or cm.group(2) or "").strip()
            if cand:
                candidates.append(cand)
        info["nlinarith_candidates"] = candidates
        info["n_candidates"] = len(candidates)

        # Does any candidate match the corrigé square (y + x/2) or scalar multiple (x + 2y)?
        corrige_eq = [
            r"y\s*\+\s*x\s*/\s*2",
            r"x\s*/\s*2\s*\+\s*y",
            r"x\s*\+\s*2\s*\*?\s*y",
            r"2\s*\*?\s*y\s*\+\s*x",
        ]
        has_corrige = any(re.search(p, c) for c in candidates for p in corrige_eq)
        info["has_corrige_square"] = has_corrige

        if len(candidates) == 1:
            return ("S2_single_sq_nonneg", 0.6, info)
        elif len(candidates) >= 3:
            return ("S3_shotgun_nlinarith", 0.2, info)
        else:  # 2 candidates
            return ("S2b_two_candidates", 0.4, info)

    # S4: pure black-box automation
    if POSITIVITY_RE.search(proof):
        return ("S4_positivity", 0.0, info)
    if POLYRITH_RE.search(proof):
        return ("S4_polyrith", 0.0, info)

    return ("S5_other", None, info)


def main():
    # Pull P12 PASSes
    g_verdicts = json.load(open(ROOT / "goedel/verdicts.json"))
    k_verdicts = json.load(open(ROOT / "kimina/verdicts.json"))

    def collect(verdicts, tid="P12.subq_I_B_2_a"):
        out = []
        for v in verdicts:
            if v["theorem_id"] == tid and v["passed"]:
                out.append({"attempt": v["attempt"], "proof": v.get("candidate", "") or ""})
        return out

    g = collect(g_verdicts)
    k = collect(k_verdicts)
    print(f"Goedel P12 PASSes: {len(g)}")
    print(f"Kimina P12 PASSes: {len(k)}")

    def histogram(samples):
        counter = Counter()
        scores = []
        details_by_strategy = {}
        for s in samples:
            strat, score, det = classify(s["proof"])
            counter[strat] += 1
            if score is not None:
                scores.append(score)
            details_by_strategy.setdefault(strat, []).append({"attempt": s["attempt"], **det})
        return counter, scores, details_by_strategy

    g_counter, g_scores, g_details = histogram(g)
    k_counter, k_scores, k_details = histogram(k)

    print(f"\n{'Strategy':30} {'Bidirec':>9} {'Goedel':>8} {'Kimina':>8}")
    print("-" * 60)
    bidirec_grade = {
        "S1_named_decomp": 1.0,
        "S2_single_sq_nonneg": 0.6,
        "S2b_two_candidates": 0.4,
        "S3_shotgun_nlinarith": 0.2,
        "S4_positivity": 0.0,
        "S4_polyrith": 0.0,
        "S5_other": None,
    }
    all_strats = sorted(set(list(g_counter.keys()) + list(k_counter.keys())),
                       key=lambda s: -(bidirec_grade.get(s) or -1))
    for s in all_strats:
        gr = bidirec_grade.get(s)
        gr_str = f"{gr:.2f}" if gr is not None else "?"
        print(f"{s:30} {gr_str:>9} {g_counter.get(s, 0):>8} {k_counter.get(s, 0):>8}")
    import statistics as st
    print("-" * 60)
    print(f"{'Mean bidirec score':30} {' ':>9} "
          f"{(st.mean(g_scores) if g_scores else 0):>8.2f} "
          f"{(st.mean(k_scores) if k_scores else 0):>8.2f}")
    print(f"{'PASS count':30} {' ':>9} {len(g):>8} {len(k):>8}")

    # Investigate S2 candidates
    print("\n=== S2 / S3 candidate inspection (Kimina) ===")
    for strat in ["S3_shotgun_nlinarith", "S2_single_sq_nonneg", "S2b_two_candidates"]:
        items = k_details.get(strat, [])[:3]
        if not items: continue
        print(f"\n{strat}:")
        for it in items:
            print(f"  attempt {it['attempt']}: candidates = {it.get('nlinarith_candidates', [])}")
            print(f"    has_corrige_square: {it.get('has_corrige_square')}")

    # Save
    out = {
        "goedel": {"counter": dict(g_counter), "n_pass": len(g),
                   "mean_bidirec": (sum(g_scores)/len(g_scores)) if g_scores else None},
        "kimina": {"counter": dict(k_counter), "n_pass": len(k),
                   "mean_bidirec": (sum(k_scores)/len(k_scores)) if k_scores else None},
        "bidirec_grade": bidirec_grade,
        "details_kimina": k_details,
        "details_goedel": g_details,
    }
    json.dump(out, open(OUT, "w"), indent=1, default=str)
    print(f"\nWrote {OUT}")


if __name__ == "__main__":
    main()
