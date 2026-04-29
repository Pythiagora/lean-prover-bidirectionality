# /// script
# requires-python = ">=3.11"
# ///
"""Per-PASS bidirectionality-vs-corrigé score, aggregated.

Score per PASS = (# preserved-kind moves matched) / (# preserved-kind moves total)
Hidden / detour matches do NOT count toward bidirectionality.

Outputs per-(theorem, prover):
  - n_pass
  - mean bidirec score (0..1)
  - shotgun rate (fraction of PASSes hitting any 'hidden' or 'detour' pattern)
  - cross-prover divergence per theorem
"""
import json, re
from pathlib import Path
from collections import defaultdict
import statistics as st

ROOT = Path("/home/dxwoo/Code/AITP/rerun4")
SCORES_OUT = Path("/tmp/bidirec_scores_aggregate.json")

# Reuse MOVES + helpers from corrige_moves.py
import sys
sys.path.insert(0, '/tmp')
from corrige_moves import MOVES, load_arm, score_pass


def per_pass_bidirec(proof: str, moves: list) -> tuple[float, bool]:
    """(score, any_hidden_or_detour) for one PASS proof."""
    if not moves:
        return None, False
    pres = [e for e in moves if len(e) == 2]
    hide = [e for e in moves if len(e) == 3]
    if not pres:
        return None, any(score_pass(proof, [e])[e[0]] in ("hidden", "detour") for e in hide)
    sp = score_pass(proof, moves)
    n_pres = sum(1 for e in pres if sp[e[0]] == "preserved")
    score = n_pres / len(pres)
    has_hidden = any(sp[e[0]] in ("hidden", "detour") for e in hide)
    return score, has_hidden


def main():
    g = load_arm("goedel")
    k = load_arm("kimina")

    table = {}
    for tid in sorted(set(list(g.keys()) + list(k.keys()))):
        moves = MOVES.get(tid, [])
        if not moves:
            continue
        row = {"moves": [{"name": e[0], "kind": e[2] if len(e) == 3 else "preserved"} for e in moves]}
        for arm_name, arm in [("goedel", g), ("kimina", k)]:
            samples = arm.get(tid, [])
            scores, hidden_flags = [], []
            for s in samples:
                sc, hh = per_pass_bidirec(s["proof"], moves)
                if sc is not None:
                    scores.append(sc)
                hidden_flags.append(hh)
            if scores:
                row[arm_name] = {
                    "n_pass": len(samples),
                    "n_scored": len(scores),
                    "mean_bidirec": round(st.mean(scores), 3),
                    "shotgun_rate": round(sum(hidden_flags) / max(len(hidden_flags), 1), 3),
                }
            else:
                row[arm_name] = {"n_pass": len(samples), "n_scored": 0,
                                 "mean_bidirec": None, "shotgun_rate": None}
        table[tid] = row

    json.dump(table, open(SCORES_OUT, "w"), indent=1)

    # Print summary
    print(f"\n{'Theorem':35} {'#G':>4} {'BidG':>5} {'ShotG':>6}    {'#K':>4} {'BidK':>5} {'ShotK':>6}    {'BidGap':>7}")
    print("-" * 100)
    g_avgs, k_avgs = [], []
    for tid, row in table.items():
        gn = row.get('goedel', {}); kn = row.get('kimina', {})
        gb = gn.get('mean_bidirec'); kb = kn.get('mean_bidirec')
        gp = gn.get('n_pass', 0); kp = kn.get('n_pass', 0)
        gs = gn.get('shotgun_rate'); ks = kn.get('shotgun_rate')
        if gb is not None: g_avgs.append(gb)
        if kb is not None: k_avgs.append(kb)
        gap = (gb - kb) if (gb is not None and kb is not None) else None
        gb_str = f"{gb:.2f}" if gb is not None else "—"
        kb_str = f"{kb:.2f}" if kb is not None else "—"
        gs_str = f"{gs:.2f}" if gs is not None else "—"
        ks_str = f"{ks:.2f}" if ks is not None else "—"
        gap_str = f"{gap:+.2f}" if gap is not None else "—"
        print(f"{tid:35} {gp:>4} {gb_str:>5} {gs_str:>6}    {kp:>4} {kb_str:>5} {ks_str:>6}    {gap_str:>7}")

    print("-" * 100)
    if g_avgs and k_avgs:
        print(f"{'OVERALL MEAN BIDIREC':35} {sum(p['goedel']['n_pass'] for p in table.values() if p.get('goedel',{}).get('mean_bidirec') is not None):>4} "
              f"{st.mean(g_avgs):.2f}                "
              f"{sum(p['kimina']['n_pass'] for p in table.values() if p.get('kimina',{}).get('mean_bidirec') is not None):>4} "
              f"{st.mean(k_avgs):.2f}")
    print(f"\nWrote {SCORES_OUT}")


if __name__ == "__main__":
    main()
