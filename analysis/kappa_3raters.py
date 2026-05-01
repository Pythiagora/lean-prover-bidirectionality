#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["httpx", "scikit-learn", "numpy"]
# ///
"""
Add GPT-5.5 as third classifier; compute pair-wise and 3-way agreement.
Reuses existing Gemini results from kappa_full78.json.
"""
import os, re, json, asyncio, sys, time
from pathlib import Path
from collections import Counter
import httpx, numpy as np
from sklearn.metrics import cohen_kappa_score

PER_THEOREM = Path("/home/dxwoo/Code/AITP/rerun4/seed_robustness/per_theorem")
GEMINI_RESULTS = Path("/home/dxwoo/Code/lean-prover-bidirectionality/analysis/kappa_full78.json")
OUT = Path("/home/dxwoo/Code/lean-prover-bidirectionality/analysis/kappa_3raters.json")
MODEL = "openai/gpt-5.5"
MODEL_LABEL = "GPT-5.5"
CONCURRENCY = 8


def parse_index(theorem_dir: Path):
    idx = theorem_dir / "INDEX.md"
    if not idx.exists():
        return "", {}
    text = idx.read_text()
    crit_match = re.search(r"##\s*(Classification criteria|Statement[^#]*)\n(.*?)(?=\n##\s)", text, re.S)
    criterion = crit_match.group(0).strip() if crit_match else ""
    labels = {}
    section_re = re.compile(r"^###\s+(Goedel|Kimina)\s+[—–-]+\s+\((a|b|c)\)[^\n]*\n(.*?)(?=^###\s|^##\s|\Z)", re.M | re.S)
    for m in section_re.finditer(text):
        arm = m.group(1).lower(); cls = m.group(2); body = m.group(3)
        for fm in re.finditer(r"\b(goedel|kimina)_att(\d+)\.md\b", body):
            if fm.group(1) == arm:
                labels[f"{fm.group(1)}_att{fm.group(2).zfill(2)}.md"] = cls
        for am in re.finditer(r"\batt(\d+)\b", body):
            labels.setdefault(f"{arm}_att{am.group(1).zfill(2)}.md", cls)
    return criterion, labels


def collect():
    rows = []
    for tdir in sorted(PER_THEOREM.iterdir()):
        if not tdir.is_dir() or tdir.name.startswith("_"): continue
        criterion, labels = parse_index(tdir)
        for fname, cls in labels.items():
            ap = tdir / fname
            if not ap.exists(): continue
            text = ap.read_text()
            blocks = re.findall(r"```lean4?\s*\n(.*?)```", text, re.S)
            script = blocks[-1].strip() if blocks else ""
            if len(script) < 30: continue
            rows.append({"theorem": tdir.name, "file": fname, "arm": fname.split("_")[0],
                         "orig": cls, "script": script, "criterion": criterion})
    return rows


PROMPT = """Classify a Lean 4 tactic script against a per-theorem bidirectionality criterion.

THREE CLASSES:
- (a) ROUTE-PRESERVING: the corrigé's exact witness term appears inside an explicit `have` declaration OR inside an `apply <named_lemma>` invocation. The script's structure mirrors the corrigé's named moves.
- (b) LOWER-ABSTRACTION: the corrigé's witness is present BUT only inside a hint list of a closing automation tactic (e.g. `nlinarith [sq_nonneg (witness), ...]`, `<;> field_simp <;> ring_nf`). Witness present as INGREDIENT, not as STEP.
- (c) OPAQUE: shotgun `nlinarith`, `polyrith`, `aesop`, `fun_prop` chain with no recognizable corrigé witness, OR proof-by-coincidence.

STRICT BOUNDARY RULE: a witness inside `nlinarith [...]` hint syntax counts as (b), regardless of whether it matches the corrigé exactly. Only an explicit `have h : ... := by ...` with the witness term, or `apply <named_lemma>` with a corrigé-aligned lemma name, qualifies as (a).

THEOREM-SPECIFIC CRITERION:
{criterion}

LEAN SCRIPT:
```lean4
{script}
```

Output ONLY this JSON on one line, nothing else: {{"class":"a"}} OR {{"class":"b"}} OR {{"class":"c"}}"""


async def classify_one(client, row, api_key, sem):
    async with sem:
        prompt = PROMPT.format(criterion=row["criterion"][:3000], script=row["script"][:8000])
        try:
            resp = await client.post(
                "https://openrouter.ai/api/v1/chat/completions",
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                json={"model": MODEL, "max_tokens": 256, "temperature": 0.0,
                      "messages": [{"role": "user", "content": prompt}]},
                timeout=240.0,
            )
            resp.raise_for_status()
            d = resp.json()
            content = d["choices"][0]["message"]["content"] or ""
            usage = d.get("usage", {})
            m = re.search(r'"class"\s*:\s*"?([abc])"?', content)
            return {**row, "gpt": m.group(1) if m else "?",
                    "raw": content[:200], "in_tok": usage.get("prompt_tokens", 0),
                    "out_tok": usage.get("completion_tokens", 0)}
        except Exception as e:
            return {**row, "gpt": "ERROR", "raw": str(e)[:200], "in_tok": 0, "out_tok": 0}


def fleiss_kappa(matrix):
    n_sub, n_cat = matrix.shape
    n_raters = matrix.sum(axis=1)[0]
    p_j = matrix.sum(axis=0) / (n_sub * n_raters)
    P_e = (p_j ** 2).sum()
    P_i = (matrix * (matrix - 1)).sum(axis=1) / (n_raters * (n_raters - 1))
    return (P_i.mean() - P_e) / (1 - P_e)


async def main():
    api_key = os.environ.get("OPENROUTER_API_KEY")
    if not api_key: print("ERROR: OPENROUTER_API_KEY not set"); sys.exit(1)

    # Load Gemini results
    gem = json.loads(GEMINI_RESULTS.read_text())
    gemini_label = {f"{r['theorem']}/{r['file']}": r["indep"] for r in gem["results"]}

    rows = collect()
    print(f"Collected {len(rows)} PASSes; calling GPT-5.5 ({len(rows)} requests)\n")

    sem = asyncio.Semaphore(CONCURRENCY)
    async with httpx.AsyncClient() as client:
        tasks = [classify_one(client, r, api_key, sem) for r in rows]
        t0 = time.time()
        results = []
        for i, coro in enumerate(asyncio.as_completed(tasks), 1):
            r = await coro
            results.append(r)
            if i % 20 == 0 or i == len(rows):
                ok = sum(1 for x in results if x["gpt"] in ("a","b","c"))
                print(f"  [{i:>3}/{len(rows)}] {time.time()-t0:.0f}s, {ok} OK")

    # Build 3-rater matrix
    sonnet = []; gemini = []; gpt = []; rows_used = []
    for r in results:
        fid = f"{r['theorem']}/{r['file']}"
        gem_l = gemini_label.get(fid, "?")
        gpt_l = r["gpt"]
        if gem_l in ("a","b","c") and gpt_l in ("a","b","c"):
            sonnet.append(r["orig"]); gemini.append(gem_l); gpt.append(gpt_l); rows_used.append(r)

    n = len(rows_used)
    print(f"\n=== n={n} valid 3-way pairs ===")

    def k(a, b, label):
        agr = sum(x==y for x,y in zip(a,b))
        kap = cohen_kappa_score(a, b)
        print(f"  {label:30s}  agree={agr}/{n} ({agr/n*100:.1f}%)  kappa={kap:.3f}")
        return kap, agr

    print("\nPair-wise Cohen's kappa:")
    k_sg, _ = k(sonnet, gemini, "Sonnet vs Gemini-3.1-Pro")
    k_so, _ = k(sonnet, gpt, "Sonnet vs GPT-5.5")
    k_go, _ = k(gemini, gpt, "Gemini-3.1-Pro vs GPT-5.5")

    # 3-way majority vote vs Sonnet
    print("\nMajority-vote (Gemini + GPT-5.5 + Sonnet) — majority of 3 raters per PASS:")
    maj_pairs = []
    for s, g, o in zip(sonnet, gemini, gpt):
        votes = Counter([s, g, o]).most_common(1)[0][0]
        maj_pairs.append((s, votes))
    y1 = [p[0] for p in maj_pairs]; y2 = [p[1] for p in maj_pairs]
    k_maj = cohen_kappa_score(y1, y2)
    agr = sum(x==y for x,y in zip(y1,y2))
    print(f"  Sonnet vs majority             agree={agr}/{n} ({agr/n*100:.1f}%)  kappa={k_maj:.3f}")

    # 2-of-3 council = Gemini + GPT, majority vs Sonnet
    print("\n2-LLM council (Gemini + GPT, both must agree else either):")
    council_pairs = []
    for s, g, o in zip(sonnet, gemini, gpt):
        if g == o:
            council = g  # unanimous
        else:
            council = g  # tie-break: prefer Gemini (the prior independent rater)
        council_pairs.append((s, council))
    y1 = [p[0] for p in council_pairs]; y2 = [p[1] for p in council_pairs]
    k_council = cohen_kappa_score(y1, y2)
    agr = sum(x==y for x,y in zip(y1,y2))
    print(f"  Sonnet vs LLM-council          agree={agr}/{n} ({agr/n*100:.1f}%)  kappa={k_council:.3f}")

    # Fleiss kappa across 3 raters
    cats = ["a","b","c"]
    matrix = np.zeros((n, 3), dtype=int)
    for i, lbls in enumerate(zip(sonnet, gemini, gpt)):
        for l in lbls:
            matrix[i, cats.index(l)] += 1
    k_fleiss = fleiss_kappa(matrix)
    print(f"\nFleiss' kappa (3 raters)         kappa={k_fleiss:.3f}")

    # Excluding P16
    print("\n--- Excluding P16.IV.3 ---")
    keep = [i for i, r in enumerate(rows_used) if "P16" not in r["theorem"]]
    s2, g2, o2 = [sonnet[i] for i in keep], [gemini[i] for i in keep], [gpt[i] for i in keep]
    n2 = len(keep)
    print(f"  n={n2}")
    k(s2, g2, "Sonnet vs Gemini")
    k(s2, o2, "Sonnet vs GPT-5.5")
    k(g2, o2, "Gemini vs GPT-5.5")
    maj2 = []
    for s, g, o in zip(s2, g2, o2):
        v = Counter([s, g, o]).most_common(1)[0][0]
        maj2.append((s, v))
    y1 = [p[0] for p in maj2]; y2 = [p[1] for p in maj2]
    k_m2 = cohen_kappa_score(y1, y2)
    agr = sum(x==y for x,y in zip(y1,y2))
    print(f"  Sonnet vs majority(3)          agree={agr}/{n2} ({agr/n2*100:.1f}%)  kappa={k_m2:.3f}")

    # Cost
    in_tok = sum(r.get("in_tok", 0) for r in results)
    out_tok = sum(r.get("out_tok", 0) for r in results)
    cost = (in_tok * 5.00 + out_tok * 30.00) / 1_000_000
    print(f"\nGPT-5.5 cost: ${cost:.4f} ({in_tok} in + {out_tok} out tokens)")

    OUT.write_text(json.dumps({
        "n": n, "n_excl_p16": n2,
        "kappa": {
            "sonnet_gemini": k_sg, "sonnet_gpt": k_so, "gemini_gpt": k_go,
            "sonnet_vs_majority3": k_maj, "sonnet_vs_council2": k_council,
            "fleiss_3raters": k_fleiss, "sonnet_vs_majority3_excl_p16": k_m2,
        },
        "cost_usd": cost,
        "labels": {f"{r['theorem']}/{r['file']}": {"sonnet": r['orig'], "gemini": gemini_label.get(f"{r['theorem']}/{r['file']}", "?"), "gpt": r["gpt"]}
                   for r in rows_used},
    }, indent=2))
    print(f"\nSaved: {OUT}")


if __name__ == "__main__":
    asyncio.run(main())
