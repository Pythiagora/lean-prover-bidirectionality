#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["httpx", "scikit-learn"]
# ///
"""
Cohen's kappa on all 78 INDEX-enumerated PASSes via OpenRouter Gemini 3.1 Pro.
Tightened prompt with explicit (a)/(b) boundary rule. max_tokens=512 to avoid truncation.
"""
import os, re, json, asyncio, sys
from pathlib import Path
from collections import defaultdict
import httpx
from sklearn.metrics import cohen_kappa_score, confusion_matrix

PER_THEOREM = Path("/home/dxwoo/Code/AITP/rerun4/seed_robustness/per_theorem")
OUT = Path("/home/dxwoo/Code/lean-prover-bidirectionality/analysis/kappa_full78.json")
MODEL = "google/gemini-3.1-pro-preview"
CONCURRENCY = 6


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
        arm = m.group(1).lower()
        cls = m.group(2)
        body = m.group(3)
        for fm in re.finditer(r"\b(goedel|kimina)_att(\d+)\.md\b", body):
            if fm.group(1) == arm:
                labels[f"{fm.group(1)}_att{fm.group(2).zfill(2)}.md"] = cls
        for am in re.finditer(r"\batt(\d+)\b", body):
            labels.setdefault(f"{arm}_att{am.group(1).zfill(2)}.md", cls)
    return criterion, labels


def extract_lean_script(att_file: Path) -> str:
    text = att_file.read_text()
    blocks = re.findall(r"```lean4?\s*\n(.*?)```", text, re.S)
    return blocks[-1].strip() if blocks else ""


def collect():
    rows = []
    for tdir in sorted(PER_THEOREM.iterdir()):
        if not tdir.is_dir() or tdir.name.startswith("_"):
            continue
        criterion, labels = parse_index(tdir)
        for fname, cls in labels.items():
            ap = tdir / fname
            if not ap.exists():
                continue
            script = extract_lean_script(ap)
            if len(script) < 30:
                continue
            rows.append({
                "theorem": tdir.name,
                "file": fname,
                "arm": fname.split("_")[0],
                "orig": cls,
                "script": script,
                "criterion": criterion,
            })
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
                json={
                    "model": MODEL,
                    "max_tokens": 512,
                    "temperature": 0.0,
                    "messages": [{"role": "user", "content": prompt}],
                },
                timeout=180.0,
            )
            resp.raise_for_status()
            content = resp.json()["choices"][0]["message"]["content"] or ""
            m = re.search(r'"class"\s*:\s*"?([abc])"?', content)
            return {**row, "indep": m.group(1) if m else "?", "indep_raw": content[:300]}
        except Exception as e:
            return {**row, "indep": "ERROR", "indep_raw": str(e)[:300]}


async def main():
    api_key = os.environ.get("OPENROUTER_API_KEY")
    if not api_key:
        print("ERROR: OPENROUTER_API_KEY not set"); sys.exit(1)

    rows = collect()
    print(f"Collected {len(rows)} labeled PASSes across {len(set(r['theorem'] for r in rows))} theorems")
    by_label = defaultdict(int)
    for r in rows: by_label[r["orig"]] += 1
    print(f"Original label dist: {dict(by_label)}")

    sem = asyncio.Semaphore(CONCURRENCY)
    async with httpx.AsyncClient() as client:
        tasks = [classify_one(client, r, api_key, sem) for r in rows]
        results = []
        for i, coro in enumerate(asyncio.as_completed(tasks), 1):
            r = await coro
            print(f"[{i:>3}/{len(rows)}] {r['theorem']:32s} {r['file']:22s} orig={r['orig']} indep={r['indep']}")
            results.append(r)

    valid = [r for r in results if r["indep"] in ("a","b","c")]
    y1 = [r["orig"] for r in valid]
    y2 = [r["indep"] for r in valid]
    if not valid:
        print("No valid pairs!"); return

    kappa = cohen_kappa_score(y1, y2)
    agree = sum(a==b for a,b in zip(y1,y2))
    print(f"\n=== RESULTS (n={len(valid)}/{len(rows)}) ===")
    print(f"Raw agreement: {agree}/{len(valid)} = {agree/len(valid)*100:.1f}%")
    print(f"Cohen's kappa: {kappa:.3f}")
    labels = sorted(set(y1) | set(y2))
    cm = confusion_matrix(y1, y2, labels=labels)
    print("\nConfusion matrix (rows=Sonnet original, cols=Gemini independent):")
    print("       " + "  ".join(f"{l:>4}" for l in labels))
    for i, l in enumerate(labels):
        print(f"  {l:>4} " + "  ".join(f"{cm[i,j]:>4}" for j in range(len(labels))))

    for arm in ("goedel","kimina"):
        a = [r for r in valid if r["arm"]==arm]
        if a:
            y1a = [r["orig"] for r in a]; y2a = [r["indep"] for r in a]
            ka = cohen_kappa_score(y1a, y2a) if len(set(y1a))>1 else float('nan')
            aa = sum(x==y for x,y in zip(y1a,y2a))
            print(f"  {arm}: n={len(a)}, agree={aa}/{len(a)}={aa/len(a)*100:.1f}%, kappa={ka:.3f}")

    disagree = [r for r in valid if r["orig"] != r["indep"]]
    print(f"\n{len(disagree)} disagreements:")
    for r in disagree:
        print(f"  {r['theorem']:32s} {r['file']:22s} {r['orig']}->{r['indep']}")

    OUT.write_text(json.dumps({
        "model": MODEL, "n_total": len(rows), "n_valid": len(valid),
        "kappa": kappa, "raw_agreement_pct": agree/len(valid)*100,
        "labels": labels, "confusion_matrix": cm.tolist(),
        "results": results,
    }, indent=2))
    print(f"\nSaved: {OUT}")


if __name__ == "__main__":
    asyncio.run(main())
