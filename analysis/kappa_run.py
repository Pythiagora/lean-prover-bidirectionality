#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["httpx", "scikit-learn"]
# ///
"""
Compute Cohen's kappa for per-PASS bidirectionality classification.

1. Parse per-theorem INDEX.md files to extract original (a)/(b)/(c) labels per PASS.
2. Stratified-sample 50 PASSes across theorems with mixed (a)/(b) splits.
3. Send each script + theorem-specific criterion to an independent classifier (Gemini 3.1 Pro
   via OpenRouter — different model lineage from Sonnet that did the original).
4. Compare original vs independent labels; compute Cohen's kappa.
"""
import os, re, json, random, asyncio, sys
from pathlib import Path
from collections import defaultdict
import httpx
from sklearn.metrics import cohen_kappa_score, confusion_matrix

PER_THEOREM = Path("/home/dxwoo/Code/AITP/rerun4/seed_robustness/per_theorem")
OUT = Path("/tmp/kappa_results.json")
N_SAMPLE = 50
SEED = 4242
MODEL = "google/gemini-3.1-pro-preview"
CONCURRENCY = 6

random.seed(SEED)


def parse_index(theorem_dir: Path):
    """
    Return:
      criterion: str (the '## Classification criteria' or '## Statement and corrigé' block)
      labels: dict {attempt_filename: 'a'|'b'|'c'}
    Parsing strategy: under each '### {arm} — (a/b/c) ...' heading, collect any
    occurrence of `goedel_attNN.md` / `kimina_attNN.md` mentioned in the section.
    """
    idx = theorem_dir / "INDEX.md"
    if not idx.exists():
        return None, {}
    text = idx.read_text()

    # Criterion block: from '## Classification criteria' (or '## Statement') up to next '##'
    crit_match = re.search(r"##\s*(Classification criteria|Statement[^#]*)\n(.*?)(?=\n##\s)", text, re.S)
    criterion = crit_match.group(0).strip() if crit_match else ""

    labels = {}
    # Find sections like '### Goedel — (a) route-preserving (X/Y)' and capture content until next '### ' or '## '
    section_re = re.compile(r"^###\s+(Goedel|Kimina)\s+[—–-]+\s+\((a|b|c)\)[^\n]*\n(.*?)(?=^###\s|^##\s|\Z)", re.M | re.S)
    for m in section_re.finditer(text):
        arm = m.group(1).lower()
        cls = m.group(2)
        body = m.group(3)
        # Extract any 'goedel_attNN.md' or 'kimina_attNN.md' mentions
        for fm in re.finditer(r"\b(goedel|kimina)_att(\d+)\.md\b", body):
            fname = f"{fm.group(1)}_att{fm.group(2).zfill(2)}.md"
            # Only assign if the arm matches the section
            if fm.group(1) == arm:
                labels[fname] = cls
        # Also try patterns like 'att10, att22, att27' under arm-specific headings
        for am in re.finditer(r"\batt(\d+)\b", body):
            fname = f"{arm}_att{am.group(1).zfill(2)}.md"
            # Don't overwrite explicit *.md mentions
            labels.setdefault(fname, cls)
    return criterion, labels


def extract_lean_script(att_file: Path) -> str:
    text = att_file.read_text()
    # Find last ```lean4 block
    blocks = re.findall(r"```lean4?\s*\n(.*?)```", text, re.S)
    if not blocks:
        return ""
    return blocks[-1].strip()


def collect():
    """Walk all theorems, collect (theorem, file, label, script, criterion) tuples."""
    rows = []
    for tdir in sorted(PER_THEOREM.iterdir()):
        if not tdir.is_dir() or tdir.name.startswith("_"):
            continue
        criterion, labels = parse_index(tdir)
        if not labels:
            continue
        for fname, cls in labels.items():
            ap = tdir / fname
            if not ap.exists():
                continue
            script = extract_lean_script(ap)
            if len(script) < 30:  # skip empty/garbage
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


def stratified_sample(rows, n=50, seed=SEED):
    """
    Sample stratified across (theorem, label). Prefer theorems with both (a) and (b).
    """
    by_theorem = defaultdict(list)
    for r in rows:
        by_theorem[r["theorem"]].append(r)

    # Rank theorems by min((a), (b)) count — high min => well-mixed
    mixed = []
    for t, rs in by_theorem.items():
        n_a = sum(1 for r in rs if r["orig"] == "a")
        n_b = sum(1 for r in rs if r["orig"] == "b")
        mixed.append((min(n_a, n_b), n_a, n_b, t))
    mixed.sort(reverse=True)

    rng = random.Random(seed)
    sample = []
    # Allocate ~5 (a) + ~5 (b) per top theorem until we hit n
    for min_ab, n_a, n_b, t in mixed:
        if len(sample) >= n:
            break
        rs = by_theorem[t]
        a_pool = [r for r in rs if r["orig"] == "a"]
        b_pool = [r for r in rs if r["orig"] == "b"]
        take_a = min(5, len(a_pool), n - len(sample))
        sample.extend(rng.sample(a_pool, take_a))
        take_b = min(5, len(b_pool), n - len(sample))
        sample.extend(rng.sample(b_pool, take_b))

    return sample[:n]


CLASSIFIER_PROMPT = """You are classifying a Lean 4 tactic script against a per-theorem bidirectionality criterion.

The criterion has THREE classes:
- (a) ROUTE-PRESERVING: the script names the corrigé's key moves as explicit `have` statements with the corrigé's witness term, or uses named Mathlib lemmas that correspond to the corrigé's named moves. The proof structure is recoverable from the script: a reader who knows the corrigé can locate each move.
- (b) LOWER-ABSTRACTION: the corrigé's witnesses are present (e.g., the right square in a `nlinarith` hint list, or the right lemma applied without intermediate naming) but the proof structure is absorbed into bounded automation (one `nlinarith [...]` with hint lists, `<;> field_simp <;> ring_nf` cascades, etc.). The corrigé is recoverable as ingredients but not as steps.
- (c) OPAQUE: shotgun `nlinarith` with no recognizable corrigé witness, `polyrith`, raw `aesop`/`fun_prop` chains, or output where the corrigé route is genuinely absent.

THEOREM-SPECIFIC CRITERION:
{criterion}

LEAN SCRIPT:
```lean4
{script}
```

Output a single JSON object on one line with NO additional text:
{{"class": "a"|"b"|"c", "reason": "one short sentence"}}"""


async def classify_one(client: httpx.AsyncClient, row: dict, api_key: str, sem: asyncio.Semaphore):
    async with sem:
        prompt = CLASSIFIER_PROMPT.format(
            criterion=row["criterion"][:3000],
            script=row["script"][:8000],
        )
        try:
            resp = await client.post(
                "https://openrouter.ai/api/v1/chat/completions",
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                json={
                    "model": MODEL,
                    "max_tokens": 256,
                    "temperature": 0.0,
                    "messages": [{"role": "user", "content": prompt}],
                },
                timeout=180.0,
            )
            resp.raise_for_status()
            data = resp.json()
            content = data["choices"][0]["message"]["content"] or ""
            m = re.search(r'\{.*?"class"\s*:\s*"([abc])".*?\}', content, re.S)
            if not m:
                return {**row, "indep": "?", "indep_raw": content[:200]}
            return {**row, "indep": m.group(1), "indep_raw": content[:200]}
        except Exception as e:
            return {**row, "indep": "ERROR", "indep_raw": str(e)[:200]}


async def main():
    api_key = os.environ.get("OPENROUTER_API_KEY")
    if not api_key:
        print("ERROR: OPENROUTER_API_KEY not set"); sys.exit(1)

    rows = collect()
    print(f"Collected {len(rows)} labeled PASSes across {len(set(r['theorem'] for r in rows))} theorems")
    by_label = defaultdict(int)
    for r in rows: by_label[r["orig"]] += 1
    print(f"Original label distribution: {dict(by_label)}")

    sample = stratified_sample(rows, n=N_SAMPLE)
    print(f"Sampled {len(sample)} PASSes; per-label split:")
    by_label_s = defaultdict(int)
    for r in sample: by_label_s[r["orig"]] += 1
    print(f"  {dict(by_label_s)}")
    print(f"Theorems sampled: {sorted(set(r['theorem'] for r in sample))}")

    sem = asyncio.Semaphore(CONCURRENCY)
    async with httpx.AsyncClient() as client:
        tasks = [classify_one(client, r, api_key, sem) for r in sample]
        results = []
        for i, coro in enumerate(asyncio.as_completed(tasks), 1):
            r = await coro
            print(f"[{i}/{len(sample)}] {r['theorem']:30s} {r['file']:20s} orig={r['orig']} indep={r['indep']}")
            results.append(r)

    # Compute kappa, dropping ERROR/?
    valid = [r for r in results if r["indep"] in ("a", "b", "c")]
    y1 = [r["orig"] for r in valid]
    y2 = [r["indep"] for r in valid]
    if not valid:
        print("No valid pairs!"); return
    kappa = cohen_kappa_score(y1, y2)
    print(f"\n--- RESULTS ---")
    print(f"Valid pairs: {len(valid)} / {len(sample)}")
    print(f"Cohen's kappa: {kappa:.3f}")
    print(f"Raw agreement: {sum(a == b for a, b in zip(y1, y2))}/{len(valid)} = {sum(a==b for a,b in zip(y1,y2))/len(valid)*100:.1f}%")
    labels = sorted(set(y1) | set(y2))
    cm = confusion_matrix(y1, y2, labels=labels)
    print("\nConfusion matrix (rows=original, cols=independent):")
    print("     " + "  ".join(f"{l:>4}" for l in labels))
    for i, l in enumerate(labels):
        print(f"{l:>4} " + "  ".join(f"{cm[i,j]:>4}" for j in range(len(labels))))

    OUT.write_text(json.dumps({
        "model": MODEL,
        "n_sample": len(sample),
        "n_valid": len(valid),
        "kappa": kappa,
        "labels": labels,
        "confusion_matrix": cm.tolist(),
        "raw_agreement_pct": sum(a==b for a,b in zip(y1,y2))/len(valid)*100,
        "results": results,
    }, indent=2))
    print(f"\nResults saved: {OUT}")


if __name__ == "__main__":
    asyncio.run(main())
