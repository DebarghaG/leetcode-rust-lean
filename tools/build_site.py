#!/usr/bin/env python3
"""Build the data for the progress site (site/data/) from the repository.

    python3 tools/build_site.py

A theorem counts as proved (or refuted) only if status/verified.json records a passing
`lake comparator` check of its proof file, for the current proof file and the current
Specs.lean (both by hash). Writes site/data/index.json (one entry per program) and
site/data/p/<task>.json (everything the program page shows).
"""
import hashlib, json, re, subprocess, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "site" / "data"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()[:16]


def contributor(path):
    m = re.search(r"^Contributor:\s*(.+)$", path.read_text(), re.M)
    if m:
        return m.group(1).strip()
    try:
        return subprocess.run(["git", "log", "--diff-filter=A", "--format=%an", "--", str(path)], cwd=ROOT,
                              capture_output=True, text=True).stdout.split("\n")[-2].strip() or "unknown"
    except IndexError:
        return "unknown"


def main():
    verified = json.loads((ROOT / "status" / "verified.json").read_text()) if (ROOT / "status" / "verified.json").exists() else {}
    (OUT / "p").mkdir(parents=True, exist_ok=True)
    index, contributors, totals, flat = [], {}, dict(theorems=0, proved=0, refuted=0), []
    for prog in sorted((ROOT / "programs").iterdir()):
        meta = json.loads((prog / "program.json").read_text())
        specs = json.loads((prog / "specs.json").read_text()) if (prog / "specs.json").exists() else []
        specs_sha = sha(prog / "Specs.lean") if specs else None
        thms = []
        for s in specs:
            st, proof = "open", None
            for kind, suffix in (("proved", ""), ("refuted", "_neg")):
                f = prog / "Proofs" / f"spec_{s['id']}{suffix}.lean"
                rel = str(f.relative_to(ROOT))
                v = verified.get(rel)
                if f.exists() and v and v.get("ok") and v.get("proof_sha") == sha(f) and v.get("specs_sha") == specs_sha:
                    who = contributor(f)
                    st = "conflict" if st != "open" else kind
                    proof = dict(file=rel, by=who, checked=v.get("checked"), text=f.read_text())
                    c = contributors.setdefault(who, dict(name=who, proved=0, refuted=0))
                    c[kind] += 1
            thms.append(dict(s, status=st, proof=proof))
            flat.append([prog.name, s["id"], s["category"][:2], int(s["main"]), st[0], s["statement"][:400],
                         proof["by"] if proof else ""])
            totals["theorems"] += 1
            if st in ("proved", "refuted"):
                totals[st] += 1
        code = prog / "Aegis" / meta["lean_function"].split(".")[1] / "Code"
        page = dict(meta, theorems=thms,
                    rust=(prog / "solution.rs").read_text(),
                    lean_funs=(code / "Funs.lean").read_text(),
                    lean_types=(code / "Types.lean").read_text(),
                    lean_funs_external=(code / "FunsExternal.lean").read_text() if (code / "FunsExternal.lean").exists() else "",
                    specs_file=(prog / "Specs.lean").read_text() if specs else "")
        (OUT / "p" / f"{prog.name}.json").write_text(json.dumps(page, ensure_ascii=False, separators=(",", ":")))
        index.append(dict(t=prog.name, q=meta["question_id"], d=meta["difficulty"][0], s=meta["split"][:2],
                          g=meta["tags"], m=next((x["id"] for x in specs if x["main"]), 0),
                          c="".join(x["category"][:2] for x in specs),
                          st="".join({"open": "o", "proved": "p", "refuted": "r", "conflict": "x"}[x["status"]] for x in thms)))
    data = dict(built=time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime()), totals=totals,
                programs=index, contributors=sorted(contributors.values(), key=lambda c: -(c["proved"] + c["refuted"])))
    (OUT / "index.json").write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")))
    (OUT / "theorems.json").write_text(json.dumps(flat, ensure_ascii=False, separators=(",", ":")))
    print(f"{len(index)} programs, {totals['theorems']} theorems, {totals['proved']} proved, {totals['refuted']} refuted")


if __name__ == "__main__":
    main()
