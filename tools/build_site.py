#!/usr/bin/env python3
"""Build the data for the progress site (site/data/) from the repository.

    python3 tools/build_site.py

A theorem counts as proved (or refuted) only if status/verified.json records a passing
`lake comparator` check of its proof file, for the current proof file and the current program
(by hash of the proof, and of everything the proof is checked against). Writes site/data/index.json (one entry per program) and
site/data/p/<task>.json (everything the program page shows).
"""
import hashlib, json, re, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import check
import source_index

PINS = dict(lean="v4.36.0", mathlib="fc4f59e577feb1a4956671bc04ac18aaaf8cd842",
            aeneas="0c19cd5bff9298565362c6ca9c4f48a29033a0e9", charon="5a2a17bd")
OPENS = ("", "Aeneas.", "Aeneas.Std.", "Aeneas.Std.Result.")       # namespaces the Lean files open
OUT = ROOT / "site" / "data"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()[:16]


def header(path, field):
    """A `Field: value` line of the proof file's header comment, or None."""
    m = re.search(rf"^{field}:[ \t]*(.+?)[ \t]*$", path.read_text()[:3000], re.M)
    return m.group(1).strip() if m and m.group(1).strip() else None


POINTS = {"Easy": 1, "Medium": 2, "Hard": 3}     # a main theorem counts three times


def points(difficulty, main):
    return POINTS[difficulty] * (3 if main else 1)


def contributor(path):
    m = header(path, "Contributor")
    if m:
        return m
    try:
        return subprocess.run(["git", "log", "--diff-filter=A", "--format=%an", "--", str(path)], cwd=ROOT,
                              capture_output=True, text=True).stdout.split("\n")[-2].strip() or "unknown"
    except IndexError:
        return "unknown"


def main():
    verified = json.loads((ROOT / "status" / "verified.json").read_text()) if (ROOT / "status" / "verified.json").exists() else {}
    (OUT / "p").mkdir(parents=True, exist_ok=True)
    index, contributors, totals, flat, recent, mains, credits = [], {}, dict(theorems=0, proved=0, refuted=0), [], [], [], []
    for prog in sorted((ROOT / "programs").iterdir()):
        meta = json.loads((prog / "program.json").read_text())
        specs = json.loads((prog / "specs.json").read_text()) if (prog / "specs.json").exists() else []
        thms = []
        for s in specs:
            st, proof = ("superseded" if s.get("superseded_by") else "open"), None
            for kind, suffix in (("proved", ""), ("refuted", "_neg")):
                f = prog / "Proofs" / f"spec_{s['id']}{suffix}.lean"
                rel = str(f.relative_to(ROOT))
                v = verified.get(rel)
                if f.exists() and v and v.get("ok") and check.current(v, rel):
                    who = contributor(f)
                    org, system = header(f, "Organization"), header(f, "System")
                    st = "conflict" if st in ("proved", "refuted") else kind
                    when = v.get("first_verified") or v.get("checked") or ""
                    proof = dict(file=rel, by=who, org=org, system=system, checked=when, text=f.read_text())
                    pts = points(meta["difficulty"], s["main"])
                    c = contributors.setdefault(who, dict(name=who, proved=0, refuted=0))
                    c[kind] += 1
                    credits.append(dict(t=prog.name, id=s["id"], kind=kind, by=who, org=org, system=system,
                                        date=when, points=pts, main=bool(s["main"]), d=meta["difficulty"][0]))
                    recent.append(dict(t=prog.name, id=s["id"], kind=kind, by=who, checked=when,
                                       lines=proof["text"].count("\n"), main=s["main"], cat=s["category"]))
            thms.append(dict(s, status=st, proof=proof))
            if s["main"] and st in ("proved", "refuted"):
                txt = (prog / "Specs.lean").read_text()
                m = re.search(rf"^[ \t]*theorem spec_{s['id']}\b.*?(?=:=\s*by\s*\n\s*sorry)", txt, re.M | re.S)
                stmt = "\n".join(l[2:] if l.startswith("  ") else l for l in m.group(0).splitlines()) if m else ""
                mains.append(dict(t=prog.name, id=s["id"], status=st, by=proof["by"], stmt=stmt.rstrip(),
                                  lines=proof["text"].count("\n")))
            flat.append([prog.name, s["id"], s["category"][:2], int(s["main"]), st[0], s["statement"][:400],
                         proof["by"] if proof else ""])
            totals["theorems"] += st != "superseded"
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
                          st="".join({"open": "o", "proved": "p", "refuted": "r", "conflict": "x", "superseded": "s"}[x["status"]] for x in thms)))
    first = [r for r in flat if r[4] == "o" and r[2] in ("no", "bo", "ed")
             and json.loads((ROOT / "programs" / r[0] / "program.json").read_text())["difficulty"] == "Easy"]
    first = sorted(first, key=lambda r: hashlib.sha256(f"{r[0]}{r[1]}".encode()).hexdigest())[:12]
    recent.sort(key=lambda r: (r["checked"], r["t"], r["id"]), reverse=True)
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    data = dict(built=time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime()), commit=commit, totals=totals, recent=recent[:200], first=first, mains=mains,
                programs=index, contributors=sorted(contributors.values(), key=lambda c: -(c["proved"] + c["refuted"])))
    # links from names in the Lean code to their definitions in the Aeneas library
    aen_root = check.PACKAGES / "aeneas" / "backends" / "lean"
    links = {}
    if aen_root.exists():
        ix = source_index.index_aeneas(aen_root)
        toks = set()
        for f in (OUT / "p").glob("*.json"):
            toks |= set(re.findall(r"[A-Za-z_][\w'.]*[\w']", f.read_text()))
        for t in toks:
            for o in OPENS:
                if o + t in ix:
                    links[t] = ix[o + t]; break
    (OUT / "links.json").write_text(json.dumps(links, separators=(",", ":")))
    data["pins"] = PINS
    orgs = json.loads((ROOT / "organizations.json").read_text()) if (ROOT / "organizations.json").exists() else {}
    data["verified_orgs"] = orgs.get("organizations", {})
    data["credits"] = sorted(credits, key=lambda c: (c["date"], c["t"], c["id"]))     # one per resolved theorem
    (OUT / "index.json").write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")))
    done = totals["proved"] + totals["refuted"]
    (OUT / "badge.json").write_text(json.dumps(dict(schemaVersion=1, label="theorems resolved",
                                                     message=f"{done:,} / {totals['theorems']:,}", color="2e9e5b")))
    (OUT / "progress.json").write_text(json.dumps(dict(built=data["built"], commit=commit, **totals,
                                                        main_resolved=len(mains), teams=len({c["org"] or c["by"] for c in credits})), indent=1))
    (OUT / "theorems.json").write_text(json.dumps(flat, ensure_ascii=False, separators=(",", ":")))
    print(f"{len(index)} programs, {totals['theorems']} theorems, {totals['proved']} proved, {totals['refuted']} refuted")


if __name__ == "__main__":
    main()
