#!/usr/bin/env python3
"""Check contributions. The same script runs locally and in CI.

    python3 tools/check.py proof programs/<task>/Proofs/spec_3.lean     # a proof (or spec_3_neg.lean)
    python3 tools/check.py specs programs/<task> [--base origin/main]   # a program's Specs.lean
    python3 tools/check.py changed --base origin/main                   # whatever a branch changed

A proof is accepted when `lake comparator` accepts it against the program's Specs.lean: same
statement, no sorry, only the axioms propext, Quot.sound and Classical.choice, checked by the
Lean kernel. Needs elan (Lean 4.36.0), bwrap, and the shared packages in .lake/packages at the
repository root (run `lake update && lake exe cache get` there once).
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKAGES = Path(os.environ.get("LEAN_PACKAGES", ROOT / ".lake" / "packages")).resolve()
STATUS = ROOT / "status" / "verified.json"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()[:16]


def in_program(prog, cmd, timeout=3600):
    """Run `cmd` in the program's directory with the shared packages mounted read-only at
    programs/<task>/.lake/packages (Comparator resolves dependencies inside the project)."""
    (prog / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
    full = ["bwrap", "--die-with-parent", "--bind", "/", "/", "--dev-bind", "/dev", "/dev",
            "--ro-bind", str(PACKAGES), str((prog / ".lake" / "packages").resolve()),
            "--chdir", str(prog.resolve()), "--", "bash", "-c", cmd]
    try:
        p = subprocess.run(full, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        return 124, (e.stdout or b"").decode(errors="replace") + "\nTIMEOUT"


def specs_of(prog):
    return json.loads((prog / "specs.json").read_text())


def namespace(prog):
    return re.search(r"^[ \t]*namespace (\S+)", (prog / "Specs.lean").read_text(), re.M).group(1)


def check_proof(path, record=False):
    path = Path(path).resolve(); prog = path.parent.parent
    m = re.fullmatch(r"(spec_(\d+))(_neg)?\.lean", path.name)
    res = dict(file=str(path.relative_to(ROOT)), ok=False)
    if path.parent.name != "Proofs" or not m:
        res["error"] = "a proof lives at programs/<task>/Proofs/spec_<n>.lean or spec_<n>_neg.lean"
        return res
    ids = {s["id"] for s in specs_of(prog)}
    if int(m.group(2)) not in ids:
        res["error"] = f"{prog.name} has no theorem spec_{m.group(2)}"; return res
    thm = f"{namespace(prog)}.{m.group(1)}{m.group(3) or ''}"
    res.update(task=prog.name, theorem=thm, kind="refutation" if m.group(3) else "proof")
    cfg = dict(challenge_module="Specs", solution_module=f"Proofs.{path.stem}",
               theorem_names=[thm], permitted_axioms=AXIOMS)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, dir="/tmp") as f:
        json.dump(cfg, f); cfg_path = f.name
    t0 = time.time()
    rc, log = in_program(prog, f"lake build Specs Proofs.{path.stem} && lake comparator --config {cfg_path}")
    os.unlink(cfg_path)
    res.update(ok=(rc == 0 and "Your solution is okay!" in log), seconds=round(time.time() - t0),
               proof_sha=sha(path), specs_sha=sha(prog / "Specs.lean"))
    if not res["ok"]:
        errs = [l for l in log.splitlines() if "error" in l.lower()]
        res["error"] = "\n".join(errs[-8:]) or log[-2000:]
    if record:
        record_result(res)
    return res


def record_result(res):
    STATUS.parent.mkdir(exist_ok=True)
    st = json.loads(STATUS.read_text()) if STATUS.exists() else {}
    st[res["file"]] = {k: res.get(k) for k in ("task", "theorem", "kind", "ok", "proof_sha", "specs_sha")}
    st[res["file"]]["checked"] = time.strftime("%Y-%m-%d")
    STATUS.write_text(json.dumps(dict(sorted(st.items())), indent=1) + "\n")


def theorem_texts(src):
    """name -> statement text (from `theorem` to `:=`), for spec_n and spec_n_neg."""
    out = {}
    for m in re.finditer(r"^[ \t]*theorem (spec_\d+(?:_neg)?)\b(.*?):=", src, re.M | re.S):
        out[m.group(1)] = " ".join(m.group(2).split())
    return out


def check_specs(prog, base=None):
    prog = Path(prog).resolve(); res = dict(task=prog.name, ok=False, problems=[])
    src = (prog / "Specs.lean").read_text(); sj = specs_of(prog)
    thms = theorem_texts(src)
    names = [n for n in re.findall(r"^[ \t]*theorem (spec_\d+)\b", src, re.M)]
    ids = [s["id"] for s in sj]
    if names != [f"spec_{i}" for i in ids]:
        res["problems"].append(f"theorems in Specs.lean {names} do not match specs.json ids {ids}")
    if ids != list(range(1, len(ids) + 1)):
        res["problems"].append("specs.json ids must be 1..n in order")
    if sum(1 for s in sj if s.get("main")) != 1:
        res["problems"].append("exactly one theorem must be marked main")
    for n in names:
        if f"{n}_neg" not in thms:
            res["problems"].append(f"{n} has no negation {n}_neg")
        if not re.search(rf"-/\s*\n[ \t]*theorem {n}\b", src):
            res["problems"].append(f"{n} has no docstring with its natural-language statement")
    if base:
        try:
            old = subprocess.run(["git", "show", f"{base}:{(prog / 'Specs.lean').relative_to(ROOT)}"],
                                 cwd=ROOT, capture_output=True, text=True, check=True).stdout
            for n, text in theorem_texts(old).items():
                if thms.get(n) != text:
                    res["problems"].append(f"{n} was changed or removed; released statements are frozen "
                                           "(add a new theorem instead, and mark the old one superseded)")
        except subprocess.CalledProcessError:
            pass                                  # a new program
    rc, log = in_program(prog, "lake build Specs")
    errs = [l for l in log.splitlines() if re.search(r"\berror\b", l)]
    sorries = len(re.findall(r"declaration uses .sorry.", log))
    if rc != 0 or errs:
        res["problems"].append("Specs.lean does not build:\n" + "\n".join(errs[:8]))
    elif sorries != 2 * len(names):
        res["problems"].append(f"expected {2 * len(names)} sorries (each theorem and its negation), "
                               f"found {sorries}: `sorry` is only allowed as a theorem proof")
    res["ok"] = not res["problems"]
    return res


def changed(base):
    diff = subprocess.run(["git", "diff", "--name-only", f"{base}...HEAD"], cwd=ROOT,
                          capture_output=True, text=True, check=True).stdout.split()
    results, ok = [], True
    proofs = sorted({f for f in diff if re.fullmatch(r"programs/[^/]+/Proofs/spec_\d+(_neg)?\.lean", f)
                     and (ROOT / f).exists()})
    spec_progs = sorted({f.split("/")[1] for f in diff if re.fullmatch(r"programs/[^/]+/(Specs\.lean|specs\.json)", f)})
    code = sorted({f.split("/")[1] for f in diff if re.match(r"programs/[^/]+/(Aegis/|solution\.rs|tests\.json)", f)})
    for p in spec_progs:
        r = check_specs(ROOT / "programs" / p, base); results.append(("specs", r)); ok &= r["ok"]
    for f in proofs:
        r = check_proof(ROOT / f); results.append(("proof", r)); ok &= r["ok"]
    for p in code:
        results.append(("program", dict(task=p, ok=None, note="program code changed: needs maintainer "
                                        "review and re-extraction (CONTRIBUTING.md)")))
    return ok, results


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("what", choices=["proof", "specs", "changed"])
    ap.add_argument("path", nargs="?")
    ap.add_argument("--base", default=None)
    ap.add_argument("--record", action="store_true", help="write the result to status/verified.json")
    a = ap.parse_args()
    if a.what == "proof":
        r = check_proof(a.path, a.record); print(json.dumps(r, indent=1)); sys.exit(0 if r["ok"] else 1)
    if a.what == "specs":
        r = check_specs(a.path, a.base); print(json.dumps(r, indent=1)); sys.exit(0 if r["ok"] else 1)
    ok, results = changed(a.base or "origin/main")
    for kind, r in results:
        print(f"[{kind}] {json.dumps(r)}")
    if not results:
        print("nothing to check")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
