#!/usr/bin/env python3
"""Start a proof: copy a program's Specs.lean to programs/<task>/Proofs/spec_<n>.lean.

    python3 tools/new_proof.py <task> <n>               # to prove spec_<n>
    python3 tools/new_proof.py <task> <n> --negation    # to refute it: prove spec_<n>_neg

Then replace that theorem's `sorry` with a proof (add any lemmas you need before it) and run
    python3 tools/check.py proof programs/<task>/Proofs/spec_<n>.lean
The other theorems in the file may keep their `sorry`; only your theorem is checked.
"""
import argparse, json, os, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("task"); ap.add_argument("n", type=int)
    ap.add_argument("--negation", action="store_true")
    ap.add_argument("--name", help="how you want to be credited (default: your git user.name)")
    a = ap.parse_args()
    prog = ROOT / "programs" / a.task
    if not (prog / "specs.json").exists():
        sys.exit(f"no program {a.task} with theorems")
    ids = {s["id"] for s in json.loads((prog / "specs.json").read_text())}
    if a.n not in ids:
        sys.exit(f"{a.task} has theorems spec_1 .. spec_{max(ids)}")
    name = f"spec_{a.n}" + ("_neg" if a.negation else "")
    dst = prog / "Proofs" / f"{name}.lean"
    if dst.exists():
        sys.exit(f"{dst.relative_to(ROOT)} already exists")
    who = a.name or subprocess.run(["git", "config", "user.name"], capture_output=True, text=True).stdout.strip() or "your name"
    src = (prog / "Specs.lean").read_text()
    imports = "".join(re.findall(r"^import [^\n]+\n", src, re.M))
    body = re.sub(r"^import [^\n]+\n", "", src, flags=re.M).lstrip("\n")
    dst.parent.mkdir(exist_ok=True)
    # so that an editor opened on the program finds the shared packages instead of fetching its own
    link = prog / ".lake" / "packages"
    if not link.exists() and not link.is_symlink():
        link.parent.mkdir(exist_ok=True); link.symlink_to(os.path.relpath(ROOT / ".lake" / "packages", link.parent))
    dst.write_text(f"{imports}\n/-\nProof of `{name}` ({a.task}).\nContributor: {who}\n-/\n\n{body}")
    rel = dst.relative_to(ROOT)
    print(f"wrote {rel}\nprove `{name}` there, then run:\n  python3 tools/check.py proof {rel}")


if __name__ == "__main__":
    main()
