#!/usr/bin/env python3
"""Check every proof that has no result for its current file and program in
status/verified.json (new proofs, edited proofs, or proofs whose program changed), and record
the results. Runs on the main branch, which is trusted; a failed proof is not re-checked until
it or its program changes.

    python3 tools/verify_all.py [--limit-minutes 240]
"""
import argparse, json, sys, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check

ROOT = check.ROOT


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--limit-minutes", type=float, default=240)
    a = ap.parse_args(); t0 = time.time()
    st = json.loads(check.STATUS.read_text()) if check.STATUS.exists() else {}
    files = sorted(f.relative_to(ROOT).as_posix() for f in ROOT.glob("programs/*/Proofs/spec_*.lean"))
    todo = [f for f in files if check.PROOF_RE.fullmatch(f) and not check.current(st.get(f), f)]
    print(len(files), "proofs,", len(todo), "to check", flush=True)
    bad = 0
    for f in todo:
        if time.time() - t0 > 60 * a.limit_minutes:
            print("time limit reached; the rest is checked on the next run"); break
        r = check.check_proof(f, record=True)
        print(("ok    " if r["ok"] else "FAILED"), f, r.get("seconds", ""), flush=True)
        bad += not r["ok"]
    st = json.loads(check.STATUS.read_text()) if check.STATUS.exists() else {}
    st = {k: v for k, v in st.items() if (ROOT / k).exists()}          # proofs that were removed
    check.STATUS.write_text(json.dumps(dict(sorted(st.items())), indent=1) + "\n")
    print(bad, "failed")


if __name__ == "__main__":
    main()
