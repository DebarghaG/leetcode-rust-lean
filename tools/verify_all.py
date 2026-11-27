#!/usr/bin/env python3
"""Check every proof whose current file has no passing record in status/verified.json
(new proofs, edited proofs, or proofs whose Specs.lean changed), and record the results.

    python3 tools/verify_all.py
"""
import json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check

ROOT = check.ROOT


def main():
    st = json.loads(check.STATUS.read_text()) if check.STATUS.exists() else {}
    todo = []
    for f in sorted(ROOT.glob("programs/*/Proofs/spec_*.lean")):
        rel = str(f.relative_to(ROOT)); v = st.get(rel)
        if not (v and v.get("ok") and v.get("proof_sha") == check.sha(f)
                and v.get("specs_sha") == check.sha(f.parent.parent / "Specs.lean")):
            todo.append(f)
    print(len(todo), "proofs to check", flush=True)
    bad = 0
    for f in todo:
        r = check.check_proof(f, record=True)
        print(("ok    " if r["ok"] else "FAILED"), r["file"], r.get("seconds", ""), flush=True)
        bad += not r["ok"]
    # drop records of proofs that no longer exist
    st = json.loads(check.STATUS.read_text()) if check.STATUS.exists() else {}
    st = {k: v for k, v in st.items() if (ROOT / k).exists()}
    check.STATUS.write_text(json.dumps(dict(sorted(st.items())), indent=1) + "\n")
    print(bad, "failed")


if __name__ == "__main__":
    main()
