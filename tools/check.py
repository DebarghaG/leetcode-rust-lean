#!/usr/bin/env python3
"""Check contributions. The same script runs locally and in CI.

    python3 tools/check.py proof programs/<task>/Proofs/spec_3.lean     # a proof (or spec_3_neg.lean)
    python3 tools/check.py specs programs/<task> [--base origin/main]   # a program's Specs.lean
    python3 tools/check.py changed --base origin/main                   # what a branch changes

A proof is checked in a fresh copy of its program, taken from a trusted commit (`--trusted`,
default HEAD; in CI the base of the pull request), with only the proof file added. Nothing is
built before `lake comparator`, which builds the challenge and then the proof, each in its own
sandbox, and accepts the proof only if it states the same theorem, uses no `sorry` and no axiom
besides propext, Quot.sound and Classical.choice, and is accepted by Lean's kernel and by every
independent checker bundled with Lean (`--paranoid`). The whole run is
wrapped in an outer sandbox: read-only file system, no network, private /tmp.

Needs Linux, elan, bwrap, and the shared packages built once at the repository root:
    lake exe cache get && lake build Aeneas
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path

# CHECK_ROOT lets CI run the trusted checker (from the base branch) on a pull request's checkout
ROOT = Path(os.environ.get("CHECK_ROOT", Path(__file__).resolve().parent.parent)).resolve()
PACKAGES = Path(os.environ.get("LEAN_PACKAGES", ROOT / ".lake" / "packages")).resolve()
ELAN_HOME = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
STATUS = Path(os.environ.get("CHECK_STATUS", ROOT / "status" / "verified.json"))
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PROOF_RE = re.compile(r"programs/([^/]+)/Proofs/spec_(\d+)(_neg)?\.lean")


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else Path(data).read_bytes()).hexdigest()[:16]


def git(*args, **kw):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=kw.pop("text", True), check=True, **kw).stdout


def program_files(task, ref=None):
    """{relative path: bytes} of everything a proof of this program is checked against:
    the program without its Proofs/, plus the root toolchain and manifest."""
    out = {}
    if ref:
        for line in git("ls-tree", "-r", "--name-only", ref, f"programs/{task}").splitlines():
            if f"programs/{task}/Proofs/" not in line:
                out[line] = git("show", f"{ref}:{line}", text=False)
        for f in ("lean-toolchain", "lake-manifest.json"):
            out[f] = git("show", f"{ref}:{f}", text=False)
    else:
        prog = ROOT / "programs" / task
        for p in sorted(prog.rglob("*")):
            rel = p.relative_to(ROOT).as_posix()
            if p.is_file() and "/Proofs/" not in rel and "/.lake/" not in rel:
                out[rel] = p.read_bytes()
        for f in ("lean-toolchain", "lake-manifest.json"):
            out[f] = (ROOT / f).read_bytes()
    if not any(k.endswith("/Specs.lean") for k in out):
        raise FileNotFoundError(f"programs/{task} has no Specs.lean" + (f" at {ref}" if ref else ""))
    return out


def tree_sha(task, ref=None):
    files = program_files(task, ref)
    return sha(b"".join(k.encode() + b"\0" + sha(v).encode() + b"\n" for k, v in sorted(files.items())))


def workspace(task, ref=None):
    """A fresh directory holding the trusted program, ready for one check."""
    ws = Path(tempfile.mkdtemp(prefix="check-", dir=os.environ.get("CHECK_TMP")))
    for rel, data in program_files(task, ref).items():
        if rel.startswith("programs/"):
            dst = ws / "p" / rel.split("/", 2)[2]
            dst.parent.mkdir(parents=True, exist_ok=True); dst.write_bytes(data)
    (ws / "p" / "Proofs").mkdir(exist_ok=True)
    (ws / "p" / ".lake" / "packages").mkdir(parents=True)
    (ws / "home").mkdir()
    return ws


def toolchain_bin(project):
    """The bin directory of the project's Lean toolchain, resolved outside the sandbox. Inside it,
    lake and lean are run directly, without elan, which would want to write its own files."""
    out = subprocess.run(["elan", "which", "lake"], cwd=project, capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError("cannot find the toolchain with elan: " + out.stderr.strip())
    return str(Path(out.stdout.strip()).resolve().parent)


def sandboxed(ws, cmd, timeout=3600, packages_writable=False):
    """Run cmd in ws/p: read-only file system except ws, shared packages read-only, no network."""
    tc = toolchain_bin(ws / "p")
    if cmd and cmd[0] == "lake":
        cmd = [str(Path(tc) / "lake"), *cmd[1:]]
    full = ["bwrap", "--die-with-parent", "--ro-bind", "/", "/", "--dev-bind", "/dev", "/dev", "--proc", "/proc",
            "--tmpfs", "/tmp", "--bind", str(ws), str(ws),
            "--bind" if packages_writable else "--ro-bind", str(PACKAGES), str(ws / "p" / ".lake" / "packages"),
            "--unshare-net", "--setenv", "HOME", str(ws / "home"), "--setenv", "PATH", f"{tc}:/usr/local/bin:/usr/bin:/bin",
            "--unsetenv", "ELAN_HOME", "--unsetenv", "ELAN_TOOLCHAIN",
            "--chdir", str(ws / "p"), "--", *cmd]
    try:
        p = subprocess.run(full, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        return 124, ((e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")) + "\nTIMEOUT"


def comparator(ws, challenge, solution, names, axioms=AXIOMS, timeout=3600):
    cfg = ws / "comparator.json"            # outside the project directory
    cfg.write_text(json.dumps(dict(challenge_module=challenge, solution_module=solution,
                                   theorem_names=names, permitted_axioms=axioms)))
    # --paranoid: besides Lean's kernel, every independent checker bundled with Lean must accept
    rc, log = sandboxed(ws, ["lake", "comparator", "--config", str(cfg), "--paranoid"], timeout)
    return rc == 0 and "Your solution is okay!" in log, log


def namespace_of(specs_text):
    return re.search(r"^[ \t]*namespace (\S+)", specs_text, re.M).group(1)


def check_proof(path, trusted=None, record=False, proof_bytes=None):
    """path: programs/<task>/Proofs/spec_<n>[_neg].lean. The proof text is read from the working
    tree (or proof_bytes); the program it is checked against comes from `trusted` (a git ref) or,
    without one, from the working tree."""
    rel = Path(path).resolve().relative_to(ROOT).as_posix() if Path(path).is_absolute() or Path(path).exists() else str(path)
    m = PROOF_RE.fullmatch(rel)
    res = dict(file=rel, ok=False)
    if not m:
        res["error"] = "a proof lives at programs/<task>/Proofs/spec_<n>.lean or spec_<n>_neg.lean"; return res
    task, n, neg = m.group(1), int(m.group(2)), bool(m.group(3))
    try:
        ws = workspace(task, trusted)
    except (FileNotFoundError, subprocess.CalledProcessError) as e:
        res["error"] = f"no such program with theorems: {e}"; return res
    try:
        specs = json.loads((ws / "p" / "specs.json").read_text())
        if n not in {s["id"] for s in specs}:
            res["error"] = f"{task} has no theorem spec_{n}"; return res
        thm = f"{namespace_of((ws / 'p' / 'Specs.lean').read_text())}.spec_{n}{'_neg' if neg else ''}"
        data = proof_bytes if proof_bytes is not None else (ROOT / rel).read_bytes()
        (ws / "p" / "Proofs" / Path(rel).name).write_bytes(data)
        t0 = time.time()
        ok, log = comparator(ws, "Specs", f"Proofs.{Path(rel).stem}", [thm])
        res.update(task=task, theorem=thm, kind="refutation" if neg else "proof", ok=ok,
                   seconds=round(time.time() - t0), proof_sha=sha(data), tree_sha=tree_sha(task, trusted))
        if not ok:
            errs = [l for l in log.splitlines() if re.search(r"error|Illegal|mismatch|differ", l, re.I)]
            res["error"] = "\n".join(errs[-10:]) or log[-2000:]
            res["log"] = log[-6000:]                     # the full tail, for diagnosing the environment
    finally:
        shutil.rmtree(ws, ignore_errors=True)
    if record:
        record_result(res)
    return res


def record_result(res):
    STATUS.parent.mkdir(exist_ok=True)
    st = json.loads(STATUS.read_text()) if STATUS.exists() else {}
    old = st.get(res["file"], {})
    today = time.strftime("%Y-%m-%d")
    st[res["file"]] = {k: res.get(k) for k in ("task", "theorem", "kind", "ok", "proof_sha", "tree_sha")}
    st[res["file"]]["checked"] = today
    st[res["file"]]["first_verified"] = old.get("first_verified") if old.get("ok") and res["ok"] else (today if res["ok"] else None)
    STATUS.write_text(json.dumps(dict(sorted(st.items())), indent=1) + "\n")


def current(rec, proof_file):
    """Is a status record valid for the proof file and its program as they are now?"""
    task = PROOF_RE.fullmatch(proof_file).group(1)
    return (rec and rec.get("proof_sha") == sha(ROOT / proof_file) and rec.get("tree_sha") == tree_sha(task))


def warm(proof="programs/calculate-delayed-arrival-time/Proofs/spec_2.lean"):
    """Run one full `lake comparator --paranoid` check of a known proof while the shared packages
    are writable, so that Lake and Comparator write whatever they want there once (CI does this
    before it saves or uses its package cache). Every later check mounts the packages read-only."""
    task = PROOF_RE.fullmatch(proof).group(1)
    ws = workspace(task)
    try:
        specs = (ws / "p" / "Specs.lean").read_text()
        (ws / "p" / "Proofs" / Path(proof).name).write_bytes((ROOT / proof).read_bytes())
        thm = f"{namespace_of(specs)}.{Path(proof).stem}"
        cfg = ws / "comparator.json"
        cfg.write_text(json.dumps(dict(challenge_module="Specs", solution_module=f"Proofs.{Path(proof).stem}",
                                       theorem_names=[thm], permitted_axioms=AXIOMS)))
        # what Lake thinks is out of date, before anything is built (a dry run)
        for pkg in ("mathlib", "aeneas"):
            d = PACKAGES / pkg / ".lake" / "build"
            print(f"{pkg}: {sum(1 for _ in d.rglob('*.olean')) if d.exists() else 0} .olean files in {d}", flush=True)
        rc, log = sandboxed(ws, ["lake", "build", "--no-build", "Specs", f"Proofs.{Path(proof).stem}"])
        print("dry run:", rc, "\n" + "\n".join(log.splitlines()[-25:]), flush=True)
        stale = sorted(set(re.findall(r"Building ([\w.']+)", log)) - set(re.findall(r"Building ((?:Aegis|Specs|Proofs)[\w.']*)", log)))
        if stale:
            print(f"{len(stale)} modules of the shared packages are out of date, e.g. {stale[:8]}; not rebuilding them here")
            return False
        rc, log = sandboxed(ws, ["lake", "comparator", "--config", str(cfg), "--paranoid"], packages_writable=True)
        print(log[-4000:]); return rc == 0 and "Your solution is okay!" in log
    finally:
        shutil.rmtree(ws, ignore_errors=True)


# ------------------------------------------------------------------ specifications

def theorem_headers(src):
    return re.findall(r"^[ \t]*theorem (spec_\d+(?:_neg)?)\b", src, re.M)


def check_specs(prog, base=None):
    """Structure of Specs.lean and specs.json, that it builds with `sorry` only as theorem
    proofs, and (with base) that every released theorem and negation states exactly what it
    stated at base: comparator, with the base file as challenge and sorryAx permitted."""
    prog = Path(prog).resolve(); task = prog.name
    res = dict(task=task, ok=False, problems=[])
    src = (prog / "Specs.lean").read_text(); sj = json.loads((prog / "specs.json").read_text())
    heads = theorem_headers(src)
    names = [h for h in heads if not h.endswith("_neg")]
    ids = [s["id"] for s in sj]
    if names != [f"spec_{i}" for i in ids]:
        res["problems"].append(f"theorems in Specs.lean {names} do not match specs.json ids {ids}")
    if ids != list(range(1, len(ids) + 1)):
        res["problems"].append("specs.json ids must be 1..n in order")
    if sum(1 for s in sj if s.get("main")) != 1:
        res["problems"].append("exactly one theorem must be marked main")
    for nm in names:
        if f"{nm}_neg" not in heads:
            res["problems"].append(f"{nm} has no negation {nm}_neg")
        if not re.search(rf"-/\s*\n[ \t]*theorem {nm}\b", src):
            res["problems"].append(f"{nm} has no docstring with its natural-language statement")
    ws = Path(tempfile.mkdtemp(prefix="specs-", dir=os.environ.get("CHECK_TMP")))
    try:
        shutil.copytree(prog, ws / "p", ignore=shutil.ignore_patterns(".lake", "Proofs"))
        (ws / "p" / "Proofs").mkdir(); (ws / "p" / ".lake" / "packages").mkdir(parents=True); (ws / "home").mkdir()
        shutil.copy(ROOT / "lean-toolchain", ws / "p" / "lean-toolchain")
        rc, log = sandboxed(ws, ["lake", "build", "Specs"])
        errs = [l for l in log.splitlines() if re.search(r"\berror\b", l)]
        sorries = len(re.findall(r"declaration uses .sorry.", log))
        if rc != 0 or errs:
            res["problems"].append("Specs.lean does not build:\n" + "\n".join(errs[:8]))
        elif sorries != len(heads):
            res["problems"].append(f"expected {len(heads)} sorries (one per theorem), found {sorries}: "
                                   "`sorry` is only allowed as a theorem proof")
        if base:
            try:
                old = git("show", f"{base}:programs/{task}/Specs.lean")
            except subprocess.CalledProcessError:
                old = None                                   # a new program
            if old is not None:
                old_names = theorem_headers(old)
                (ws / "p" / "Proofs" / "Base.lean").write_text(old)
                (ws / "p" / "Proofs" / "New.lean").write_text(src)
                ns = namespace_of(old)
                ok, log = comparator(ws, "Proofs.Base", "Proofs.New", [f"{ns}.{x}" for x in old_names],
                                     AXIOMS + ["sorryAx"])
                if not ok:
                    res["problems"].append("a released statement changed; released statements are frozen "
                                           "(add a new theorem instead):\n" + "\n".join(log.splitlines()[-6:]))
    finally:
        shutil.rmtree(ws, ignore_errors=True)
    res["ok"] = not res["problems"]
    return res


# ------------------------------------------------------------------ pull requests

def changed(base, allow_other=False):
    """What a branch may change without a maintainer: add proof files, or extend one program's
    Specs.lean and specs.json. Everything else needs the `maintainer-approved` label."""
    diff = [l.split("\t") for l in git("diff", "--name-status", "--no-renames", f"{base}...HEAD").splitlines()]
    results, problems = [], []
    added_proofs, spec_progs, other = [], set(), []
    for st, path in ((d[0], d[-1]) for d in diff):
        if PROOF_RE.fullmatch(path) and st == "A":
            added_proofs.append(path)
        elif re.fullmatch(r"programs/[^/]+/(Specs\.lean|specs\.json)", path) and st == "M":
            spec_progs.add(path.split("/")[1])
        else:
            other.append(f"{st} {path}")
    if other and not allow_other:
        problems.append("these changes need a maintainer (label `maintainer-approved`): " + ", ".join(other)
                        + ". A pull request may add proof files, or extend a program's specifications.")
    if spec_progs and added_proofs:
        problems.append("send proofs and specification changes in separate pull requests")
    for p in sorted(spec_progs):
        r = check_specs(ROOT / "programs" / p, base); results.append(("specs", r))
        if not r["ok"]: problems.append(f"specs of {p} fail")
    for f in sorted(added_proofs):
        # the program is taken from the base commit, never from the pull request
        r = check_proof(f, trusted=base); results.append(("proof", r))
        if not r["ok"]: problems.append(f"{f} is not accepted")
    return not problems, results, problems


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("what", choices=["proof", "specs", "changed", "warm"])
    ap.add_argument("path", nargs="?")
    ap.add_argument("--base", default=None, help="for specs/changed: the commit to compare against")
    ap.add_argument("--trusted", default=None, help="for proof: take the program from this commit")
    ap.add_argument("--allow-other", action="store_true", help="for changed: a maintainer approved other changes")
    ap.add_argument("--record", action="store_true", help="write the result to status/verified.json")
    a = ap.parse_args()
    if a.what == "proof":
        r = check_proof(a.path, a.trusted, a.record); print(json.dumps(r, indent=1)); sys.exit(0 if r["ok"] else 1)
    if a.what == "warm":
        sys.exit(0 if warm() else 1)
    if a.what == "specs":
        r = check_specs(a.path, a.base); print(json.dumps(r, indent=1)); sys.exit(0 if r["ok"] else 1)
    ok, results, problems = changed(a.base or "origin/main", a.allow_other)
    for kind, r in results:
        log = r.pop("log", None)
        print(f"[{kind}] {json.dumps(r)}")
        if log:
            print(f"----- comparator output for {r.get('file')} -----\n{log}\n-----")
    for p in problems:
        print("PROBLEM:", p)
    if not results and not problems:
        print("nothing to check")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
