"""Where Lean declarations are defined, so the site can link names to their source.

index_aeneas(dir) maps fully qualified names declared in the Aeneas Lean library to
"path#Lline" (relative to backends/lean). local_defs(text) finds the definitions of one file.
"""
import re
from pathlib import Path

DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:public|private|protected|noncomputable|partial|unsafe|nonrec|meta)[ \t]+)*"
                  r"(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)[ \t]+([^\s:(\[{]+)")
NS = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:public|noncomputable|private)[ \t]+)*(namespace|section|end)\b[ \t]*([^\s]*)")
CTOR = re.compile(r"^[ \t]*\|[ \t]*([A-Za-z_][\w']*)")


def decls(text):
    """Yield (qualified name, line) for the declarations of a Lean file, constructors included."""
    stack, last_inductive = [], None
    for i, line in enumerate(text.splitlines(), 1):
        m = NS.match(line)
        if m:
            kind, name = m.groups()
            if kind == "namespace":
                stack.append(("ns", name))
            elif kind == "section":
                stack.append(("sec", name))
            elif stack:
                stack.pop()
            last_inductive = None
            continue
        m = DECL.match(line)
        if m:
            kind, name = m.groups()
            if kind == "instance" and (name.startswith(":") or not re.match(r"[A-Za-z_]", name)):
                continue
            full = ".".join([n for k, n in stack if k == "ns"] + [name.lstrip("_root_.")])
            yield full, i
            last_inductive = full if kind in ("inductive", "structure", "class") else None
            continue
        m = CTOR.match(line)
        if m and last_inductive:
            yield f"{last_inductive}.{m.group(1)}", i


def index_aeneas(root):
    root = Path(root); out = {}
    for f in sorted(root.glob("Aeneas/**/*.lean")):
        rel = f.relative_to(root).as_posix()
        for name, line in decls(f.read_text(errors="replace")):
            out.setdefault(name, f"{rel}#L{line}")
    return out
