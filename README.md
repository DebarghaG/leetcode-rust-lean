# LeetCode Rust-to-Lean: proofs

Theorem provers are now very good at competition mathematics, and the benchmarks for it are
close to saturated. Proving that real code is correct is a different and much harder problem,
and it is the one that matters for software.

This repository collects proofs of the theorems in the
[LeetCode Rust-to-Lean](https://huggingface.co/datasets/Debargha/leetcode-rust-lean) dataset:
2,126 programs and 24,617 theorems about them. Each program is a Rust solution to a LeetCode
problem that passes every test case, translated to Lean 4 by [Aeneas](https://github.com/AeneasVerif/aeneas). The Lean code is
the program itself, with machine integers, overflow checks, loops and panics, not a clean
mathematical model of it. Each theorem states one property of one program, in natural language
and in Lean 4.

Progress is shown on the [project site](https://debarghag.github.io/leetcode-rust-lean/).

## The task

Prove a theorem, or prove its negation. Every theorem comes with its negation already stated, so
a refutation always targets the same statement.

A proof may add any definitions and lemmas it needs, and imports from the same Lean, Mathlib and
Aeneas versions. It may not change the statement. It must not use `sorry`, and it may only use
the standard axioms `propext`, `Quot.sound` and `Classical.choice`. This rules out
`native_decide`, which adds an axiom of its own.

The check is mechanical. Lean's built-in `lake comparator` compares the proof with the original
statement, checks the axioms, and replays the proof in the Lean kernel and in nanoda, an independent
kernel bundled with Lean. Nothing is graded by hand or by a model.

## Layout

```
programs/<task>/
  program.json          the problem: statement, difficulty, tags, signatures
  solution.rs           the Rust program
  tests.json            its test cases
  Aegis/<Problem>/Code/ the Lean translation (Types.lean, Funs.lean, FunsExternal.lean)
  Specs.lean            every theorem spec_<n> and its negation spec_<n>_neg, all with `sorry`
  specs.json            the theorems in natural language
  Proofs/spec_<n>.lean  a proof of spec_<n> (or spec_<n>_neg.lean, a refutation)
tools/                  new_proof.py, check.py, verify_all.py, build_site.py
site/                   the project site
```

Each program is its own small Lake project. The programs share one copy of Mathlib and Aeneas,
fetched once at the repository root.

## Proving a theorem

You need Linux (`lake comparator` runs only there; on macOS or Windows use a Linux container or
WSL 2), [elan](https://github.com/leanprover/elan), `python3` and `bwrap` (Bubblewrap). On
Ubuntu 23.10 and later, bwrap needs `sudo sysctl kernel.apparmor_restrict_unprivileged_userns=0`.

```bash
lake exe cache get && lake build Aeneas             # once: fetch Mathlib and Aeneas, build Aeneas
python3 tools/new_proof.py sum-of-square-numbers 2  # copies Specs.lean to programs/<task>/Proofs/spec_2.lean
# replace the sorry of spec_2 with a proof; add lemmas before it if you need them
python3 tools/check.py proof programs/sum-of-square-numbers/Proofs/spec_2.lean
```

`new_proof.py` also links the shared packages into the program, so an editor opened on
`programs/<task>` works without fetching anything. The last command prints `"ok": true` when
`lake comparator` accepts the proof. To refute a
theorem, run `new_proof.py` with `--negation` and prove `spec_<n>_neg`. Then open a pull request;
CI runs the same check. See [CONTRIBUTING.md](CONTRIBUTING.md) for specifications and programs.

## Credits

The first 52 proofs were found by an automated prover during a pilot run and are credited to
`by-eureka`. Proofs record their contributor in their header.

## Citation

This is an unofficial reproduction of the methodology of
[*Scaling Lean Theorem Proving for Real-World Code Verification*](https://arxiv.org/abs/2610.38174),
made by the paper's first author. If you use it, please cite the paper:

```bibtex
@misc{ganguly2026scalingleantheoremproving,
      title={Scaling Lean Theorem Proving for Real-World Code Verification}, 
      author={Debargha Ganguly and Divya Raghunathan and Dejan Jovanović and Vikash Singh and Soonho Kong and Aaron Tomb and Aman Goel and Ferhat Erata and Sam Bayless},
      year={2026},
      eprint={2610.38174},
      archivePrefix={arXiv},
      primaryClass={cs.CL},
      url={https://arxiv.org/abs/2610.38174}, 
}
```

MIT license.
