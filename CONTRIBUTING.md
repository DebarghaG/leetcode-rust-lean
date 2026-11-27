# Contributing

There are three kinds of contribution. Each comes in as a pull request, and CI checks it with
`tools/check.py`, the same script you can run locally.

## 1. Proofs

Prove a theorem, or refute it by proving its negation.

```bash
python3 tools/new_proof.py <task> <n> [--negation] [--name "Your Name"]
# edit programs/<task>/Proofs/spec_<n>.lean
python3 tools/check.py proof programs/<task>/Proofs/spec_<n>.lean
```

- One file per theorem: `Proofs/spec_<n>.lean` proves `spec_<n>`, and `Proofs/spec_<n>_neg.lean`
  proves `spec_<n>_neg`.
- The file starts as a copy of `Specs.lean`. Replace the `sorry` of your theorem with a proof.
  Add any definitions and lemmas you need before it. The other theorems may keep their `sorry`;
  only yours is checked, and your proof may not use them.
- Do not change the statement, the program, or the definitions the statement uses.
- Only the axioms `propext`, `Quot.sound` and `Classical.choice` are allowed. `native_decide` is
  not.
- The header's `Contributor:` line is how you are credited on the site.

A proof is accepted when `lake comparator` accepts it against the program's `Specs.lean`.

## 2. Specifications

Add a theorem to a program, or a better version of an existing one.

- Add `spec_<n+1>` at the end of the program's `Specs.lean`, with its natural-language
  statement as a docstring (`/-- ... Preconditions: ... -/`), and its negation `spec_<n+1>_neg`
  right after it, both with `sorry`. Add the same theorem to `specs.json`.
- The theorem must be about the program: it mentions the function and constrains its result.
  Helper notions are ordinary definitions, never `sorry`.
- Released statements are frozen, because proofs depend on them. To improve one, add a new
  theorem and give the old entry in `specs.json` a `"superseded_by": <n>` field.

```bash
python3 tools/check.py specs programs/<task> --base origin/main
```

checks that the file builds, that every theorem has its docstring and its negation, that the only
`sorry`s are theorem proofs, and that no released statement changed. A maintainer also reads the
new statement against its natural-language text.

## 3. Programs

Add a program for a LeetCode problem that is not covered yet, or fix a translation.

- `solution.rs` is safe Rust in the subset Aeneas translates (see the dataset card), and passes
  every test case in `tests.json` with `cargo test` in a debug build.
- The Lean code under `Aegis/` is the output of Charon `5a2a17bd` and Aeneas `0c19cd5b`,
  unchanged, apart from `FunsExternal.lean`, which holds models of the few library functions
  Aeneas cannot translate.
- A maintainer re-runs the extraction and the tests before merging. A fix to an existing
  program re-checks every proof about it.

## Reviews

Proofs are merged when CI passes. Specifications and programs also need a maintainer's review.
