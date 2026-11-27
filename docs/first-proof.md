# Your first proof

This walks through one complete proof, from an open theorem to a merged pull request. The example
is `spec_2` of `calculate-delayed-arrival-time`: the program never fails on valid inputs.

## 1. The program and the theorem

The Rust program (`programs/calculate-delayed-arrival-time/solution.rs`):

```rust
pub fn find_delayed_arrival_time(arrivalTime: i64, delayedTime: i64) -> i64 {
    (arrivalTime + delayedTime) % 24
}
```

Its Lean translation by Aeneas (`Aegis/FindDelayedArrivalTime/Code/Funs.lean`):

```lean
def find_delayed_arrival_time
  (arrivalTime : Std.I64) (delayedTime : Std.I64) : Result Std.I64 := do
  let i ← arrivalTime + delayedTime
  i % 24#i64
```

Both the addition and the remainder can fail in Lean, because Rust would panic on an overflow or a
division by zero. The theorem (`Specs.lean`) says that on valid inputs neither happens:

```lean
theorem spec_2 (arrivalTime delayedTime : Std.I64)
    (h_arrival_lo : 1 ≤ arrivalTime.val) (h_arrival_hi : arrivalTime.val < 24)
    (h_delayed_lo : 1 ≤ delayedTime.val) (h_delayed_hi : delayedTime.val ≤ 24) :
    ∃ r, find_delayed_arrival_time arrivalTime delayedTime = ok r := by
  sorry
```

## 2. Set up once

On Linux, with elan, Python 3 and bwrap:

```bash
git clone https://github.com/<you>/leetcode-rust-lean     # your fork
cd leetcode-rust-lean
lake exe cache get && lake build Aeneas                   # Mathlib from its cache, Aeneas built once
```

## 3. Start the proof

```bash
python3 tools/new_proof.py calculate-delayed-arrival-time 2 --name "Your Name" --org "Your Lab"
```

This copies `Specs.lean` to `programs/calculate-delayed-arrival-time/Proofs/spec_2.lean` with your
name in the header, and links the shared packages so your editor works in that folder. Open the
folder `programs/calculate-delayed-arrival-time` in VS Code with the Lean extension.

## 4. Prove it

Replace the `sorry` of `spec_2` (and only that one) with a proof. Aeneas' `step` tactic walks
through a `Result` program one operation at a time, using the bounds in the hypotheses to show
that each operation succeeds. Here is the proof that is in the repository:

```lean
  -- A total specification (no `fail`, no `div`) yields a successful result.
  have key : ∀ {α : Type} {m : Result α} {p : Aeneas.Std.WP.Post α},
      Aeneas.Std.WP.spec m p → ∃ v, m = ok v := by
    intro α m p h
    cases m using Result.cases with
    | ret v => exact ⟨v, rfl⟩
    | vis e k => cases e; exact absurd h (by simp)
    | div => exact absurd h (by simp)
  refine key (p := fun _ => True) ?_
  unfold find_delayed_arrival_time
  step
  step
```

The two `step`s are the addition and the remainder. You may add definitions and lemmas before the
theorem; you may not change its statement, use `sorry`, or use axioms other than `propext`,
`Quot.sound` and `Classical.choice`.

## 5. Check it

```bash
python3 tools/check.py proof programs/calculate-delayed-arrival-time/Proofs/spec_2.lean
```

prints `"ok": true` when `lake comparator` accepts the proof: it rebuilds the challenge and your
file in a sandbox, checks that the statement is unchanged and the axioms are allowed, and replays
the proof in Lean's kernel and in nanoda. This is exactly what CI does.

## 6. Open a pull request

Commit only the new file under `Proofs/` and open a pull request. CI runs the same check against
the program as it is on the main branch; when it passes, the proof is merged, the theorem turns
green on the site, and the points go to the names in your header on the leaderboard.

To refute a theorem instead, start with `--negation` and prove `spec_<n>_neg`.
