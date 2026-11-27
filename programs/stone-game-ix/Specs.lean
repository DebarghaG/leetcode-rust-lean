import Aegis.StoneGameIx.Code.Funs

/-!
# Specifications of `Aegis.StoneGameIx.stone_game_ix`

LeetCode problem `stone-game-ix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.StoneGameIx (stone_game_ix)

namespace AegisSpec.StoneGameIx

def values (stones : Slice Std.I64) : List ℤ := stones.val.map (fun x => x.val)

def countResidue (stones : Slice Std.I64) (k : ℕ) : ℕ :=
  stones.val.countP (fun x => x.val % 3 = (k : ℤ))

def validInput (stones : Slice Std.I64) : Prop :=
  1 ≤ stones.val.length ∧ stones.val.length ≤ 100000 ∧
    ∀ (i : ℕ) (hi : i < stones.val.length),
      1 ≤ (stones.val[i]'hi).val ∧ (stones.val[i]'hi).val ≤ 10000

def natAbsDiff (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

def SameContent (stones stones' : Slice Std.I64) : Prop := (values stones).Perm (values stones')

def legalMove (n s r : ℕ) : Bool := decide (0 < n) && decide ((s + r) % 3 ≠ 0)

def outcome : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, _ => 1
  | f + 1, c0, c1, c2, s =>
    let successors : List ℕ :=
      (if legalMove c0 s 0 then [2 - outcome f (c0 - 1) c1 c2 s] else []) ++
      (if legalMove c1 s 1 then [2 - outcome f c0 (c1 - 1) c2 ((s + 1) % 3)] else []) ++
      (if legalMove c2 s 2 then [2 - outcome f c0 c1 (c2 - 1) ((s + 2) % 3)] else [])
    successors.foldl max 0

def firstPlayerWins (c0 c1 c2 : ℕ) : Bool := outcome (c0 + c1 + c2) c0 c1 c2 0 == 2

def winsByFirstRemoving (c0 c1 c2 k : ℕ) : Bool :=
  (k == 0 && legalMove c0 0 0 && outcome (c0 - 1 + c1 + c2) (c0 - 1) c1 c2 0 == 0) ||
  (k == 1 && legalMove c1 0 1 && outcome (c0 + (c1 - 1) + c2) c0 (c1 - 1) c2 1 == 0) ||
  (k == 2 && legalMove c2 0 2 && outcome (c0 + c1 + (c2 - 1)) c0 c1 (c2 - 1) 2 == 0)

/-- Let c0, c1, c2 be the numbers of indices i with stones[i] mod 3 = 0, 1, 2 respectively, using mathematical remainder so c0 + c1 + c2 = len(stones). Whenever stone_game_ix(stones) returns a result r (a Bool), r = true exactly when either (A) c0 is even and c1 > 0 and c2 > 0, or (B) c0 is odd and |c1 - c2| > 2. In every other successful return, r = false.
  Preconditions: The input satisfies the problem constraints: stones is a slice of 64-bit integers with 1 <= len(stones) <= 100000 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 10000. -/
theorem spec_1 (stones : Slice Std.I64) (hvalid : validInput stones) :
    ∀ r : Bool, stone_game_ix stones = Result.ok r →
      (r = true ↔
        (countResidue stones 0 % 2 = 0 ∧ 0 < countResidue stones 1 ∧ 0 < countResidue stones 2) ∨
        (countResidue stones 0 % 2 = 1 ∧
          2 < natAbsDiff (countResidue stones 1) (countResidue stones 2))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : validInput stones), ∀ r : Bool, stone_game_ix stones = Result.ok r →
      (r = true ↔
        (countResidue stones 0 % 2 = 0 ∧ 0 < countResidue stones 1 ∧ 0 < countResidue stones 2) ∨
        (countResidue stones 0 % 2 = 1 ∧
          2 < natAbsDiff (countResidue stones 1) (countResidue stones 2)))) := by
  sorry

/-- stone_game_ix(stones) does not fail: for every input satisfying the constraints it returns a Result.ok value, with no arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: The input satisfies the problem constraints: 1 <= len(stones) <= 100000 and, for every i with 0 <= i < len(stones), 1 <= stones[i] <= 10000. -/
theorem spec_2 (stones : Slice Std.I64) (hvalid : validInput stones) :
    ∃ r : Bool, stone_game_ix stones = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : validInput stones), ∃ r : Bool, stone_game_ix stones = Result.ok r) := by
  sorry

/-- Whenever stone_game_ix(stones) returns r and stone_game_ix(stones') returns r', we have r = r'.
  Preconditions: stones and stones' are both valid inputs as in the problem constraints (1 <= length <= 100000 and values in 1..10000), and stones' is a permutation of stones: same length and same multiset of values. -/
theorem spec_3 (stones stones' : Slice Std.I64) (hvalid : validInput stones)
    (hvalid' : validInput stones') (hperm : SameContent stones stones') :
    ∀ r r' : Bool, stone_game_ix stones = Result.ok r →
      stone_game_ix stones' = Result.ok r' → r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones stones' : Slice Std.I64) (hvalid : validInput stones)
    (hvalid' : validInput stones') (hperm : SameContent stones stones'), ∀ r r' : Bool, stone_game_ix stones = Result.ok r →
      stone_game_ix stones' = Result.ok r' → r = r') := by
  sorry

/-- Whenever stone_game_ix(stones) returns a result r, r = true, and Alice has a winning strategy in the stone-removal game whose first move is: if c1 <= c2, remove a stone whose value is congruent to 1 modulo 3; if c2 < c1, remove a stone whose value is congruent to 2 modulo 3. When c1 = c2, removing either a residue-1 or a residue-2 stone works as the first move.
  Preconditions: The input satisfies the constraints. Let c0, c1, c2 be the counts of entries with residues 0, 1, 2 modulo 3, with c0 even, c1 > 0, and c2 > 0. -/
theorem spec_4 (stones : Slice Std.I64) (hvalid : validInput stones)
    (hc0 : countResidue stones 0 % 2 = 0) (hc1 : 0 < countResidue stones 1)
    (hc2 : 0 < countResidue stones 2) :
    (∀ r : Bool, stone_game_ix stones = Result.ok r → r = true) ∧
    (firstPlayerWins (countResidue stones 0) (countResidue stones 1) (countResidue stones 2)
      = true) ∧
    (countResidue stones 1 ≤ countResidue stones 2 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
        (countResidue stones 2) 1 = true) ∧
    (countResidue stones 2 < countResidue stones 1 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
        (countResidue stones 2) 2 = true) ∧
    (countResidue stones 1 = countResidue stones 2 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
          (countResidue stones 2) 1 = true ∧
        winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
          (countResidue stones 2) 2 = true) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice Std.I64) (hvalid : validInput stones)
    (hc0 : countResidue stones 0 % 2 = 0) (hc1 : 0 < countResidue stones 1)
    (hc2 : 0 < countResidue stones 2), (∀ r : Bool, stone_game_ix stones = Result.ok r → r = true) ∧
    (firstPlayerWins (countResidue stones 0) (countResidue stones 1) (countResidue stones 2)
      = true) ∧
    (countResidue stones 1 ≤ countResidue stones 2 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
        (countResidue stones 2) 1 = true) ∧
    (countResidue stones 2 < countResidue stones 1 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
        (countResidue stones 2) 2 = true) ∧
    (countResidue stones 1 = countResidue stones 2 →
      winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
          (countResidue stones 2) 1 = true ∧
        winsByFirstRemoving (countResidue stones 0) (countResidue stones 1)
          (countResidue stones 2) 2 = true)) := by
  sorry

end AegisSpec.StoneGameIx
