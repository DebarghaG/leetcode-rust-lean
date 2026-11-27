import Aegis.MinMoves.Code.Funs

/-!
# Specifications of `Aegis.MinMoves.min_moves`

LeetCode problem `minimum-moves-to-reach-target-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinMoves

open Aegis.MinMoves (min_moves)

inductive Move where
  | incr
  | dbl
  deriving DecidableEq, Repr

namespace Move

def act : Move → ℤ → ℤ
  | incr, x => x + 1
  | dbl, x => 2 * x

def isDbl : Move → Bool
  | dbl => true
  | incr => false

end Move

def runFrom (x : ℤ) (moves : List Move) : ℤ :=
  moves.foldl (fun v mv => mv.act v) x

def numDoubles (moves : List Move) : ℕ :=
  moves.countP Move.isDbl

def Reaches (target : ℤ) (maxDoubles : ℤ) (moves : List Move) : Prop :=
  runFrom 1 moves = target ∧ (numDoubles moves : ℤ) ≤ maxDoubles

def Achievable (target : ℤ) (maxDoubles : ℤ) (m : ℤ) : Prop :=
  ∃ moves : List Move, (moves.length : ℤ) = m ∧ Reaches target maxDoubles moves

def popcount (n : ℕ) : ℤ :=
  ((List.range (Nat.log2 n + 1)).countP (fun i => n.testBit i) : ℤ)

def floorLog2 (n : ℕ) : ℤ :=
  (Nat.log2 n : ℤ)

/-- The function returns a result r and r is the least non-negative integer m for which there exists a sequence of exactly m moves starting from 1 and ending at target, where each move is either an increment (replace the current value x by x + 1) or a double (replace x by 2 * x), and at most maxDoubles of the m moves are doubles.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_1 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧
      0 ≤ r.val ∧ Achievable target.val maxDoubles.val r.val ∧
      ∀ m : ℤ, 0 ≤ m → Achievable target.val maxDoubles.val m → r.val ≤ m := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧
      0 ≤ r.val ∧ Achievable target.val maxDoubles.val r.val ∧
      ∀ m : ℤ, 0 ≤ m → Achievable target.val maxDoubles.val m → r.val ≤ m) := by
  sorry

/-- The function does not fail: for every target and maxDoubles satisfying the preconditions, min_moves target maxDoubles returns a result (some Std.I64 value), not a panic/overflow/out-of-bounds failure.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_2 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∃ r : Std.I64, min_moves target maxDoubles = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∃ r : Std.I64, min_moves target maxDoubles = ok r) := by
  sorry

/-- Whenever min_moves target maxDoubles returns a result r, r >= 0.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_3 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∀ r : Std.I64, min_moves target maxDoubles = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever min_moves target maxDoubles returns a result r, r <= target - 1.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_4 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r → r.val ≤ target.val - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∀ r : Std.I64, min_moves target maxDoubles = ok r → r.val ≤ target.val - 1) := by
  sorry

/-- Let pc(n) be the number of 1-bits in the binary expansion of n (n >= 1), and let floor_log2(n) be the unique integer k with 2^k <= n < 2^(k+1). Whenever min_moves target maxDoubles returns a result r, r >= floor_log2(target) + pc(target) - 1.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_5 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      floorLog2 target.val.toNat + popcount target.val.toNat - 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      floorLog2 target.val.toNat + popcount target.val.toNat - 1 ≤ r.val) := by
  sorry

/-- Whenever min_moves target maxDoubles returns a result r, there exists a sequence of exactly r moves from 1 to target, each move being an increment or a double, in which the number of double moves is at most maxDoubles.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_6 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      Achievable target.val maxDoubles.val r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      Achievable target.val maxDoubles.val r.val) := by
  sorry

/-- Whenever min_moves target maxDoubles returns a result r, every sequence of moves from 1 to target in which each move is an increment or a double and the number of double moves is at most maxDoubles has length at least r.
  Preconditions: target and maxDoubles are integers with 1 <= target <= 1000000000 and 0 <= maxDoubles <= 100. -/
theorem spec_7 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      ∀ moves : List Move, Reaches target.val maxDoubles.val moves →
        r.val ≤ (moves.length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      ∀ moves : List Move, Reaches target.val maxDoubles.val moves →
        r.val ≤ (moves.length : ℤ)) := by
  sorry

/-- The function returns a result r with r = 0.
  Preconditions: target = 1 and 0 <= maxDoubles <= 100. -/
theorem spec_8 (target maxDoubles : Std.I64)
    (h_target : target.val = 1)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100) :
    ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧ r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target : target.val = 1)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100), ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r with r = target - 1.
  Preconditions: 1 <= target <= 1000000000 and maxDoubles = 0. -/
theorem spec_9 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md : maxDoubles.val = 0) :
    ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧ r.val = target.val - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md : maxDoubles.val = 0), ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧ r.val = target.val - 1) := by
  sorry

/-- The function returns a result r with r = ceil(target / 2), i.e., r is the least integer m such that 2*m >= target.
  Preconditions: 2 <= target <= 1000000000 and maxDoubles = 1. -/
theorem spec_10 (target maxDoubles : Std.I64)
    (h_target_lo : 2 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md : maxDoubles.val = 1) :
    ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧
      r.val = (target.val + 1) / 2 ∧
      ∀ m : ℤ, 2 * m ≥ target.val → r.val ≤ m := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 2 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md : maxDoubles.val = 1), ∃ r : Std.I64, min_moves target maxDoubles = ok r ∧
      r.val = (target.val + 1) / 2 ∧
      ∀ m : ℤ, 2 * m ≥ target.val → r.val ≤ m) := by
  sorry

/-- If min_moves target maxDoubles1 returns r1 and min_moves target maxDoubles2 returns r2, then r2 <= r1.
  Preconditions: 1 <= target <= 1000000000 and 0 <= maxDoubles1 <= maxDoubles2 <= 100. -/
theorem spec_11 (target maxDoubles1 maxDoubles2 : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md1_lo : 0 ≤ maxDoubles1.val) (h_md_le : maxDoubles1.val ≤ maxDoubles2.val)
    (h_md2_hi : maxDoubles2.val ≤ 100) :
    ∀ r1 r2 : Std.I64, min_moves target maxDoubles1 = ok r1 →
      min_moves target maxDoubles2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (target maxDoubles1 maxDoubles2 : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md1_lo : 0 ≤ maxDoubles1.val) (h_md_le : maxDoubles1.val ≤ maxDoubles2.val)
    (h_md2_hi : maxDoubles2.val ≤ 100), ∀ r1 r2 : Std.I64, min_moves target maxDoubles1 = ok r1 →
      min_moves target maxDoubles2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Let pc(n) be the number of 1-bits in the binary expansion of n. Whenever min_moves target maxDoubles returns a result r, r = floor_log2(target) + pc(target) - 1.
  Preconditions: 1 <= target <= 1000000000, 0 <= maxDoubles <= 100, and maxDoubles >= max(0, floor_log2(target) - 1), where floor_log2(n) is the unique k with 2^k <= n < 2^(k+1). -/
theorem spec_12 (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100)
    (h_enough : max (0 : ℤ) (floorLog2 target.val.toNat - 1) ≤ maxDoubles.val) :
    ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      r.val = floorLog2 target.val.toNat + popcount target.val.toNat - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (target maxDoubles : Std.I64)
    (h_target_lo : 1 ≤ target.val) (h_target_hi : target.val ≤ 1000000000)
    (h_md_lo : 0 ≤ maxDoubles.val) (h_md_hi : maxDoubles.val ≤ 100)
    (h_enough : max (0 : ℤ) (floorLog2 target.val.toNat - 1) ≤ maxDoubles.val), ∀ r : Std.I64, min_moves target maxDoubles = ok r →
      r.val = floorLog2 target.val.toNat + popcount target.val.toNat - 1) := by
  sorry

end AegisSpec.MinMoves
