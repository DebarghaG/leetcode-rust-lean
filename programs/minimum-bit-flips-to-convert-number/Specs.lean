import Aegis.MinBitFlips.Code.Funs

/-!
# Specifications of `Aegis.MinBitFlips.min_bit_flips`

LeetCode problem `minimum-bit-flips-to-convert-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinBitFlips

namespace AegisSpec.MinBitFlips

def bitAt (x : ℤ) (i : ℕ) : ℤ := (x / (2 : ℤ) ^ i) % 2

def bitDiffCount (a b : ℤ) : ℕ :=
  ((Finset.range 64).filter (fun i => bitAt a i ≠ bitAt b i)).card

def isSingleBitFlip (x y : ℤ) : Prop :=
  ∃ i : ℕ, (bitAt x i = 0 ∧ y = x + (2 : ℤ) ^ i) ∨
           (bitAt x i = 1 ∧ y = x - (2 : ℤ) ^ i)

def ReachExact : ℕ → ℤ → ℤ → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z : ℤ, isSingleBitFlip x z ∧ ReachExact n z y

def bxor (a b : ℤ) : ℕ := Nat.xor a.toNat b.toNat

def toI64 (n : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, r equals the number of nonnegative integers i such that the i-th least significant bit of start differs from the i-th least significant bit of goal. Formally, with bit_i(x) = (x / 2^i) mod 2 for x >= 0, r = |{ i in Nat | bit_i(start) != bit_i(goal) }|. Bits above the highest set bit are treated as 0.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_1 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      r.val = (bitDiffCount start.val goal.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      r.val = (bitDiffCount start.val goal.val : ℤ)) := by
  sorry

/-- For every start and goal satisfying the preconditions, min_bit_flips(start, goal) returns Result.ok r for some i64 r; it does not panic, overflow, or otherwise fail.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_2 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∃ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∃ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r) := by
  sorry

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, 0 <= r.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_3 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      0 ≤ r.val) := by
  sorry

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, r <= 30.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_4 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      r.val ≤ 30 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      r.val ≤ 30) := by
  sorry

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, r = 0 if and only if start = goal.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_5 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      (r.val = 0 ↔ start.val = goal.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      (r.val = 0 ↔ start.val = goal.val)) := by
  sorry

/-- For every start and goal satisfying the preconditions, if min_bit_flips(start, goal) returns Result.ok r1 and min_bit_flips(goal, start) returns Result.ok r2, then r1 = r2.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_6 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r1 →
      Aegis.MinBitFlips.min_bit_flips goal start = ok r2 →
      r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r1 r2 : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r1 →
      Aegis.MinBitFlips.min_bit_flips goal start = ok r2 →
      r1.val = r2.val) := by
  sorry

/-- If min_bit_flips(start, goal) returns Result.ok r and min_bit_flips(2*start, 2*goal) returns Result.ok r', then r = r'.
  Preconditions: 0 <= start <= 10^9, 0 <= goal <= 10^9, 2*start <= 10^9, and 2*goal <= 10^9. -/
theorem spec_7 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hstart2 : 2 * start.val ≤ (10 ^ 9 : ℤ))
    (hgoal2 : 2 * goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 (2 * start.val)) (toI64 (2 * goal.val)) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hstart2 : 2 * start.val ≤ (10 ^ 9 : ℤ))
    (hgoal2 : 2 * goal.val ≤ (10 ^ 9 : ℤ)), ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 (2 * start.val)) (toI64 (2 * goal.val)) = ok r' →
      r.val = r'.val) := by
  sorry

/-- If min_bit_flips(start, goal) returns Result.ok r and min_bit_flips(start + 2^k, goal + 2^k) returns Result.ok r', then r = r'.
  Preconditions: 0 <= start <= 10^9, 0 <= goal <= 10^9, k is a nonnegative integer, bit_k(start) = 0, bit_k(goal) = 0, start + 2^k <= 10^9, and goal + 2^k <= 10^9, where bit_k(x) = (x / 2^k) mod 2. -/
theorem spec_8 (start goal : Std.I64) (k : ℕ)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hbitS : bitAt start.val k = 0)
    (hbitG : bitAt goal.val k = 0)
    (hstartk : start.val + (2 : ℤ) ^ k ≤ (10 ^ 9 : ℤ))
    (hgoalk : goal.val + (2 : ℤ) ^ k ≤ (10 ^ 9 : ℤ)) :
    ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 (start.val + (2 : ℤ) ^ k))
        (toI64 (goal.val + (2 : ℤ) ^ k)) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (start goal : Std.I64) (k : ℕ)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hbitS : bitAt start.val k = 0)
    (hbitG : bitAt goal.val k = 0)
    (hstartk : start.val + (2 : ℤ) ^ k ≤ (10 ^ 9 : ℤ))
    (hgoalk : goal.val + (2 : ℤ) ^ k ≤ (10 ^ 9 : ℤ)), ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 (start.val + (2 : ℤ) ^ k))
        (toI64 (goal.val + (2 : ℤ) ^ k)) = ok r' →
      r.val = r'.val) := by
  sorry

/-- If min_bit_flips(a, b) returns Result.ok rab, min_bit_flips(b, c) returns Result.ok rbc, and min_bit_flips(a, c) returns Result.ok rac, then rac <= rab + rbc.
  Preconditions: 0 <= a <= 10^9, 0 <= b <= 10^9, and 0 <= c <= 10^9. -/
theorem spec_9 (a b c : Std.I64)
    (ha : 0 ≤ a.val ∧ a.val ≤ (10 ^ 9 : ℤ))
    (hb : 0 ≤ b.val ∧ b.val ≤ (10 ^ 9 : ℤ))
    (hc : 0 ≤ c.val ∧ c.val ≤ (10 ^ 9 : ℤ)) :
    ∀ rab rbc rac : Std.I64,
      Aegis.MinBitFlips.min_bit_flips a b = ok rab →
      Aegis.MinBitFlips.min_bit_flips b c = ok rbc →
      Aegis.MinBitFlips.min_bit_flips a c = ok rac →
      rac.val ≤ rab.val + rbc.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b c : Std.I64)
    (ha : 0 ≤ a.val ∧ a.val ≤ (10 ^ 9 : ℤ))
    (hb : 0 ≤ b.val ∧ b.val ≤ (10 ^ 9 : ℤ))
    (hc : 0 ≤ c.val ∧ c.val ≤ (10 ^ 9 : ℤ)), ∀ rab rbc rac : Std.I64,
      Aegis.MinBitFlips.min_bit_flips a b = ok rab →
      Aegis.MinBitFlips.min_bit_flips b c = ok rbc →
      Aegis.MinBitFlips.min_bit_flips a c = ok rac →
      rac.val ≤ rab.val + rbc.val) := by
  sorry

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, there exists a finite sequence of exactly r single-bit flips that transforms start into goal. A single-bit flip chooses a nonnegative bit position i and replaces a number x by x + 2^i if the i-th bit of x is 0, or by x - 2^i if the i-th bit of x is 1.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_10 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      ∃ n : ℕ, (n : ℤ) = r.val ∧ ReachExact n start.val goal.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      ∃ n : ℕ, (n : ℤ) = r.val ∧ ReachExact n start.val goal.val) := by
  sorry

/-- Whenever min_bit_flips(start, goal) returns Result.ok r, there is no finite sequence of fewer than r single-bit flips that transforms start into goal, where a single-bit flip chooses a nonnegative bit position i and replaces a number x by x + 2^i if the i-th bit of x is 0, or by x - 2^i if the i-th bit of x is 1.
  Preconditions: 0 <= start <= 10^9 and 0 <= goal <= 10^9. -/
theorem spec_11 (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)) :
    ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      ∀ n : ℕ, (n : ℤ) < r.val → ¬ ReachExact n start.val goal.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (start goal : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ)), ∀ r : Std.I64, Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      ∀ n : ℕ, (n : ℤ) < r.val → ¬ ReachExact n start.val goal.val) := by
  sorry

/-- If min_bit_flips(start, goal) returns Result.ok r and min_bit_flips((2^m - 1) - start, (2^m - 1) - goal) returns Result.ok r', then r = r'.
  Preconditions: m is a nonnegative integer with 2^m - 1 <= 10^9, 0 <= start < 2^m, and 0 <= goal < 2^m. -/
theorem spec_12 (start goal : Std.I64) (m : ℕ)
    (hm : (2 : ℤ) ^ m - 1 ≤ (10 ^ 9 : ℤ))
    (hstart : 0 ≤ start.val ∧ start.val < (2 : ℤ) ^ m)
    (hgoal : 0 ≤ goal.val ∧ goal.val < (2 : ℤ) ^ m) :
    ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 ((2 : ℤ) ^ m - 1 - start.val))
        (toI64 ((2 : ℤ) ^ m - 1 - goal.val)) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (start goal : Std.I64) (m : ℕ)
    (hm : (2 : ℤ) ^ m - 1 ≤ (10 ^ 9 : ℤ))
    (hstart : 0 ≤ start.val ∧ start.val < (2 : ℤ) ^ m)
    (hgoal : 0 ≤ goal.val ∧ goal.val < (2 : ℤ) ^ m), ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips (toI64 ((2 : ℤ) ^ m - 1 - start.val))
        (toI64 ((2 : ℤ) ^ m - 1 - goal.val)) = ok r' →
      r.val = r'.val) := by
  sorry

/-- If min_bit_flips(start, goal) returns Result.ok r and min_bit_flips(start', goal') returns Result.ok r', then r = r'.
  Preconditions: 0 <= start <= 10^9, 0 <= goal <= 10^9, 0 <= start' <= 10^9, 0 <= goal' <= 10^9, and (start XOR goal) = (start' XOR goal'), where XOR is bitwise exclusive or on nonnegative integers. -/
theorem spec_13 (start goal start' goal' : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hstart' : 0 ≤ start'.val ∧ start'.val ≤ (10 ^ 9 : ℤ))
    (hgoal' : 0 ≤ goal'.val ∧ goal'.val ≤ (10 ^ 9 : ℤ))
    (hxor : bxor start.val goal.val = bxor start'.val goal'.val) :
    ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips start' goal' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (start goal start' goal' : Std.I64)
    (hstart : 0 ≤ start.val ∧ start.val ≤ (10 ^ 9 : ℤ))
    (hgoal : 0 ≤ goal.val ∧ goal.val ≤ (10 ^ 9 : ℤ))
    (hstart' : 0 ≤ start'.val ∧ start'.val ≤ (10 ^ 9 : ℤ))
    (hgoal' : 0 ≤ goal'.val ∧ goal'.val ≤ (10 ^ 9 : ℤ))
    (hxor : bxor start.val goal.val = bxor start'.val goal'.val), ∀ r r' : Std.I64,
      Aegis.MinBitFlips.min_bit_flips start goal = ok r →
      Aegis.MinBitFlips.min_bit_flips start' goal' = ok r' →
      r.val = r'.val) := by
  sorry

end AegisSpec.MinBitFlips
