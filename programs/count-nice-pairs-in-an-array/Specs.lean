import Aegis.CountNicePairs.Code.Funs

/-!
# Specifications of `Aegis.CountNicePairs.count_nice_pairs`

LeetCode problem `count-nice-pairs-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountNicePairs

namespace AegisSpec.CountNicePairs

def M : ℤ := 1000000007

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def digit (x k : Nat) : Nat := x / 10 ^ k % 10

def numDigits (x : Nat) : Nat := Nat.log 10 x + 1

def revNat (x : Nat) : Nat :=
  ((List.range (numDigits x)).map (fun k => digit x k)).foldl (fun acc d => acc * 10 + d) 0

def rev (x : ℤ) : ℤ := (revNat x.toNat : ℤ)

@[reducible] def nicePair (a b : ℤ) : Prop := a + rev b = b + rev a

def nicePairCount : List ℤ → ℕ
  | [] => 0
  | x :: xs => (xs.filter (fun y => decide (nicePair x y))).length + nicePairCount xs

def diffCount (l : List ℤ) (d : ℤ) : ℕ := (l.filter (fun x => x - rev x = d)).length

def nicePairCountByDiff (l : List ℤ) : ℕ :=
  (l.map (fun x => x - rev x)).toFinset.sum (fun d => diffCount l d * (diffCount l d - 1) / 2)

/-- Let M = 1000000007. For each non-negative integer x, let rev(x) be the integer obtained by writing x in decimal without leading zeros, reversing the resulting digit string, and interpreting it in decimal (so rev(0)=0, rev(123)=321, and rev(120)=21). Let C be the number of index pairs (i,j) such that 0 <= i < j < len(nums) and nums[i] + rev(nums[j]) = nums[j] + rev(nums[i]). Then count_nice_pairs(nums) returns a result r and r is the unique integer satisfying 0 <= r < M and r is congruent to C modulo M.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000) :
    ∃ r : Std.I64,
      count_nice_pairs nums = ok r ∧
        0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (nicePairCount (vals nums) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000), ∃ r : Std.I64,
      count_nice_pairs nums = ok r ∧
        0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (nicePairCount (vals nums) : ℤ)) := by
  sorry

/-- For every nums satisfying the preconditions, count_nice_pairs(nums) returns a result; it does not fail, panic, or overflow.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000) :
    ∃ r : Std.I64, count_nice_pairs nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000), ∃ r : Std.I64, count_nice_pairs nums = ok r) := by
  sorry

/-- For every nums satisfying the preconditions, whenever count_nice_pairs(nums) returns a result r, 0 <= r <= 1000000006.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000) :
    ∀ r : Std.I64, count_nice_pairs nums = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000), ∀ r : Std.I64, count_nice_pairs nums = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- count_nice_pairs(nums) returns 0.
  Preconditions: nums is a slice of 64-bit signed integers with len(nums) = 1 and 0 <= nums[0] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (a : ℤ)
    (hlen : vals nums = [a])
    (hval : 0 ≤ a ∧ a ≤ 1000000000) :
    ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (a : ℤ)
    (hlen : vals nums = [a])
    (hval : 0 ≤ a ∧ a ≤ 1000000000), ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 0) := by
  sorry

/-- Let rev be the decimal-digit reversal with rev(0)=0 and no leading zeros in the output. If nums[0] + rev(nums[1]) = nums[1] + rev(nums[0]), then count_nice_pairs(nums) returns 1; otherwise count_nice_pairs(nums) returns 0.
  Preconditions: nums is a slice of 64-bit signed integers with len(nums) = 2 and, for i = 0 and i = 1, 0 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (a b : ℤ)
    (hlen : vals nums = [a, b])
    (hval : (0 ≤ a ∧ a ≤ 1000000000) ∧ (0 ≤ b ∧ b ≤ 1000000000)) :
    (a + rev b = b + rev a → ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 1) ∧
      (a + rev b ≠ b + rev a → ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b : ℤ)
    (hlen : vals nums = [a, b])
    (hval : (0 ≤ a ∧ a ≤ 1000000000) ∧ (0 ≤ b ∧ b ≤ 1000000000)), (a + rev b = b + rev a → ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 1) ∧
      (a + rev b ≠ b + rev a → ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 0)) := by
  sorry

/-- count_nice_pairs(nums) returns (len(nums) * (len(nums) - 1) / 2) mod 1000000007.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. In addition, there is an integer d such that nums[i] - rev(nums[i]) = d for every i with 0 <= i < len(nums), where rev is decimal-digit reversal. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hd :
      ∃ d : ℤ,
        ∀ (i : ℕ) (hi : i < (vals nums).length), ((vals nums)[i]'hi) - rev ((vals nums)[i]'hi) = d) :
    ∃ r : Std.I64,
      count_nice_pairs nums = ok r ∧
        r.val = (((vals nums).length * ((vals nums).length - 1) / 2 : ℕ) : ℤ) % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hd :
      ∃ d : ℤ,
        ∀ (i : ℕ) (hi : i < (vals nums).length), ((vals nums)[i]'hi) - rev ((vals nums)[i]'hi) = d), ∃ r : Std.I64,
      count_nice_pairs nums = ok r ∧
        r.val = (((vals nums).length * ((vals nums).length - 1) / 2 : ℕ) : ℤ) % M) := by
  sorry

/-- Whenever count_nice_pairs(nums) returns r and count_nice_pairs(other) returns s, r = s.
  Preconditions: nums and other are slices of 64-bit signed integers, each satisfying 1 <= length <= 100000 and all elements between 0 and 1000000000 inclusive. Let rev be decimal-digit reversal. For every integer d, the number of indices i with 0 <= i < len(nums) and nums[i] - rev(nums[i]) = d equals the number of indices j with 0 <= j < len(other) and other[j] - rev(other[j]) = d. -/
theorem spec_7 (nums other : Slice Std.I64)
    (hlen_nums : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval_nums :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hlen_other : 1 ≤ (vals other).length ∧ (vals other).length ≤ 100000)
    (hval_other :
      ∀ (j : ℕ) (hj : j < (vals other).length),
        0 ≤ ((vals other)[j]'hj) ∧ ((vals other)[j]'hj) ≤ 1000000000)
    (hdiff : ∀ d : ℤ, diffCount (vals nums) d = diffCount (vals other) d) :
    ∀ r s : Std.I64,
      count_nice_pairs nums = ok r → count_nice_pairs other = ok s → r.val = s.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums other : Slice Std.I64)
    (hlen_nums : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval_nums :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hlen_other : 1 ≤ (vals other).length ∧ (vals other).length ≤ 100000)
    (hval_other :
      ∀ (j : ℕ) (hj : j < (vals other).length),
        0 ≤ ((vals other)[j]'hj) ∧ ((vals other)[j]'hj) ≤ 1000000000)
    (hdiff : ∀ d : ℤ, diffCount (vals nums) d = diffCount (vals other) d), ∀ r s : Std.I64,
      count_nice_pairs nums = ok r → count_nice_pairs other = ok s → r.val = s.val) := by
  sorry

/-- Let M = 1000000007 and let rev be decimal-digit reversal. For each integer d, let c(d) be the number of indices i such that 0 <= i < len(nums) and nums[i] - rev(nums[i]) = d. Whenever count_nice_pairs(nums) returns r, r is the unique integer with 0 <= r < M and r is congruent modulo M to the sum over all integers d of c(d) * (c(d) - 1) / 2.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000) :
    ∀ r : Std.I64,
      count_nice_pairs nums = ok r →
        0 ≤ r.val ∧ r.val < M ∧
          Int.ModEq M r.val (nicePairCountByDiff (vals nums) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 100000)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000), ∀ r : Std.I64,
      count_nice_pairs nums = ok r →
        0 ≤ r.val ∧ r.val < M ∧
          Int.ModEq M r.val (nicePairCountByDiff (vals nums) : ℤ)) := by
  sorry

/-- Let C be the number of index pairs (i,j) such that 0 <= i < j < len(nums) and nums[i] + rev(nums[j]) = nums[j] + rev(nums[i]), where rev is decimal-digit reversal. Then count_nice_pairs(nums) returns C.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 44721 and, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 44721)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000) :
    ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = (nicePairCount (vals nums) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 44721)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000), ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = (nicePairCount (vals nums) : ℤ)) := by
  sorry

/-- Let M = 1000000007 and let rev be decimal-digit reversal. Let add be the number of indices i with 0 <= i < len(nums) such that nums[i] - rev(nums[i]) = x - rev(x). Whenever count_nice_pairs(nums) returns r and count_nice_pairs(ext) returns s, s is the unique integer with 0 <= s < M and s is congruent to r + add modulo M.
  Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 99999 and all elements between 0 and 1000000000 inclusive. The integer x satisfies 0 <= x <= 1000000000. Let ext be the slice of length len(nums)+1 with ext[i] = nums[i] for 0 <= i < len(nums) and ext[len(nums)] = x. -/
theorem spec_10 (nums ext : Slice Std.I64) (x : ℤ)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 99999)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hx : 0 ≤ x ∧ x ≤ 1000000000)
    (hext : vals ext = vals nums ++ [x]) :
    ∀ r s : Std.I64,
      count_nice_pairs nums = ok r → count_nice_pairs ext = ok s →
        0 ≤ s.val ∧ s.val < M ∧
          Int.ModEq M s.val (r.val + (diffCount (vals nums) (x - rev x) : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums ext : Slice Std.I64) (x : ℤ)
    (hlen : 1 ≤ (vals nums).length ∧ (vals nums).length ≤ 99999)
    (hval :
      ∀ (i : ℕ) (hi : i < (vals nums).length),
        0 ≤ ((vals nums)[i]'hi) ∧ ((vals nums)[i]'hi) ≤ 1000000000)
    (hx : 0 ≤ x ∧ x ≤ 1000000000)
    (hext : vals ext = vals nums ++ [x]), ∀ r s : Std.I64,
      count_nice_pairs nums = ok r → count_nice_pairs ext = ok s →
        0 ≤ s.val ∧ s.val < M ∧
          Int.ModEq M s.val (r.val + (diffCount (vals nums) (x - rev x) : ℤ))) := by
  sorry

/-- count_nice_pairs(nums) returns 2.
  Preconditions: nums is the slice of 64-bit signed integers [42, 11, 1, 97]. -/
theorem spec_11 (nums : Slice Std.I64)
    (hnums : vals nums = [42, 11, 1, 97]) :
    ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hnums : vals nums = [42, 11, 1, 97]), ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 2) := by
  sorry

/-- count_nice_pairs(nums) returns 4.
  Preconditions: nums is the slice of 64-bit signed integers [13, 10, 35, 24, 76]. -/
theorem spec_12 (nums : Slice Std.I64)
    (hnums : vals nums = [13, 10, 35, 24, 76]) :
    ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 4 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hnums : vals nums = [13, 10, 35, 24, 76]), ∃ r : Std.I64, count_nice_pairs nums = ok r ∧ r.val = 4) := by
  sorry

end AegisSpec.CountNicePairs
