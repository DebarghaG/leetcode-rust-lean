import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-pairs-with-xor-in-a-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPairs

def xor64 (a b : Int) : Int := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

def valAt (nums : Slice Std.I64) (i : Nat) : Int :=
  (nums.val.map (fun x => x.val)).getD i 0

def xorAt (nums : Slice Std.I64) (i j : Nat) : Int := xor64 (valAt nums i) (valAt nums j)

abbrev IsCountedPair (nums : Slice Std.I64) (low high : Int) (p : Nat × Nat) : Prop :=
  p.1 < p.2 ∧ p.2 < nums.val.length ∧ low ≤ xorAt nums p.1 p.2 ∧ xorAt nums p.1 p.2 ≤ high

abbrev IsOrderedPair (nums : Slice Std.I64) (low high : Int) (p : Nat × Nat) : Prop :=
  p.1 ≠ p.2 ∧ p.1 < nums.val.length ∧ p.2 < nums.val.length ∧
    low ≤ xorAt nums p.1 p.2 ∧ xorAt nums p.1 p.2 ≤ high

def pairCount (nums : Slice Std.I64) (low high : Int) : Nat :=
  ((List.range nums.val.length).product (List.range nums.val.length)).countP
    (fun p => decide (IsCountedPair nums low high p))

def orderedPairCount (nums : Slice Std.I64) (low high : Int) : Nat :=
  ((List.range nums.val.length).product (List.range nums.val.length)).countP
    (fun p => decide (IsOrderedPair nums low high p))

def HasCountedPair (nums : Slice Std.I64) (low high : Int) : Prop :=
  ∃ p : Nat × Nat, IsCountedPair nums low high p

def multiplicity (nums : Slice Std.I64) (v : Int) : Nat :=
  (nums.val.map (fun x => x.val)).countP (fun a => decide (a = v))

/-- The function returns a result r, and r equals the number of pairs (i, j) such that 0 <= i < j < len(nums) and low <= (nums[i] XOR nums[j]) <= high, where XOR denotes bitwise exclusive-or on the integer values.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high <= 20000. -/
theorem spec_1 (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000) :
    ∃ r : Std.I64, Aegis.CountPairs.count_pairs nums low high = ok r ∧
      r.val = (pairCount nums low.val high.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000), ∃ r : Std.I64, Aegis.CountPairs.count_pairs nums low high = ok r ∧
      r.val = (pairCount nums low.val high.val : Int)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, access out of bounds, or panic.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high <= 20000. -/
theorem spec_2 (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000) :
    ∃ r : Std.I64, Aegis.CountPairs.count_pairs nums low high = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000), ∃ r : Std.I64, Aegis.CountPairs.count_pairs nums low high = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums)*(len(nums)-1)/2.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high <= 20000. -/
theorem spec_3 (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r) :
    0 ≤ r.val ∧ r.val ≤ (((nums.val.length * (nums.val.length - 1)) / 2 : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r), 0 ≤ r.val ∧ r.val ≤ (((nums.val.length * (nums.val.length - 1)) / 2 : Nat) : Int)) := by
  sorry

/-- Whenever count_pairs nums low high returns r and count_pairs nums2 low high returns r2, we have r = r2.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; 1 <= low <= high <= 20000; and nums2 is a slice of i64 such that len(nums2) = len(nums) and for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices i with 0 <= i < len(nums2) and nums2[i] = v. -/
theorem spec_4 (nums nums2 : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (h_len2 : nums2.val.length = nums.val.length)
    (h_mult : ∀ v : Int, multiplicity nums v = multiplicity nums2 v)
    (r r2 : Std.I64)
    (h_r : Aegis.CountPairs.count_pairs nums low high = ok r)
    (h_r2 : Aegis.CountPairs.count_pairs nums2 low high = ok r2) :
    r = r2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (h_len2 : nums2.val.length = nums.val.length)
    (h_mult : ∀ v : Int, multiplicity nums v = multiplicity nums2 v)
    (r r2 : Std.I64)
    (h_r : Aegis.CountPairs.count_pairs nums low high = ok r)
    (h_r2 : Aegis.CountPairs.count_pairs nums2 low high = ok r2), r = r2) := by
  sorry

/-- Whenever count_pairs nums low high1 returns r1 and count_pairs nums low high2 returns r2, we have r1 <= r2.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high1 <= high2 <= 20000. -/
theorem spec_5 (nums : Slice Std.I64) (low high1 high2 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_1 : low.val ≤ high1.val) (h_2 : high1.val ≤ high2.val)
    (h_3 : high2.val ≤ 20000)
    (r1 r2 : Std.I64)
    (h_r1 : Aegis.CountPairs.count_pairs nums low high1 = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums low high2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high1 high2 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_1 : low.val ≤ high1.val) (h_2 : high1.val ≤ high2.val)
    (h_3 : high2.val ≤ 20000)
    (r1 r2 : Std.I64)
    (h_r1 : Aegis.CountPairs.count_pairs nums low high1 = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums low high2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever count_pairs nums low1 high returns r1 and count_pairs nums low2 high returns r2, we have r2 <= r1.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low1 <= low2 <= high <= 20000. -/
theorem spec_6 (nums : Slice Std.I64) (low1 low2 high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low1 : 1 ≤ low1.val) (h_12 : low1.val ≤ low2.val) (h_2h : low2.val ≤ high.val)
    (h_high : high.val ≤ 20000)
    (r1 r2 : Std.I64)
    (h_r1 : Aegis.CountPairs.count_pairs nums low1 high = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums low2 high = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (low1 low2 high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low1 : 1 ≤ low1.val) (h_12 : low1.val ≤ low2.val) (h_2h : low2.val ≤ high.val)
    (h_high : high.val ≤ 20000)
    (r1 r2 : Std.I64)
    (h_r1 : Aegis.CountPairs.count_pairs nums low1 high = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums low2 high = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever count_pairs nums low high returns r, 2*r equals the number of ordered pairs (i, j) such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and low <= (nums[i] XOR nums[j]) <= high.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high <= 20000. -/
theorem spec_7 (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r) :
    2 * r.val = (orderedPairCount nums low.val high.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r), 2 * r.val = (orderedPairCount nums low.val high.val : Int)) := by
  sorry

/-- Whenever count_pairs nums low high returns r, r > 0 if and only if there exists a pair (i, j) with 0 <= i < j < len(nums) and low <= (nums[i] XOR nums[j]) <= high.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; and 1 <= low <= high <= 20000. -/
theorem spec_8 (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r) :
    0 < r.val ↔ HasCountedPair nums low.val high.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (r : Std.I64) (h_r : Aegis.CountPairs.count_pairs nums low high = ok r), 0 < r.val ↔ HasCountedPair nums low.val high.val) := by
  sorry

/-- Whenever count_pairs nums low high returns r, count_pairs nums low t returns r1, and count_pairs nums t+1 high returns r2, we have r = r1 + r2.
  Preconditions: len(nums) is between 1 and 20000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 20000; 1 <= low <= high <= 20000; and t is an integer with low <= t < high. -/
theorem spec_9 (nums : Slice Std.I64) (low high t t1 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (h_t_low : low.val ≤ t.val) (h_t_high : t.val < high.val)
    (h_t1 : t1.val = t.val + 1)
    (r r1 r2 : Std.I64)
    (h_r : Aegis.CountPairs.count_pairs nums low high = ok r)
    (h_r1 : Aegis.CountPairs.count_pairs nums low t = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums t1 high = ok r2) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (low high t t1 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 20000)
    (h_val : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 20000)
    (h_low : 1 ≤ low.val) (h_low_high : low.val ≤ high.val) (h_high : high.val ≤ 20000)
    (h_t_low : low.val ≤ t.val) (h_t_high : t.val < high.val)
    (h_t1 : t1.val = t.val + 1)
    (r r1 r2 : Std.I64)
    (h_r : Aegis.CountPairs.count_pairs nums low high = ok r)
    (h_r1 : Aegis.CountPairs.count_pairs nums low t = ok r1)
    (h_r2 : Aegis.CountPairs.count_pairs nums t1 high = ok r2), r.val = r1.val + r2.val) := by
  sorry

end AegisSpec.CountPairs
