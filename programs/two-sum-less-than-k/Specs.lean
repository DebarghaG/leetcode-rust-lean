import Aegis.TwoSumLessThanK.Code.Funs

/-!
# Specifications of `Aegis.TwoSumLessThanK.two_sum_less_than_k`

LeetCode problem `two-sum-less-than-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TwoSumLessThanK

def elem (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def pairSumsBelow (nums : Slice Std.I64) (k : Int) : Set Int :=
  { s | ∃ i j : Nat,
      i < j ∧ j < nums.val.length ∧ s = elem nums i + elem nums j ∧
        elem nums i + elem nums j < k }

def pairSums (nums : Slice Std.I64) : Set Int :=
  { s | ∃ i j : Nat, i < j ∧ j < nums.val.length ∧ s = elem nums i + elem nums j }

def IsMaxOf (nums : Slice Std.I64) (M : Int) : Prop :=
  (∃ t : Nat, t < nums.val.length ∧ elem nums t = M) ∧
    ∀ i : Nat, i < nums.val.length → elem nums i ≤ M

def occurrences (nums : Slice Std.I64) (v : Int) : Nat :=
  (nums.val.filter fun x => x.val == v).length

def IsPermutation (nums nums' : Slice Std.I64) : Prop :=
  nums.val.length = nums'.val.length ∧
    ∀ v : Int, occurrences nums v = occurrences nums' v

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, the following holds. Let S = {nums[i] + nums[j] | 0 <= i < j < len(nums) and nums[i] + nums[j] < k}. If S is empty, then r = -1; otherwise r is the maximum element of S, i.e., r is in S and every s in S satisfies s <= r.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      (pairSumsBelow nums k.val = ∅ → r.val = -1) ∧
        (pairSumsBelow nums k.val ≠ ∅ →
          r.val ∈ pairSumsBelow nums k.val ∧
            ∀ s, s ∈ pairSumsBelow nums k.val → s ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      (pairSumsBelow nums k.val = ∅ → r.val = -1) ∧
        (pairSumsBelow nums k.val ≠ ∅ →
          r.val ∈ pairSumsBelow nums k.val ∧
            ∀ s, s ∈ pairSumsBelow nums k.val → s ≤ r.val)) := by
  sorry

/-- The call two_sum_less_than_k(nums, k) returns a result r; it does not fail (no panic, no out-of-bounds access, and no 64-bit overflow).
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∃ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∃ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r and r != -1, we have r < k.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 → r.val < k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 → r.val < k.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r and r != -1, we have r >= 2.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 → 2 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 → 2 ≤ r.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, r = -1.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= k <= 2000; and len(nums) = 1. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen : nums.val.length = 1) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r → r.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen : nums.val.length = 1), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r → r.val = -1) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, if nums[0] + nums[1] < k then r = nums[0] + nums[1], and otherwise r = -1.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= k <= 2000; and len(nums) = 2. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen : nums.val.length = 2) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val = (if elem nums 0 + elem nums 1 < k.val
        then elem nums 0 + elem nums 1 else -1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen : nums.val.length = 2), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val = (if elem nums 0 + elem nums 1 < k.val
        then elem nums 0 + elem nums 1 else -1)) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r and r != -1, there exist indices i and j such that 0 <= i < j < len(nums), nums[i] + nums[j] < k, and r = nums[i] + nums[j].
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 →
        ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
          elem nums i + elem nums j < k.val ∧
            r.val = elem nums i + elem nums j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 →
        ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
          elem nums i + elem nums j < k.val ∧
            r.val = elem nums i + elem nums j) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r and r != -1, for every i and j with 0 <= i < j < len(nums) and nums[i] + nums[j] < k, we have nums[i] + nums[j] <= r.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 →
        ∀ i j : Nat, i < j → j < nums.val.length →
          elem nums i + elem nums j < k.val →
            elem nums i + elem nums j ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ≠ -1 →
        ∀ i j : Nat, i < j → j < nums.val.length →
          elem nums i + elem nums j < k.val →
            elem nums i + elem nums j ≤ r.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, r = -1 if and only if there do not exist indices i and j with 0 <= i < j < len(nums) and nums[i] + nums[j] < k.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and 1 <= k <= 2000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      (r.val = -1 ↔
        ¬ ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
          elem nums i + elem nums j < k.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      (r.val = -1 ↔
        ¬ ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
          elem nums i + elem nums j < k.val)) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r and two_sum_less_than_k(nums', k) returns a result r', we have r = r'.
  Preconditions: nums and nums' are slices of 64-bit integers; both satisfy 1 <= len <= 100 and all elements are in [1,1000]; 1 <= k <= 2000; nums' is a permutation of nums, meaning len(nums') = len(nums) and for every integer v, the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices i with 0 <= i < len(nums') and nums'[i] = v. -/
theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100)
    (helem_pos' : ∀ i : Nat, i < nums'.val.length → 1 ≤ elem nums' i)
    (helem_le' : ∀ i : Nat, i < nums'.val.length → elem nums' i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hperm : IsPermutation nums nums') :
    ∀ r r', Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      Aegis.TwoSumLessThanK.two_sum_less_than_k nums' k = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 100)
    (helem_pos' : ∀ i : Nat, i < nums'.val.length → 1 ≤ elem nums' i)
    (helem_le' : ∀ i : Nat, i < nums'.val.length → elem nums' i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hperm : IsPermutation nums nums'), ∀ r r', Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      Aegis.TwoSumLessThanK.two_sum_less_than_k nums' k = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k1) returns a result r1 and two_sum_less_than_k(nums, k2) returns a result r2, we have r1 <= r2.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; and k1 and k2 are integers with 1 <= k1 <= k2 <= 2000. -/
theorem spec_11 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 2000) :
    ∀ r1 r2, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k1 = ok r1 →
      Aegis.TwoSumLessThanK.two_sum_less_than_k nums k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 2000), ∀ r1 r2, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k1 = ok r1 →
      Aegis.TwoSumLessThanK.two_sum_less_than_k nums k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, r = k - 1.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= k <= 2000; and there exist indices i and j with 0 <= i < j < len(nums) and nums[i] + nums[j] = k - 1. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hpair : ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
      elem nums i + elem nums j = k.val - 1) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r → r.val = k.val - 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hpair : ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
      elem nums i + elem nums j = k.val - 1), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r → r.val = k.val - 1) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, r is the maximum element of the set {nums[i] + nums[j] | 0 <= i < j < len(nums)}.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= k <= 2000; len(nums) >= 2; and k > 2*M, where M is the maximum of nums (i.e., M = nums[t] for some t and nums[i] <= M for every i). -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64) (M : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen_two : 2 ≤ nums.val.length)
    (hM : IsMaxOf nums M) (hkM : 2 * M < k.val) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ∈ pairSums nums ∧ ∀ s, s ∈ pairSums nums → s ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (M : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen_two : 2 ≤ nums.val.length)
    (hM : IsMaxOf nums M) (hkM : 2 * M < k.val), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val ∈ pairSums nums ∧ ∀ s, s ∈ pairSums nums → s ≤ r.val) := by
  sorry

/-- Whenever two_sum_less_than_k(nums, k) returns a result r, if 2*v < k then r = 2*v, and otherwise r = -1.
  Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= k <= 2000; len(nums) >= 2; and there exists a 64-bit integer v such that for every i with 0 <= i < len(nums), nums[i] = v. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64) (v : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen_two : 2 ≤ nums.val.length)
    (hall : ∀ i : Nat, i < nums.val.length → elem nums i = v.val) :
    ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val = (if 2 * v.val < k.val then 2 * v.val else -1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (v : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (helem_pos : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i)
    (helem_le : ∀ i : Nat, i < nums.val.length → elem nums i ≤ 1000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
    (hlen_two : 2 ≤ nums.val.length)
    (hall : ∀ i : Nat, i < nums.val.length → elem nums i = v.val), ∀ r, Aegis.TwoSumLessThanK.two_sum_less_than_k nums k = ok r →
      r.val = (if 2 * v.val < k.val then 2 * v.val else -1)) := by
  sorry

end AegisSpec.TwoSumLessThanK
