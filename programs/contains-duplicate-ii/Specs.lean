import Aegis.ContainsNearbyDuplicate.Code.Funs

/-!
# Specifications of `Aegis.ContainsNearbyDuplicate.contains_nearby_duplicate`

LeetCode problem `contains-duplicate-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ContainsNearbyDuplicate

open Aegis.ContainsNearbyDuplicate

def elemVal (nums : Slice I64) (i : Nat) : Int :=
  ((nums.val[i]?).map (fun v => v.val)).getD 0

theorem elemVal_of_lt {nums : Slice I64} {i : Nat} (h : i < nums.val.length) :
    elemVal nums i = (nums.val[i]).val := by
  simp [elemVal, List.getElem?_eq_getElem h]

/-- The function returns a result r, and r = true if and only if there exist indices i and j such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, nums[i] == nums[j], and |i - j| <= k. Equivalently, r = false if and only if for every such distinct i and j, either nums[i] != nums[j] or |i - j| > k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= k <= 100000. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        elemVal nums i = elemVal nums j ∧ |(i : Int) - (j : Int)| ≤ k.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000), ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        elemVal nums i = elemVal nums j ∧ |(i : Int) - (j : Int)| ≤ k.val)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access out of bounds), and r is a Boolean value.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= k <= 100000. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000) :
    ∃ r, contains_nearby_duplicate nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000), ∃ r, contains_nearby_duplicate nums k = ok r) := by
  sorry

/-- The function returns a result r, and r = false.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; 0 <= k <= 100000; and k = 0. -/
theorem spec_3 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_eq0 : k.val = 0) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_eq0 : k.val = 0), ∃ r, contains_nearby_duplicate nums k = ok r ∧ r = false) := by
  sorry

/-- The function returns a result r, and r = true.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; 0 <= k <= 100000; 2 <= len(nums); 1 <= k; and for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] == nums[j]. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_len_ge2 : 2 ≤ nums.val.length) (h_k_ge1 : 1 ≤ k.val)
    (h_all_eq : ∀ i j, i < nums.val.length → j < nums.val.length →
      elemVal nums i = elemVal nums j) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_len_ge2 : 2 ≤ nums.val.length) (h_k_ge1 : 1 ≤ k.val)
    (h_all_eq : ∀ i j, i < nums.val.length → j < nums.val.length →
      elemVal nums i = elemVal nums j), ∃ r, contains_nearby_duplicate nums k = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r, and r = true if and only if there exists an index i such that 0 <= i < len(nums) - 1 and nums[i] == nums[i + 1].
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; 0 <= k <= 100000; and k = 1. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_eq1 : k.val = 1) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i, i < nums.val.length - 1 ∧ elemVal nums i = elemVal nums (i + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_eq1 : k.val = 1), ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i, i < nums.val.length - 1 ∧ elemVal nums i = elemVal nums (i + 1))) := by
  sorry

/-- The function returns a result r, and r = true if and only if k >= 1 and nums[0] == nums[1].
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; 0 <= k <= 100000; and len(nums) = 2. -/
theorem spec_6 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_len_eq2 : nums.val.length = 2) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ 1 ≤ k.val ∧ elemVal nums 0 = elemVal nums 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_len_eq2 : nums.val.length = 2), ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ 1 ≤ k.val ∧ elemVal nums 0 = elemVal nums 1)) := by
  sorry

/-- The function returns a result r, and r = true if and only if there exist distinct indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), and nums[i] == nums[j].
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; 0 <= k <= 100000; and k >= len(nums) - 1. -/
theorem spec_7 (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_big : ((nums.val.length : Int) - 1) ≤ k.val) :
    ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        elemVal nums i = elemVal nums j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_k_big : ((nums.val.length : Int) - 1) ≤ k.val), ∃ r, contains_nearby_duplicate nums k = ok r ∧
      (r = true ↔ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        elemVal nums i = elemVal nums j)) := by
  sorry

/-- For all integers k1 and k2 with 0 <= k1 <= k2 <= 100000, if contains_nearby_duplicate(nums, k1) returns r1 and contains_nearby_duplicate(nums, k2) returns r2, then r1 = true implies r2 = true.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice I64) (k1 k2 : I64) (r1 r2 : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k1_ge0 : 0 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 100000) :
    contains_nearby_duplicate nums k1 = ok r1 →
      contains_nearby_duplicate nums k2 = ok r2 → r1 = true → r2 = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k1 k2 : I64) (r1 r2 : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k1_ge0 : 0 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 100000), contains_nearby_duplicate nums k1 = ok r1 →
      contains_nearby_duplicate nums k2 = ok r2 → r1 = true → r2 = true) := by
  sorry

/-- Let rev be the slice with len(rev) = len(nums) and rev[i] = nums[len(nums) - 1 - i] for every 0 <= i < len(nums). If the function returns r on nums with k and returns s on rev with the same k, then r = s.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= k <= 100000. -/
theorem spec_9 (nums rev : Slice I64) (k : I64) (r s : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_rev_len : rev.val.length = nums.val.length)
    (h_rev : ∀ i, i < nums.val.length →
      elemVal rev i = elemVal nums (nums.val.length - 1 - i)) :
    contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate rev k = ok s → r = s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums rev : Slice I64) (k : I64) (r s : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_rev_len : rev.val.length = nums.val.length)
    (h_rev : ∀ i, i < nums.val.length →
      elemVal rev i = elemVal nums (nums.val.length - 1 - i)), contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate rev k = ok s → r = s) := by
  sorry

/-- Let c be any integer and let shifted be a slice with len(shifted) = len(nums) and shifted[i] = nums[i] + c for every 0 <= i < len(nums), assuming each sum is representable as a 64-bit integer and -1000000000 <= shifted[i] <= 1000000000 for every i. If the function returns r on nums with k and returns s on shifted with the same k, then r = s.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= k <= 100000. -/
theorem spec_10 (nums shifted : Slice I64) (k : I64) (c : Int) (r s : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_shift_len : shifted.val.length = nums.val.length)
    (h_shift : ∀ i, i < nums.val.length → elemVal shifted i = elemVal nums i + c)
    (h_repr : ∀ i, i < nums.val.length →
      -9223372036854775808 ≤ elemVal nums i + c ∧
        elemVal nums i + c ≤ 9223372036854775807)
    (h_shift_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal shifted i ∧ elemVal shifted i ≤ 1000000000) :
    contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate shifted k = ok s → r = s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums shifted : Slice I64) (k : I64) (c : Int) (r s : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000)
    (h_shift_len : shifted.val.length = nums.val.length)
    (h_shift : ∀ i, i < nums.val.length → elemVal shifted i = elemVal nums i + c)
    (h_repr : ∀ i, i < nums.val.length →
      -9223372036854775808 ≤ elemVal nums i + c ∧
        elemVal nums i + c ≤ 9223372036854775807)
    (h_shift_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal shifted i ∧ elemVal shifted i ≤ 1000000000), contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate shifted k = ok s → r = s) := by
  sorry

/-- Whenever the function returns a result r with r = true, there exist indices i and j such that 0 <= i < j < len(nums), nums[i] == nums[j], and j - i <= k.
  Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; and 0 <= k <= 100000. -/
theorem spec_11 (nums : Slice I64) (k : I64) (r : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000) :
    contains_nearby_duplicate nums k = ok r → r = true →
      ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
        elemVal nums i = elemVal nums j ∧ (j : Int) - (i : Int) ≤ k.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (r : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000), contains_nearby_duplicate nums k = ok r → r = true →
      ∃ i j : Nat, i < j ∧ j < nums.val.length ∧
        elemVal nums i = elemVal nums j ∧ (j : Int) - (i : Int) ≤ k.val) := by
  sorry

/-- If the function returns r on nums with k and returns r2 on nums2 with the same k, then r = true implies r2 = true.
  Preconditions: 1 <= len(nums) <= len(nums2) <= 100000; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; for every i with 0 <= i < len(nums2), -1000000000 <= nums2[i] <= 1000000000; nums2[i] = nums[i] for every 0 <= i < len(nums); and 0 <= k <= 100000. -/
theorem spec_12 (nums nums2 : Slice I64) (k : I64) (r r2 : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ nums2.val.length)
    (h_len2_le : nums2.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_bounds2 : ∀ i, i < nums2.val.length →
      -1000000000 ≤ elemVal nums2 i ∧ elemVal nums2 i ≤ 1000000000)
    (h_prefix : ∀ i, i < nums.val.length → elemVal nums2 i = elemVal nums i)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000) :
    contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate nums2 k = ok r2 → r = true → r2 = true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice I64) (k : I64) (r r2 : Bool)
    (h_len_ge1 : 1 ≤ nums.val.length)
    (h_len_le : nums.val.length ≤ nums2.val.length)
    (h_len2_le : nums2.val.length ≤ 100000)
    (h_bounds : ∀ i, i < nums.val.length →
      -1000000000 ≤ elemVal nums i ∧ elemVal nums i ≤ 1000000000)
    (h_bounds2 : ∀ i, i < nums2.val.length →
      -1000000000 ≤ elemVal nums2 i ∧ elemVal nums2 i ≤ 1000000000)
    (h_prefix : ∀ i, i < nums.val.length → elemVal nums2 i = elemVal nums i)
    (h_k_ge0 : 0 ≤ k.val) (h_k_le : k.val ≤ 100000), contains_nearby_duplicate nums k = ok r →
      contains_nearby_duplicate nums2 k = ok r2 → r = true → r2 = true) := by
  sorry

end AegisSpec.ContainsNearbyDuplicate
