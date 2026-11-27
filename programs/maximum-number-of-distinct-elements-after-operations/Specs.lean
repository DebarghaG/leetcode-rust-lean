import Aegis.MaxDistinctElements.Code.Funs

/-!
# Specifications of `Aegis.MaxDistinctElements.max_distinct_elements`

LeetCode problem `maximum-number-of-distinct-elements-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDistinctElements

def sliceValues (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def WithinReach (nums : List Int) (k : Int) (v : List Int) : Prop :=
  ∃ (hlen : v.length = nums.length),
    ∀ (i : Nat) (hi : i < nums.length),
      nums[i] - k ≤ v[i]'(hlen.symm ▸ hi) ∧ v[i]'(hlen.symm ▸ hi) ≤ nums[i] + k

def distinctCount (v : List Int) : Nat := v.toFinset.card

def IsMaxDistinctCount (nums : List Int) (k : Int) (r : Int) : Prop :=
  (∃ v : List Int, WithinReach nums k v ∧ (distinctCount v : Int) = r) ∧
    ∀ v : List Int, WithinReach nums k v → (distinctCount v : Int) ≤ r

def listMin : List Int → Int
  | [] => 0
  | a :: l => l.foldr min a

def listMax : List Int → Int
  | [] => 0
  | a :: l => l.foldr max a

def valueSetCard (nums : Slice Std.I64) : Nat := distinctCount (sliceValues nums)

/-- Whenever max_distinct_elements(nums, k) returns a result r, r equals the maximum, over all integer sequences v of length len(nums) with nums[i] - k <= v[i] <= nums[i] + k for every 0 <= i < len(nums), of the number of distinct integers appearing in v. Here v represents the final array after legally choosing, for each index i, to add some d with -k <= d <= k (possibly d = 0).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    IsMaxDistinctCount (sliceValues nums) k.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), IsMaxDistinctCount (sliceValues nums) k.val r.val) := by
  sorry

/-- The call max_distinct_elements(nums, k) returns a result; it does not fail because of arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
    ∃ r, Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∃ r, Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, 1 <= r <= len(nums).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), 1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever max_distinct_elements(nums, 0) returns r, r equals the number of distinct values in nums, that is, the cardinality of the set { nums[i] | 0 <= i < len(nums) }.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and k = 0. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums 0#i64 = ok r) :
    r.val = (valueSetCard nums : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums 0#i64 = ok r), r.val = (valueSetCard nums : Int)) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, r = min(len(nums), 2*k + 1).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000; and there exists an integer a such that nums[i] = a for every 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64) (a : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = a)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    r.val = min (nums.val.length : Int) (2 * k.val + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64) (a : Int)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = a)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), r.val = min (nums.val.length : Int) (2 * k.val + 1)) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, r = len(nums).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 0 <= k <= 1000000000; and len(nums) <= 2*k + 1. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hsmall : (nums.val.length : Int) ≤ 2 * k.val + 1)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    r.val = (nums.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hsmall : (nums.val.length : Int) ≤ 2 * k.val + 1)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), r.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, r >= the cardinality of the set { nums[i] | 0 <= i < len(nums) }.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    (valueSetCard nums : Int) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), (valueSetCard nums : Int) ≤ r.val) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, r >= min(len(nums), 2*k + 1).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    min (nums.val.length : Int) (2 * k.val + 1) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), min (nums.val.length : Int) (2 * k.val + 1) ≤ r.val) := by
  sorry

/-- Let lo = min { nums[i] | 0 <= i < len(nums) } and hi = max { nums[i] | 0 <= i < len(nums) }. Whenever max_distinct_elements(nums, k) returns r, r <= min(len(nums), hi - lo + 2*k + 1).
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    r.val ≤ min (nums.val.length : Int)
      (listMax (sliceValues nums) - listMin (sliceValues nums) + 2 * k.val + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), r.val ≤ min (nums.val.length : Int)
      (listMax (sliceValues nums) - listMin (sliceValues nums) + 2 * k.val + 1)) := by
  sorry

/-- Whenever max_distinct_elements(nums, k1) returns r1 and max_distinct_elements(nums, k2) returns r2, r1 <= r2.
  Preconditions: nums is an array with len(nums) between 1 and 100000 and every nums[i] between 1 and 1000000000; k1 and k2 are integers with 0 <= k1 <= k2 <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (r1 : Std.I64) (r2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk1_pos : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1000000000)
    (hres1 : Aegis.MaxDistinctElements.max_distinct_elements nums k1 = ok r1)
    (hres2 : Aegis.MaxDistinctElements.max_distinct_elements nums k2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 : Std.I64) (k2 : Std.I64)
    (r1 : Std.I64) (r2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk1_pos : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1000000000)
    (hres1 : Aegis.MaxDistinctElements.max_distinct_elements nums k1 = ok r1)
    (hres2 : Aegis.MaxDistinctElements.max_distinct_elements nums k2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r and max_distinct_elements(nums2, k) returns r2, r = r2.
  Preconditions: nums and nums2 are arrays of the same length n with 1 <= n <= 100000; every entry of both arrays is between 1 and 1000000000; k is between 0 and 1000000000; and nums2 is a permutation of nums (the two arrays have the same multiset of entries, possibly in different orders). -/
theorem spec_11 (nums nums2 : Slice Std.I64) (k : Std.I64) (r r2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hval2 : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hlen_eq : nums2.val.length = nums.val.length)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hperm : List.Perm (sliceValues nums2) (sliceValues nums))
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r)
    (hres2 : Aegis.MaxDistinctElements.max_distinct_elements nums2 k = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64) (r r2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hval2 : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hlen_eq : nums2.val.length = nums.val.length)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hperm : List.Perm (sliceValues nums2) (sliceValues nums))
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r)
    (hres2 : Aegis.MaxDistinctElements.max_distinct_elements nums2 k = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever max_distinct_elements(nums, k) returns r, there exists an integer sequence v of length len(nums) such that nums[i] - k <= v[i] <= nums[i] + k for every 0 <= i < len(nums), and the number of distinct integers appearing in v is exactly r.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; and 0 <= k <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r) :
    ∃ v : List Int, WithinReach (sliceValues nums) k.val v ∧ (distinctCount v : Int) = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000)
    (hres : Aegis.MaxDistinctElements.max_distinct_elements nums k = ok r), ∃ v : List Int, WithinReach (sliceValues nums) k.val v ∧ (distinctCount v : Int) = r.val) := by
  sorry

end AegisSpec.MaxDistinctElements
