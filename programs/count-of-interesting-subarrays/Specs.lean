import Aegis.CountInterestingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountInterestingSubarrays.count_interesting_subarrays`

LeetCode problem `count-of-interesting-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountInterestingSubarrays

open Aegis.CountInterestingSubarrays
open scoped BigOperators

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def len (nums : Slice I64) : ℕ := nums.val.length

def cnt (nums : Slice I64) (modulo k : ℤ) (l r : ℕ) : ℤ :=
  (((vals nums).drop l).take (r + 1 - l)).countP (fun x => decide (x % modulo = k))

def ansCount (nums : Slice I64) (modulo k : ℤ) : ℤ :=
  ∑ l ∈ Finset.range (len nums), ∑ r ∈ Finset.Ico l (len nums),
    (if cnt nums modulo k l r % modulo = k then (1 : ℤ) else 0)

def ansExactCount (nums : Slice I64) (modulo k : ℤ) : ℤ :=
  ∑ l ∈ Finset.range (len nums), ∑ r ∈ Finset.Ico l (len nums),
    (if cnt nums modulo k l r = k then (1 : ℤ) else 0)

def existsInteresting (nums : Slice I64) (modulo k : ℤ) : Prop :=
  ∃ l r : ℕ, l ≤ r ∧ r < len nums ∧ cnt nums modulo k l r % modulo = k

/-- For each pair (l, r) with 0 <= l <= r < n, let cnt(l, r) be the number of indices i with l <= i <= r and nums[i] % modulo = k. The function returns a result ans and ans is exactly the number of pairs (l, r) with 0 <= l <= r < n such that cnt(l, r) % modulo = k. Subarrays are 0-indexed, contiguous, and non-empty.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_1 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ansCount nums modulo.val k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ansCount nums modulo.val k.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result ans; in particular, it does not fail because of integer overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_2 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, 0 <= ans <= n*(n+1)/2, where n = len(nums).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_3 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val) :
    ∀ ans : I64, count_interesting_subarrays nums modulo k = ok ans →
      0 ≤ ans.val ∧ ans.val ≤ (len nums : ℤ) * ((len nums : ℤ) + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val), ∀ ans : I64, count_interesting_subarrays nums modulo k = ok ans →
      0 ≤ ans.val ∧ ans.val ≤ (len nums : ℤ) * ((len nums : ℤ) + 1) / 2) := by
  sorry

/-- Let ans = count_interesting_subarrays(nums, modulo, k) and ans' = count_interesting_subarrays(nums', modulo, k). If for every i with 0 <= i < n, (nums[i] % modulo = k) iff (nums'[i] % modulo = k), then whenever both calls return results ans and ans', we have ans = ans'.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000 and 1 <= nums'[i] <= 1000000000; len(nums') = n; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_4 (nums nums' : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hbound' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000000)
    (hlen : len nums' = len nums)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hagree : ∀ p ∈ (vals nums).zip (vals nums'),
      (p.1 % modulo.val = k.val ↔ p.2 % modulo.val = k.val)) :
    ∀ ans ans' : I64,
      count_interesting_subarrays nums modulo k = ok ans →
      count_interesting_subarrays nums' modulo k = ok ans' →
      ans.val = ans'.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hbound' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000000)
    (hlen : len nums' = len nums)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hagree : ∀ p ∈ (vals nums).zip (vals nums'),
      (p.1 % modulo.val = k.val ↔ p.2 % modulo.val = k.val)), ∀ ans ans' : I64,
      count_interesting_subarrays nums modulo k = ok ans →
      count_interesting_subarrays nums' modulo k = ok ans' →
      ans.val = ans'.val) := by
  sorry

/-- Let n = len(nums) and let nums' be the reversal of nums, so len(nums') = n and nums'[i] = nums[n-1-i] for every i with 0 <= i < n. Whenever count_interesting_subarrays(nums, modulo, k) returns ans and count_interesting_subarrays(nums', modulo, k) returns ans', we have ans = ans'.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_5 (nums nums' : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hbound' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hrev : vals nums' = (vals nums).reverse) :
    ∀ ans ans' : I64,
      count_interesting_subarrays nums modulo k = ok ans →
      count_interesting_subarrays nums' modulo k = ok ans' →
      ans.val = ans'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums' : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hbound' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hrev : vals nums' = (vals nums).reverse), ∀ ans ans' : I64,
      count_interesting_subarrays nums modulo k = ok ans →
      count_interesting_subarrays nums' modulo k = ok ans' →
      ans.val = ans'.val) := by
  sorry

/-- The function returns a result ans and ans equals the sum over L from 1 to n of (n - L + 1 if L % modulo = k, otherwise 0), where n = len(nums).
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo; for every i with 0 <= i < n, nums[i] % modulo = k. -/
theorem spec_6 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hall : ∀ x ∈ vals nums, x % modulo.val = k.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ∑ L ∈ Finset.Ico 1 (len nums + 1),
        (if (L : ℤ) % modulo.val = k.val then (len nums : ℤ) - (L : ℤ) + 1 else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hall : ∀ x ∈ vals nums, x % modulo.val = k.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ∑ L ∈ Finset.Ico 1 (len nums + 1),
        (if (L : ℤ) % modulo.val = k.val then (len nums : ℤ) - (L : ℤ) + 1 else 0)) := by
  sorry

/-- The function returns a result ans and ans = 0.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo; k > 0; for every i with 0 <= i < n, nums[i] % modulo != k. -/
theorem spec_7 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hk_pos : 0 < k.val)
    (hnone : ∀ x ∈ vals nums, x % modulo.val ≠ k.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧ ans.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hk_pos : 0 < k.val)
    (hnone : ∀ x ∈ vals nums, x % modulo.val ≠ k.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧ ans.val = 0) := by
  sorry

/-- The function returns a result ans and ans = n*(n+1)/2, where n = len(nums), the total number of non-empty contiguous subarrays.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo; k = 0; for every i with 0 <= i < n, nums[i] % modulo != k. -/
theorem spec_8 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hk_zero : k.val = 0)
    (hnone : ∀ x ∈ vals nums, x % modulo.val ≠ k.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = (len nums : ℤ) * ((len nums : ℤ) + 1) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hk_zero : k.val = 0)
    (hnone : ∀ x ∈ vals nums, x % modulo.val ≠ k.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = (len nums : ℤ) * ((len nums : ℤ) + 1) / 2) := by
  sorry

/-- The function returns a result ans and ans is the number of pairs (l, r) with 0 <= l <= r < n such that the number of indices i with l <= i <= r and nums[i] % modulo = k is exactly k.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo; modulo > n. -/
theorem spec_9 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hmod_gt : (len nums : ℤ) < modulo.val) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ansExactCount nums modulo.val k.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hmod_gt : (len nums : ℤ) < modulo.val), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = ansExactCount nums modulo.val k.val) := by
  sorry

/-- Whenever the function returns a result ans, ans > 0 if and only if there exists a pair (l, r) with 0 <= l <= r < n such that, letting cnt(l, r) be the number of indices i with l <= i <= r and nums[i] % modulo = k, we have cnt(l, r) % modulo = k. Equivalently, ans = 0 if and only if no interesting subarray exists.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo. -/
theorem spec_10 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val) :
    ∀ ans : I64, count_interesting_subarrays nums modulo k = ok ans →
      (0 < ans.val ↔ existsInteresting nums modulo.val k.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val), ∀ ans : I64, count_interesting_subarrays nums modulo k = ok ans →
      (0 < ans.val ↔ existsInteresting nums modulo.val k.val)) := by
  sorry

/-- The function returns a result ans and ans = 1 if (nums[0] % modulo = k and 1 % modulo = k) or (nums[0] % modulo != k and k = 0), and ans = 0 otherwise.
  Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 1 <= modulo <= 1000000000; 0 <= k < modulo; n = 1. -/
theorem spec_11 (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hn_one : len nums = 1) :
    ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = (if ((vals nums).getD 0 0 % modulo.val = k.val ∧
                       (1 : ℤ) % modulo.val = k.val) ∨
                     ((vals nums).getD 0 0 % modulo.val ≠ k.val ∧ k.val = 0)
                   then (1 : ℤ) else 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (modulo k : I64)
    (hn_pos : 1 ≤ len nums) (hn_le : len nums ≤ 100000)
    (hbound : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000)
    (hmod_pos : 1 ≤ modulo.val) (hmod_le : modulo.val ≤ 1000000000)
    (hk_nonneg : 0 ≤ k.val) (hk_lt : k.val < modulo.val)
    (hn_one : len nums = 1), ∃ ans : I64, count_interesting_subarrays nums modulo k = ok ans ∧
      ans.val = (if ((vals nums).getD 0 0 % modulo.val = k.val ∧
                       (1 : ℤ) % modulo.val = k.val) ∨
                     ((vals nums).getD 0 0 % modulo.val ≠ k.val ∧ k.val = 0)
                   then (1 : ℤ) else 0)) := by
  sorry

end AegisSpec.CountInterestingSubarrays
