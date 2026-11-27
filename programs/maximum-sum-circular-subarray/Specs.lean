import Aegis.MaxSubarraySumCircular.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarraySumCircular.max_subarray_sum_circular`

LeetCode problem `maximum-sum-circular-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSubarraySumCircular

def numAt (nums : Slice I64) (i : ℕ) : ℤ :=
  (nums.val.getD i 0#i64).val

theorem length_eq_val_length (nums : Slice I64) : nums.val.length = nums.length := rfl

def circSum (nums : Slice I64) (s L : ℕ) : ℤ :=
  ∑ t ∈ Finset.range L, numAt nums ((s + t) % nums.length)

def segSum (nums : Slice I64) (i j : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (j + 1 - i), numAt nums (i + t)

def totalSum (nums : Slice I64) : ℤ :=
  ∑ i ∈ Finset.range nums.length, numAt nums i

def posSum (nums : Slice I64) : ℤ :=
  ∑ i ∈ Finset.range nums.length, max (numAt nums i) 0

def IsMaxElem (nums : Slice I64) (m : ℤ) : Prop :=
  (∀ i : ℕ, i < nums.length → numAt nums i ≤ m) ∧
    (∃ i : ℕ, i < nums.length ∧ numAt nums i = m)

def IsMaxCircSum (nums : Slice I64) (r : ℤ) : Prop :=
  (∀ s L : ℕ, s < nums.length → 1 ≤ L → L ≤ nums.length → circSum nums s L ≤ r) ∧
    (∃ s L : ℕ, s < nums.length ∧ 1 ≤ L ∧ L ≤ nums.length ∧ circSum nums s L = r)

/-- Whenever max_subarray_sum_circular(nums) returns a result r, it holds that r = max { CS(s,L) : 0 <= s < n and 1 <= L <= n }, where CS(s,L) = sum_{t=0}^{L-1} nums[(s+t) mod n]. Here the maximum is over all non-empty circular subarrays; each element is used at most once because L <= n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_1 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    IsMaxCircSum nums r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), IsMaxCircSum nums r.val) := by
  sorry

/-- For every input nums satisfying the preconditions, max_subarray_sum_circular(nums) returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_2 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000) :
    ∃ r : I64, Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000), ∃ r : I64, Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, r >= max_{0 <= i < n} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_3 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    ∀ i : ℕ, i < nums.length → numAt nums i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), ∀ i : ℕ, i < nums.length → numAt nums i ≤ r.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, r <= sum_{i=0}^{n-1} (if nums[i] > 0 then nums[i] else 0). In words, r is at most the sum of all positive elements of nums.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_4 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    r.val ≤ posSum nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), r.val ≤ posSum nums) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, r = sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000, for every i with 0 <= i < n, -30000 <= nums[i] <= 30000, and for every i with 0 <= i < n, nums[i] >= 0. -/
theorem spec_5 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hnonneg : ∀ i : ℕ, i < nums.length → 0 ≤ numAt nums i)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    r.val = totalSum nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hnonneg : ∀ i : ℕ, i < nums.length → 0 ≤ numAt nums i)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), r.val = totalSum nums) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, r = max_{0 <= i < n} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000, for every i with 0 <= i < n, -30000 <= nums[i] <= 30000, and for every i with 0 <= i < n, nums[i] <= 0. -/
theorem spec_6 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hnonpos : ∀ i : ℕ, i < nums.length → numAt nums i ≤ 0)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    IsMaxElem nums r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hnonpos : ∀ i : ℕ, i < nums.length → numAt nums i ≤ 0)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), IsMaxElem nums r.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, r >= M, where M = max { sum_{t=i}^{j} nums[t] : 0 <= i <= j < n } is the maximum sum of a non-empty ordinary (non-wrapping) contiguous subarray of nums.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_7 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    ∀ i j : ℕ, i ≤ j → j < nums.length → segSum nums i j ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), ∀ i j : ℕ, i ≤ j → j < nums.length → segSum nums i j ≤ r.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, there exist integers s and L such that 0 <= s < n, 1 <= L <= n, and r = sum_{t=0}^{L-1} nums[(s+t) mod n].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_8 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    ∃ s L : ℕ, s < nums.length ∧ 1 ≤ L ∧ L ≤ nums.length ∧ circSum nums s L = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), ∃ s L : ℕ, s < nums.length ∧ 1 ≤ L ∧ L ≤ nums.length ∧ circSum nums s L = r.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r, for every integer s with 0 <= s < n and every integer L with 1 <= L <= n, we have sum_{t=0}^{L-1} nums[(s+t) mod n] <= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. -/
theorem spec_9 (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r) :
    ∀ s L : ℕ, s < nums.length → 1 ≤ L → L ≤ nums.length → circSum nums s L ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (r : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r), ∀ s L : ℕ, s < nums.length → 1 ≤ L → L ≤ nums.length → circSum nums s L ≤ r.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r and max_subarray_sum_circular(nums') returns a result r', we have r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000 and for every i with 0 <= i < n, -30000 <= nums[i] <= 30000. Fix any integer k with 0 <= k < n and define the rotated array nums' of length n by nums'[i] = nums[(i+k) mod n] for 0 <= i < n. -/
theorem spec_10 (nums nums' : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (k : ℕ) (hk : k < nums.length)
    (hlen' : nums'.length = nums.length)
    (hrot : ∀ i : ℕ, i < nums.length → numAt nums' i = numAt nums ((i + k) % nums.length))
    (r r' : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r)
    (hres' : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (k : ℕ) (hk : k < nums.length)
    (hlen' : nums'.length = nums.length)
    (hrot : ∀ i : ℕ, i < nums.length → numAt nums' i = numAt nums ((i + k) % nums.length))
    (r r' : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r)
    (hres' : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever max_subarray_sum_circular(nums) returns a result r and max_subarray_sum_circular(nums') returns a result r', we have r' >= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 30000. Let nums' be any slice of length n such that for every i with 0 <= i < n, -30000 <= nums[i] <= 30000, -30000 <= nums'[i] <= 30000, and nums'[i] >= nums[i]. -/
theorem spec_11 (nums nums' : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hrange' : ∀ i : ℕ, i < nums'.length → -30000 ≤ numAt nums' i ∧ numAt nums' i ≤ 30000)
    (hlen' : nums'.length = nums.length)
    (hle : ∀ i : ℕ, i < nums.length → numAt nums i ≤ numAt nums' i)
    (r r' : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r)
    (hres' : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen_pos : 1 ≤ nums.length) (hlen_bound : nums.length ≤ 30000)
    (hrange : ∀ i : ℕ, i < nums.length → -30000 ≤ numAt nums i ∧ numAt nums i ≤ 30000)
    (hrange' : ∀ i : ℕ, i < nums'.length → -30000 ≤ numAt nums' i ∧ numAt nums' i ≤ 30000)
    (hlen' : nums'.length = nums.length)
    (hle : ∀ i : ℕ, i < nums.length → numAt nums i ≤ numAt nums' i)
    (r r' : I64)
    (hres : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums = ok r)
    (hres' : Aegis.MaxSubarraySumCircular.max_subarray_sum_circular nums' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxSubarraySumCircular
