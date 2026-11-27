import Aegis.MaxSubArray.Code.Funs

/-!
# Specifications of `Aegis.MaxSubArray.max_sub_array`

LeetCode problem `maximum-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSubArray

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def segSum (l : List ℤ) (i j : ℕ) : ℤ := ((l.drop i).take (j + 1 - i)).sum

def IsMaxSubarraySum (l : List ℤ) (r : ℤ) : Prop :=
  (∃ i j, i ≤ j ∧ j < l.length ∧ r = segSum l i j) ∧
    (∀ i j, i ≤ j → j < l.length → segSum l i j ≤ r)

/-- The function returns a result r and does not fail. For 0 <= i <= j < n, let S(i,j) = nums[i] + nums[i+1] + ... + nums[j]. Then there exist indices i,j with 0 <= i <= j < n such that r = S(i,j), and for every pair of indices i',j' with 0 <= i' <= j' < n, S(i',j') <= r.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      (∃ i j, i ≤ j ∧ j < (vals nums).length ∧ r.val = segSum (vals nums) i j) ∧
      (∀ i j, i ≤ j → j < (vals nums).length → segSum (vals nums) i j ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      (∃ i j, i ≤ j ∧ j < (vals nums).length ∧ r.val = segSum (vals nums) i j) ∧
      (∀ i j, i ≤ j → j < (vals nums).length → segSum (vals nums) i j ≤ r.val)) := by
  sorry

/-- The function returns a result r (it does not overflow, panic, or fail) for every input satisfying the preconditions.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r) := by
  sorry

/-- The function returns a result r. For 0 <= i <= j < n, let S(i,j) = nums[i] + nums[i+1] + ... + nums[j]. There exist indices i,j with 0 <= i <= j < n such that r = S(i,j).
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∃ i j, i ≤ j ∧ j < (vals nums).length ∧ r.val = segSum (vals nums) i j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∃ i j, i ≤ j ∧ j < (vals nums).length ∧ r.val = segSum (vals nums) i j) := by
  sorry

/-- The function returns a result r. For 0 <= i <= j < n, let S(i,j) = nums[i] + nums[i+1] + ... + nums[j]. For every pair of indices i,j with 0 <= i <= j < n, S(i,j) <= r.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∀ i j, i ≤ j → j < (vals nums).length → segSum (vals nums) i j ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∀ i j, i ≤ j → j < (vals nums).length → segSum (vals nums) i j ≤ r.val) := by
  sorry

/-- The function returns a result r and r = nums[0].
  Preconditions: Let n = len(nums). Then n = 1, and -10000 <= nums[0] <= 10000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn : (vals nums).length = 1)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ r.val = (vals nums)[0] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : (vals nums).length = 1)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ r.val = (vals nums)[0]) := by
  sorry

/-- The function returns a result r and r = nums[0] + nums[1] + ... + nums[n-1].
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000, and for every i with 0 <= i < n, nums[i] >= 0. -/
theorem spec_6 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hnonneg : ∀ (i : ℕ) (hi : i < (vals nums).length), 0 ≤ (vals nums)[i]) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ r.val = (vals nums).sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hnonneg : ∀ (i : ℕ) (hi : i < (vals nums).length), 0 ≤ (vals nums)[i]), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ r.val = (vals nums).sum) := by
  sorry

/-- The function returns a result r, and r is the maximum element of nums: there exists k0 with 0 <= k0 < n such that r = nums[k0], and for every k with 0 <= k < n, nums[k] <= r.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000, and for every i with 0 <= i < n, nums[i] <= 0. -/
theorem spec_7 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hnonpos : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i] ≤ 0) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      (∃ (k0 : ℕ) (hk0 : k0 < (vals nums).length), r.val = (vals nums)[k0]) ∧
      (∀ (k : ℕ) (hk : k < (vals nums).length), (vals nums)[k] ≤ r.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hnonpos : ∀ (i : ℕ) (hi : i < (vals nums).length), (vals nums)[i] ≤ 0), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      (∃ (k0 : ℕ) (hk0 : k0 < (vals nums).length), r.val = (vals nums)[k0]) ∧
      (∀ (k : ℕ) (hk : k < (vals nums).length), (vals nums)[k] ≤ r.val)) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000, and there exists i with 0 <= i < n and nums[i] >= 0. -/
theorem spec_8 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hwit : ∃ (i : ℕ) (hi : i < (vals nums).length), 0 ≤ (vals nums)[i]) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hwit : ∃ (i : ℕ) (hi : i < (vals nums).length), 0 ≤ (vals nums)[i]), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r > 0.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000, and there exists i with 0 <= i < n and nums[i] > 0. -/
theorem spec_9 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hwit : ∃ (i : ℕ) (hi : i < (vals nums).length), 0 < (vals nums)[i]) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ 0 < r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000)
    (hwit : ∃ (i : ℕ) (hi : i < (vals nums).length), 0 < (vals nums)[i]), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧ 0 < r.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} max(nums[i], 0), where max(nums[i], 0) is nums[i] if nums[i] > 0 and is 0 otherwise.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      r.val ≤ ((vals nums).map (fun x => max x 0)).sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      r.val ≤ ((vals nums).map (fun x => max x 0)).sum) := by
  sorry

/-- The function returns a result r. For 0 <= i <= j < n, let S(i,j) = nums[i] + nums[i+1] + ... + nums[j]. There exist indices i,j with 0 <= i <= j < n such that r = S(i,j) and either i = j, or (nums[i] >= 0 and nums[j] >= 0).
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_11 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∃ (i j : ℕ) (hij : i ≤ j) (hj : j < (vals nums).length),
        r.val = segSum (vals nums) i j ∧
          (i = j ∨ (0 ≤ (vals nums)[i] ∧ 0 ≤ (vals nums)[j])) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      ∃ (i j : ℕ) (hij : i ≤ j) (hj : j < (vals nums).length),
        r.val = segSum (vals nums) i j ∧
          (i = j ∨ (0 ≤ (vals nums)[i] ∧ 0 ≤ (vals nums)[j]))) := by
  sorry

/-- The function returns a result r. Let rev(nums) be the array of length n with rev(nums)[i] = nums[n-1-i] for 0 <= i < n. Then r is equal to the maximum sum of a non-empty contiguous subarray of rev(nums); that is, r = max { rev(nums)[i] + rev(nums)[i+1] + ... + rev(nums)[j] | 0 <= i <= j < n }.
  Preconditions: Let n = len(nums). Then 1 <= n <= 100000, and for every integer i with 0 <= i < n, -10000 <= nums[i] <= 10000. -/
theorem spec_12 (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000) :
    ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      IsMaxSubarraySum (vals nums).reverse r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ (vals nums).length)
    (hlen : (vals nums).length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < (vals nums).length),
      -10000 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 10000), ∃ r, Aegis.MaxSubArray.max_sub_array nums = ok r ∧
      IsMaxSubarraySum (vals nums).reverse r.val) := by
  sorry

end AegisSpec.MaxSubArray
