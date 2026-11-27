import Aegis.FirstMissingPositive.Code.Funs

/-!
# Specifications of `Aegis.FirstMissingPositive.first_missing_positive`

LeetCode problem `first-missing-positive`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FirstMissingPositive (first_missing_positive)

namespace AegisSpec.FirstMissingPositive

def Occurs (l : List Std.I64) (k : Int) : Prop :=
  ∃ i : Fin l.length, (l.get i).val = k

/-- The function returns a result r and r is the smallest positive integer not present in nums: (1) r >= 1; (2) for every i with 0 <= i < len(nums), nums[i] != r; (3) for every integer k with 1 <= k < r, there exists an index i with 0 <= i < len(nums) and nums[i] = k.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647) :
    ∃ r : Std.I64,
      first_missing_positive nums = ok r ∧
      1 ≤ r.val ∧
      (∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) ∧
      (∀ k : Int, 1 ≤ k → k < r.val → Occurs nums.val k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647), ∃ r : Std.I64,
      first_missing_positive nums = ok r ∧
      1 ≤ r.val ∧
      (∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) ∧
      (∀ k : Int, 1 ≤ k → k < r.val → Occurs nums.val k)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647) :
    ∃ r : Std.I64, first_missing_positive nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647), ∃ r : Std.I64, first_missing_positive nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), nums[i] != r.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r) :
    ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r), ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 1 <= k < r, there exists an index i with 0 <= i < len(nums) and nums[i] = k.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r) :
    ∀ k : Int, 1 ≤ k → k < r.val → Occurs nums.val k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r), ∀ k : Int, 1 ≤ k → k < r.val → Occurs nums.val k) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums) + 1.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r) :
    r.val ≤ (nums.val.length : Int) + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r), r.val ≤ (nums.val.length : Int) + 1) := by
  sorry

/-- Whenever the function returns a result r, if for every i with 0 <= i < len(nums), nums[i] != 1, then r = 1.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ 1) :
    r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ 1), r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(nums) and nums[i] = 1, then r >= 2.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : Occurs nums.val 1) :
    2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : Occurs nums.val 1), 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if for every integer k with 1 <= k <= len(nums), there exists an index i with 0 <= i < len(nums) and nums[i] = k, then r = len(nums) + 1.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (hall : ∀ k : Int, 1 ≤ k → k ≤ (nums.val.length : Int) → Occurs nums.val k) :
    r.val = (nums.val.length : Int) + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (hall : ∀ k : Int, 1 ≤ k → k ≤ (nums.val.length : Int) → Occurs nums.val k), r.val = (nums.val.length : Int) + 1) := by
  sorry

/-- Whenever the function returns a result r, if r = len(nums) + 1, then for every integer k with 1 <= k <= len(nums), there exists an index i with 0 <= i < len(nums) and nums[i] = k.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (hr_len : r.val = (nums.val.length : Int) + 1) :
    ∀ k : Int, 1 ≤ k → k ≤ (nums.val.length : Int) → Occurs nums.val k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (hr_len : r.val = (nums.val.length : Int) + 1), ∀ k : Int, 1 ≤ k → k ≤ (nums.val.length : Int) → Occurs nums.val k) := by
  sorry

/-- Whenever first_missing_positive(nums) returns r and first_missing_positive(nums') returns r', if for every positive integer v, v occurs in nums if and only if v occurs in nums', then r = r'.
  Preconditions: Both nums and nums' satisfy 0 <= len <= 100000 and all elements are in [-2147483648, 2147483647]. -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (hlen'_nonneg : 0 ≤ nums'.val.length) (hlen' : nums'.val.length ≤ 100000)
    (hbounds' : ∀ i : Fin nums'.val.length,
      -2147483648 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ 2147483647)
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r')
    (hinv : ∀ v : Int, 1 ≤ v → (Occurs nums.val v ↔ Occurs nums'.val v)) :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (hlen'_nonneg : 0 ≤ nums'.val.length) (hlen' : nums'.val.length ≤ 100000)
    (hbounds' : ∀ i : Fin nums'.val.length,
      -2147483648 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ 2147483647)
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r')
    (hinv : ∀ v : Int, 1 ≤ v → (Occurs nums.val v ↔ Occurs nums'.val v)), r.val = r'.val) := by
  sorry

/-- Let nums' be the array obtained from nums by replacing the element at index i with v. Whenever first_missing_positive(nums) returns r and first_missing_positive(nums') returns r', we have r = r'.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647; 0 <= i < len(nums); (nums[i] <= 0 or nums[i] > len(nums)); -2147483648 <= v <= 2147483647; and (v <= 0 or v > len(nums)). -/
theorem spec_12 (nums nums' : Slice Std.I64) (i : Nat) (v : Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ j : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get j).val ∧ (nums.val.get j).val ≤ 2147483647)
    (hi : i < nums.val.length)
    (hi_out : (nums.val.get ⟨i, hi⟩).val ≤ 0 ∨
      (nums.val.get ⟨i, hi⟩).val > (nums.val.length : Int))
    (hv_bounds : -2147483648 ≤ v.val ∧ v.val ≤ 2147483647)
    (hv_out : v.val ≤ 0 ∨ v.val > (nums.val.length : Int))
    (hnums' : nums'.val = nums.val.set i v)
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (i : Nat) (v : Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ j : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get j).val ∧ (nums.val.get j).val ≤ 2147483647)
    (hi : i < nums.val.length)
    (hi_out : (nums.val.get ⟨i, hi⟩).val ≤ 0 ∨
      (nums.val.get ⟨i, hi⟩).val > (nums.val.length : Int))
    (hv_bounds : -2147483648 ≤ v.val ∧ v.val ≤ 2147483647)
    (hv_out : v.val ≤ 0 ∨ v.val > (nums.val.length : Int))
    (hnums' : nums'.val = nums.val.set i v)
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Let nums' be the array obtained by appending v to nums. Then first_missing_positive(nums') >= first_missing_positive(nums).
  Preconditions: 0 <= len(nums) <= 100000; all elements of nums are in [-2147483648, 2147483647]; len(nums) < 100000; and v is an integer with -2147483648 <= v <= 2147483647. -/
theorem spec_13 (nums nums' : Slice Std.I64) (v : Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (hlen_lt : nums.val.length < 100000)
    (hv_bounds : -2147483648 ≤ v.val ∧ v.val ≤ 2147483647)
    (hnums' : nums'.val = nums.val ++ [v])
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (v : Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (hlen_lt : nums.val.length < 100000)
    (hv_bounds : -2147483648 ≤ v.val ∧ v.val ≤ 2147483647)
    (hnums' : nums'.val = nums.val ++ [v])
    (r r' : Std.I64)
    (hr : first_missing_positive nums = ok r)
    (hr' : first_missing_positive nums' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index i with 0 <= i < len(nums) and nums[i] = 1, and for every i with 0 <= i < len(nums), nums[i] != 2, then r = 2.
  Preconditions: 0 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -2147483648 <= nums[i] <= 2147483647. -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : Occurs nums.val 1)
    (h2 : ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ 2) :
    r.val = 2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_nonneg : 0 ≤ nums.val.length) (hlen : nums.val.length ≤ 100000)
    (hbounds : ∀ i : Fin nums.val.length,
      -2147483648 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 2147483647)
    (r : Std.I64) (hr : first_missing_positive nums = ok r)
    (h1 : Occurs nums.val 1)
    (h2 : ∀ i : Fin nums.val.length, (nums.val.get i).val ≠ 2), r.val = 2) := by
  sorry

end AegisSpec.FirstMissingPositive
