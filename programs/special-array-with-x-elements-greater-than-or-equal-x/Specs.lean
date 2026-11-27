import Aegis.SpecialArray.Code.Funs

/-!
# Specifications of `Aegis.SpecialArray.special_array`

LeetCode problem `special-array-with-x-elements-greater-than-or-equal-x`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.SpecialArray (special_array)

namespace AegisSpec.SpecialArray

def countGE (nums : Slice I64) (x : Int) : Nat :=
  (nums.val.filter (fun v => x ≤ v.val)).length

def countEq (nums : Slice I64) (v : Int) : Nat :=
  (nums.val.filter (fun u => u.val = v)).length

def lenI (nums : Slice I64) : Int :=
  (nums.val.length : Int)

def maxVal (nums : Slice I64) : Int :=
  (nums.val.map (fun v => v.val)).foldr max 0

/-- Whenever special_array(nums) returns a result r, let n = len(nums) and for any integer x let C(x) be the number of indices i with 0 <= i < n and nums[i] >= x. Then r is the unique integer x such that 0 <= x <= n and C(x) = x, if such an integer exists; otherwise r = -1. Equivalently, r != -1 if and only if there exists x with 0 <= x <= n and C(x) = x, and when r != -1 we have 0 <= r <= n and C(r) = r.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) :
    (r.val ≠ -1 ↔ ∃ x : Int, 0 ≤ x ∧ x ≤ lenI nums ∧ (countGE nums x : Int) = x) ∧
    (r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ lenI nums ∧ (countGE nums r.val : Int) = r.val) ∧
    (∀ x : Int, 0 ≤ x → x ≤ lenI nums → (countGE nums x : Int) = x → x = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r), (r.val ≠ -1 ↔ ∃ x : Int, 0 ≤ x ∧ x ≤ lenI nums ∧ (countGE nums x : Int) = x) ∧
    (r.val ≠ -1 → 0 ≤ r.val ∧ r.val ≤ lenI nums ∧ (countGE nums r.val : Int) = r.val) ∧
    (∀ x : Int, 0 ≤ x → x ≤ lenI nums → (countGE nums x : Int) = x → x = r.val)) := by
  sorry

/-- For every nums satisfying the preconditions, special_array(nums) returns a result r; it does not fail.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000) :
    ∃ r : I64, special_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000), ∃ r : I64, special_array nums = ok r) := by
  sorry

/-- Whenever special_array(nums) returns a result r, either r = -1 or 1 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) :
    r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ lenI nums) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ lenI nums)) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r != -1, the number of indices i with 0 <= i < len(nums) and nums[i] >= r is exactly r.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1) :
    (countGE nums r.val : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1), (countGE nums r.val : Int) = r.val) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r = -1, for every integer x with 0 <= x <= len(nums), the number of indices i with 0 <= i < len(nums) and nums[i] >= x is not equal to x.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hneg : r.val = -1) :
    ∀ x : Int, 0 ≤ x → x ≤ lenI nums → (countGE nums x : Int) ≠ x := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hneg : r.val = -1), ∀ x : Int, 0 ≤ x → x ≤ lenI nums → (countGE nums x : Int) ≠ x) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r != -1, for every integer y with 0 <= y <= len(nums) and y != r, the number of indices i with 0 <= i < len(nums) and nums[i] >= y is not equal to y.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1) :
    ∀ y : Int, 0 ≤ y → y ≤ lenI nums → y ≠ r.val → (countGE nums y : Int) ≠ y := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1), ∀ y : Int, 0 ≤ y → y ≤ lenI nums → y ≠ r.val → (countGE nums y : Int) ≠ y) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r != -1, let C(x) be the number of indices i with 0 <= i < len(nums) and nums[i] >= x. Then for every integer x with 0 <= x < r, C(x) > x; and for every integer x with r < x <= len(nums), C(x) < x.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1) :
    (∀ x : Int, 0 ≤ x → x < r.val → x < (countGE nums x : Int)) ∧
    (∀ x : Int, r.val < x → x ≤ lenI nums → (countGE nums x : Int) < x) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1), (∀ x : Int, 0 ≤ x → x < r.val → x < (countGE nums x : Int)) ∧
    (∀ x : Int, r.val < x → x ≤ lenI nums → (countGE nums x : Int) < x)) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r != -1, r <= M, where M is the maximum of nums, i.e. M = max({nums[i] | 0 <= i < len(nums)}).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1) :
    r.val ≤ maxVal nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1), r.val ≤ maxVal nums) := by
  sorry

/-- If there exists an integer v with 0 <= v < len(nums) such that nums[i] = v for every i with 0 <= i < len(nums), then special_array(nums) returns the result -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_9 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hv : ∃ v : Int, 0 ≤ v ∧ v < lenI nums ∧ ∀ u ∈ nums.val, u.val = v) :
    ∃ r : I64, special_array nums = ok r ∧ r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hv : ∃ v : Int, 0 ≤ v ∧ v < lenI nums ∧ ∀ u ∈ nums.val, u.val = v), ∃ r : I64, special_array nums = ok r ∧ r.val = -1) := by
  sorry

/-- If nums[i] >= len(nums) for every i with 0 <= i < len(nums), then special_array(nums) returns the result len(nums).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_10 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hall : ∀ v ∈ nums.val, lenI nums ≤ v.val) :
    ∃ r : I64, special_array nums = ok r ∧ r.val = lenI nums := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hall : ∀ v ∈ nums.val, lenI nums ≤ v.val), ∃ r : I64, special_array nums = ok r ∧ r.val = lenI nums) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r = len(nums), every element of nums satisfies nums[i] >= len(nums) for 0 <= i < len(nums).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_11 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hlen : r.val = lenI nums) :
    ∀ v ∈ nums.val, lenI nums ≤ v.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hlen : r.val = lenI nums), ∀ v ∈ nums.val, lenI nums ≤ v.val) := by
  sorry

/-- For every two arrays nums and nums2 satisfying the preconditions, if for every integer v the number of indices i with nums[i] = v equals the number of indices i with nums2[i] = v (equivalently, nums2 is a permutation of nums), then whenever special_array(nums) returns r and special_array(nums2) returns s, we have r = s.
  Preconditions: For two arrays nums and nums2: 1 <= len(nums) <= 100, 1 <= len(nums2) <= 100, and for every i in the respective index ranges, 0 <= nums[i] <= 1000 and 0 <= nums2[i] <= 1000. -/
theorem spec_12 (nums nums2 : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h1' : 1 ≤ nums2.val.length) (h2' : nums2.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (h3' : ∀ v ∈ nums2.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hperm : ∀ v : Int, countEq nums v = countEq nums2 v)
    (r s : I64) (hr : special_array nums = ok r) (hs : special_array nums2 = ok s) :
    r.val = s.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h1' : 1 ≤ nums2.val.length) (h2' : nums2.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (h3' : ∀ v ∈ nums2.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (hperm : ∀ v : Int, countEq nums v = countEq nums2 v)
    (r s : I64) (hr : special_array nums = ok r) (hs : special_array nums2 = ok s), r.val = s.val) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r != -1, let C(x) be the number of indices i with 0 <= i < len(nums) and nums[i] >= x. Then r is the least integer x with 0 <= x <= len(nums) for which C(x) <= x.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_13 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1) :
    (0 ≤ r.val ∧ r.val ≤ lenI nums ∧ (countGE nums r.val : Int) ≤ r.val) ∧
    (∀ x : Int, 0 ≤ x → x < r.val → x < (countGE nums x : Int)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hne : r.val ≠ -1), (0 ≤ r.val ∧ r.val ≤ lenI nums ∧ (countGE nums r.val : Int) ≤ r.val) ∧
    (∀ x : Int, 0 ≤ x → x < r.val → x < (countGE nums x : Int))) := by
  sorry

/-- Whenever special_array(nums) returns a result r with r = -1, let n = len(nums) and C(x) be the number of indices i with 0 <= i < n and nums[i] >= x. Then there exists an integer x with 0 <= x < n such that C(x) > x and C(x+1) < x+1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000. -/
theorem spec_14 (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hneg : r.val = -1) :
    ∃ x : Int, 0 ≤ x ∧ x < lenI nums ∧ x < (countGE nums x : Int) ∧
      (countGE nums (x + 1) : Int) < x + 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ nums.val.length) (h2 : nums.val.length ≤ 100)
    (h3 : ∀ v ∈ nums.val, 0 ≤ v.val ∧ v.val ≤ 1000)
    (r : I64) (hr : special_array nums = ok r) (hneg : r.val = -1), ∃ x : Int, 0 ≤ x ∧ x < lenI nums ∧ x < (countGE nums x : Int) ∧
      (countGE nums (x + 1) : Int) < x + 1) := by
  sorry

end AegisSpec.SpecialArray
