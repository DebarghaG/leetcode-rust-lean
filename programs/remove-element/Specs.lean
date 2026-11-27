import Aegis.RemoveElement.Code.Funs

/-!
# Specifications of `Aegis.RemoveElement.remove_element`

LeetCode problem `remove-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RemoveElement

namespace AegisSpec.RemoveElement

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def countEq (xs : List ℤ) (v : ℤ) : ℕ := (xs.filter (fun x => x = v)).length

def countNe (xs : List ℤ) (v : ℤ) : ℕ := (xs.filter (fun x => x ≠ v)).length

theorem vals_length (nums : Slice Std.I64) : (vals nums).length = nums.length := by
  simp [vals, Slice.length]

/-- The function returns a result r, and r is the number of indices i with 0 <= i < len(nums) such that nums[i] is not equal to val.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_1 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100) :
    ∃ r : Std.I64, remove_element nums val = ok r ∧ r.val = (countNe (vals nums) val.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100), ∃ r : Std.I64, remove_element nums val = ok r ∧ r.val = (countNe (vals nums) val.val : ℤ)) := by
  sorry

/-- For every nums and val satisfying the preconditions, the call does not fail: it returns some result r.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_2 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100) :
    ∃ r : Std.I64, remove_element nums val = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100), ∃ r : Std.I64, remove_element nums val = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_3 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) :
    0 ≤ r.val ∧ r.val ≤ (nums.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r), 0 ≤ r.val ∧ r.val ≤ (nums.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r plus the number of indices j with 0 <= j < len(nums) and nums[j] = val is equal to len(nums).
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_4 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) :
    r.val + (countEq (vals nums) val.val : ℤ) = (nums.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r), r.val + (countEq (vals nums) val.val : ℤ) = (nums.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r and r = 0, for every i with 0 <= i < len(nums), nums[i] = val.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_5 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) (hr0 : r.val = 0) :
    ∀ i : ℕ, ∀ (h : i < (vals nums).length), (vals nums)[i] = val.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) (hr0 : r.val = 0), ∀ i : ℕ, ∀ (h : i < (vals nums).length), (vals nums)[i] = val.val) := by
  sorry

/-- Whenever the function returns a result r and r = len(nums), for every i with 0 <= i < len(nums), nums[i] is not equal to val.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; and 0 <= val <= 100. -/
theorem spec_6 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) (hrlen : r.val = (nums.length : ℤ)) :
    ∀ i : ℕ, ∀ (h : i < (vals nums).length), (vals nums)[i] ≠ val.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (r : Std.I64) (hr : remove_element nums val = ok r) (hrlen : r.val = (nums.length : ℤ)), ∀ i : ℕ, ∀ (h : i < (vals nums).length), (vals nums)[i] ≠ val.val) := by
  sorry

/-- Whenever the function returns a result r, r < len(nums).
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= val <= 100; and there exists an index i with 0 <= i < len(nums) and nums[i] = val. -/
theorem spec_7 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length), (vals nums)[i] = val.val)
    (r : Std.I64) (hr : remove_element nums val = ok r) :
    r.val < (nums.length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length), (vals nums)[i] = val.val)
    (r : Std.I64) (hr : remove_element nums val = ok r), r.val < (nums.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r > 0.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= val <= 100; and there exists an index i with 0 <= i < len(nums) and nums[i] is not equal to val. -/
theorem spec_8 (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length), (vals nums)[i] ≠ val.val)
    (r : Std.I64) (hr : remove_element nums val = ok r) :
    0 < r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length), (vals nums)[i] ≠ val.val)
    (r : Std.I64) (hr : remove_element nums val = ok r), 0 < r.val) := by
  sorry

/-- Whenever remove_element(nums, val) returns r1 and remove_element(nums2, val) returns r2, r1 = r2.
  Preconditions: 0 <= len(nums) <= 100; all elements of nums are in [0,50]; 0 <= val <= 100; nums2 also has length at most 100 and all its elements are in [0,50]; len(nums2) = len(nums); and for every integer x, the number of indices i with 0 <= i < len(nums) and nums[i] = x equals the number of indices j with 0 <= j < len(nums2) and nums2[j] = x. -/
theorem spec_9 (nums nums2 : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hlen2 : nums2.length ≤ 100)
    (helems2 : ∀ i : ℕ, ∀ (h : i < (vals nums2).length), 0 ≤ (vals nums2)[i] ∧ (vals nums2)[i] ≤ 50)
    (hlenEq : nums2.length = nums.length)
    (hcounts : ∀ x : ℤ, countEq (vals nums) x = countEq (vals nums2) x)
    (r1 r2 : Std.I64) (hr1 : remove_element nums val = ok r1)
    (hr2 : remove_element nums2 val = ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hlen2 : nums2.length ≤ 100)
    (helems2 : ∀ i : ℕ, ∀ (h : i < (vals nums2).length), 0 ≤ (vals nums2)[i] ∧ (vals nums2)[i] ≤ 50)
    (hlenEq : nums2.length = nums.length)
    (hcounts : ∀ x : ℤ, countEq (vals nums) x = countEq (vals nums2) x)
    (r1 r2 : Std.I64) (hr1 : remove_element nums val = ok r1)
    (hr2 : remove_element nums2 val = ok r2), r1.val = r2.val) := by
  sorry

/-- Whenever remove_element(nums, val) returns r1 and remove_element(nums2, val) returns r2, r2 = r1 + 1.
  Preconditions: 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50; 0 <= val <= 100; nums2 has length at most 100; all elements of nums2 are in [0,50]; len(nums2) = len(nums); and there exists an index i with 0 <= i < len(nums) such that nums[i] = val, nums2[i] is not equal to val, and for every j with 0 <= j < len(nums) and j != i, nums[j] = nums2[j]. -/
theorem spec_10 (nums nums2 : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hlen2 : nums2.length ≤ 100)
    (helems2 : ∀ i : ℕ, ∀ (h : i < (vals nums2).length), 0 ≤ (vals nums2)[i] ∧ (vals nums2)[i] ≤ 50)
    (hlenEq : nums2.length = nums.length)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length) (h2 : i < (vals nums2).length),
      (vals nums)[i] = val.val ∧ (vals nums2)[i] ≠ val.val ∧
      ∀ j : ℕ, ∀ (hj : j < (vals nums).length) (hj2 : j < (vals nums2).length),
        j ≠ i → (vals nums)[j] = (vals nums2)[j])
    (r1 r2 : Std.I64) (hr1 : remove_element nums val = ok r1)
    (hr2 : remove_element nums2 val = ok r2) :
    r2.val = r1.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (val : Std.I64)
    (hlen : nums.length ≤ 100)
    (helems : ∀ i : ℕ, ∀ (h : i < (vals nums).length), 0 ≤ (vals nums)[i] ∧ (vals nums)[i] ≤ 50)
    (hval : 0 ≤ val.val ∧ val.val ≤ 100)
    (hlen2 : nums2.length ≤ 100)
    (helems2 : ∀ i : ℕ, ∀ (h : i < (vals nums2).length), 0 ≤ (vals nums2)[i] ∧ (vals nums2)[i] ≤ 50)
    (hlenEq : nums2.length = nums.length)
    (hex : ∃ i : ℕ, ∃ (h : i < (vals nums).length) (h2 : i < (vals nums2).length),
      (vals nums)[i] = val.val ∧ (vals nums2)[i] ≠ val.val ∧
      ∀ j : ℕ, ∀ (hj : j < (vals nums).length) (hj2 : j < (vals nums2).length),
        j ≠ i → (vals nums)[j] = (vals nums2)[j])
    (r1 r2 : Std.I64) (hr1 : remove_element nums val = ok r1)
    (hr2 : remove_element nums2 val = ok r2), r2.val = r1.val + 1) := by
  sorry

end AegisSpec.RemoveElement
