import Aegis.FindSmallestInteger.Code.Funs

/-!
# Specifications of `Aegis.FindSmallestInteger.find_smallest_integer`

LeetCode problem `smallest-missing-non-negative-integer-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindSmallestInteger

def nmod (x value : ℤ) : ℤ := Int.emod x value

def cnt (nums : List I64) (value a : ℤ) : ℕ :=
  (nums.filter (fun x => nmod x.val value = a)).length

def need (value m a : ℤ) : ℕ :=
  ((List.range m.toNat).filter (fun t => nmod (t : ℤ) value = a)).length

def Feasible (nums : List I64) (value m : ℤ) : Prop :=
  ∀ a : ℤ, 0 ≤ a → a < value → need value m a ≤ cnt nums value a

/-- Whenever find_smallest_integer(nums, value) returns a result r, r is the largest integer m with 0 <= m <= len(nums) such that for every residue a with 0 <= a < value, cnt(a) >= the number of integers t with 0 <= t < m and t mod value = a, where cnt(a) is the number of indices i with 0 <= i < len(nums) and nums[i] mod value = a. Equivalently, r is the maximum MEX attainable from nums by any number of operations that add or subtract value to individual elements.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value, so 0 <= x mod value < value. -/
theorem spec_1 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    IsGreatest
      {m : ℤ | 0 ≤ m ∧ m ≤ (nums.val.length : ℤ) ∧ Feasible nums.val value.val m}
      r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), IsGreatest
      {m : ℤ | 0 ≤ m ∧ m ≤ (nums.val.length : ℤ) ∧ Feasible nums.val value.val m}
      r.val) := by
  sorry

/-- For every input satisfying the preconditions, find_smallest_integer(nums, value) returns a result; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_2 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000) :
    ∃ r : I64, Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000), ∃ r : I64, Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, 0 <= r.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_3 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, r <= len(nums).
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_4 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, there is a choice of pairwise distinct indices i_t, one for each integer t with 0 <= t < r, all in [0, len(nums)), such that nums[i_t] mod value = t mod value for every such t. If r <= 0 the choice is empty.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_5 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    ∃ idx : Fin r.val.toNat → Fin nums.val.length,
      Function.Injective idx ∧
        ∀ t : Fin r.val.toNat,
          nmod (nums.val.get (idx t)).val value.val = nmod (t.val : ℤ) value.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), ∃ idx : Fin r.val.toNat → Fin nums.val.length,
      Function.Injective idx ∧
        ∀ t : Fin r.val.toNat,
          nmod (nums.val.get (idx t)).val value.val = nmod (t.val : ℤ) value.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, there is no choice of pairwise distinct indices i_t, one for each integer t with 0 <= t <= r, all in [0, len(nums)), such that nums[i_t] mod value = t mod value for every such t.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_6 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    ¬ ∃ idx : Fin (r.val + 1).toNat → Fin nums.val.length,
        Function.Injective idx ∧
          ∀ t : Fin (r.val + 1).toNat,
            nmod (nums.val.get (idx t)).val value.val = nmod (t.val : ℤ) value.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), ¬ ∃ idx : Fin (r.val + 1).toNat → Fin nums.val.length,
        Function.Injective idx ∧
          ∀ t : Fin (r.val + 1).toNat,
            nmod (nums.val.get (idx t)).val value.val = nmod (t.val : ℤ) value.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, cnt(r mod value) = floor(r / value), where cnt(a) is the number of indices i with 0 <= i < len(nums) and nums[i] mod value = a, and floor(r / value) is integer division of the non-negative r by positive value.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_7 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r) :
    ((cnt nums.val value.val (nmod r.val value.val) : ℕ) : ℤ) = r.val / value.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r), ((cnt nums.val value.val (nmod r.val value.val) : ℕ) : ℤ) = r.val / value.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, if value = 1 then r = len(nums).
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_8 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hv : value.val = 1) :
    r.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hv : value.val = 1), r.val = (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, if no index i with 0 <= i < len(nums) satisfies nums[i] mod value = 0, then r = 0.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_9 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hzero : ∀ x ∈ nums.val, nmod x.val value.val ≠ 0) :
    r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hzero : ∀ x ∈ nums.val, nmod x.val value.val ≠ 0), r.val = 0) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, if len(nums) >= value and for every residue a with 0 <= a < value there is an index i with 0 <= i < len(nums) and nums[i] mod value = a, then r >= value.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_10 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hlen : value.val ≤ (nums.val.length : ℤ))
    (hall : ∀ a : ℤ, 0 ≤ a → a < value.val →
      ∃ i : Fin nums.val.length, nmod (nums.val.get i).val value.val = a) :
    value.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hlen : value.val ≤ (nums.val.length : ℤ))
    (hall : ∀ a : ℤ, 0 ≤ a → a < value.val →
      ∃ i : Fin nums.val.length, nmod (nums.val.get i).val value.val = a), value.val ≤ r.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, if value > 1 and every index i with 0 <= i < len(nums) satisfies nums[i] mod value = 0, then r = 1.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_11 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hv : 1 < value.val)
    (hzero : ∀ x ∈ nums.val, nmod x.val value.val = 0) :
    r.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hv : 1 < value.val)
    (hzero : ∀ x ∈ nums.val, nmod x.val value.val = 0), r.val = 1) := by
  sorry

/-- For any two arrays nums and nums2 satisfying the preconditions, if len(nums) = len(nums2) and for every residue a with 0 <= a < value the number of indices i with nums[i] mod value = a equals the number of indices i with nums2[i] mod value = a, then whenever find_smallest_integer(nums, value) returns r and find_smallest_integer(nums2, value) returns r2, we have r = r2.
  Preconditions: All arrays mentioned have length between 1 and 100000; value is between 1 and 100000; every array element is between -10^9 and 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_12 (nums nums2 : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hlen1' : 1 ≤ nums2.val.length) (hlen2' : nums2.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (helems2 : ∀ x ∈ nums2.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen : nums.val.length = nums2.val.length)
    (hcnt : ∀ a : ℤ, 0 ≤ a → a < value.val →
      cnt nums.val value.val a = cnt nums2.val value.val a)
    (r r2 : I64)
    (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hr2 : Aegis.FindSmallestInteger.find_smallest_integer nums2 value = Result.ok r2) :
    r = r2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums2 : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hlen1' : 1 ≤ nums2.val.length) (hlen2' : nums2.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (helems2 : ∀ x ∈ nums2.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hlen : nums.val.length = nums2.val.length)
    (hcnt : ∀ a : ℤ, 0 ≤ a → a < value.val →
      cnt nums.val value.val a = cnt nums2.val value.val a)
    (r r2 : I64)
    (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hr2 : Aegis.FindSmallestInteger.find_smallest_integer nums2 value = Result.ok r2), r = r2) := by
  sorry

/-- For any integer x with -10^9 <= x <= 10^9, let nums2 be the array obtained by appending x to nums. If len(nums) < 100000, then whenever find_smallest_integer(nums, value) returns r and find_smallest_integer(nums2, value) returns r2, we have r <= r2.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_13 (nums nums2 : Slice I64) (value x : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ y ∈ nums.val, -(1000000000 : ℤ) ≤ y.val ∧ y.val ≤ 1000000000)
    (hx : -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hnums2 : nums2.val = nums.val ++ [x])
    (hlt : nums.val.length < 100000)
    (r r2 : I64)
    (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hr2 : Aegis.FindSmallestInteger.find_smallest_integer nums2 value = Result.ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice I64) (value x : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ y ∈ nums.val, -(1000000000 : ℤ) ≤ y.val ∧ y.val ≤ 1000000000)
    (hx : -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hnums2 : nums2.val = nums.val ++ [x])
    (hlt : nums.val.length < 100000)
    (r r2 : I64)
    (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hr2 : Aegis.FindSmallestInteger.find_smallest_integer nums2 value = Result.ok r2), r.val ≤ r2.val) := by
  sorry

/-- Whenever find_smallest_integer(nums, value) returns a result r, if value > len(nums), then r is the least integer t with 0 <= t <= len(nums) such that either t = len(nums) or no index i with 0 <= i < len(nums) satisfies nums[i] mod value = t.
  Preconditions: len(nums) is between 1 and 100000; value is between 1 and 100000; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; mod denotes the non-negative remainder modulo value. -/
theorem spec_14 (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hgt : (nums.val.length : ℤ) < value.val) :
    IsLeast
      {t : ℤ | 0 ≤ t ∧ t ≤ (nums.val.length : ℤ) ∧
        (t = (nums.val.length : ℤ) ∨ ∀ y ∈ nums.val, nmod y.val value.val ≠ t)}
      r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (value : I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hvalue1 : 1 ≤ value.val) (hvalue2 : value.val ≤ 100000)
    (helems : ∀ x ∈ nums.val, -(1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (r : I64) (hr : Aegis.FindSmallestInteger.find_smallest_integer nums value = Result.ok r)
    (hgt : (nums.val.length : ℤ) < value.val), IsLeast
      {t : ℤ | 0 ≤ t ∧ t ≤ (nums.val.length : ℤ) ∧
        (t = (nums.val.length : ℤ) ∨ ∀ y ∈ nums.val, nmod y.val value.val ≠ t)}
      r.val) := by
  sorry

end AegisSpec.FindSmallestInteger
