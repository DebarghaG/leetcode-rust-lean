import Aegis.MaxNonOverlapping.Code.Funs

/-!
# Specifications of `Aegis.MaxNonOverlapping.max_non_overlapping`

LeetCode problem `maximum-number-of-non-overlapping-subarrays-with-sum-equals-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxNonOverlapping

def segSum (l : List Std.I64) (a b : Nat) : Int :=
  ((l.drop a).take (b - a)).map (fun x => x.val) |>.sum

def IsFamily (l : List Std.I64) (T : Int) (ivs : List (Nat × Nat)) : Prop :=
  ivs.Pairwise (fun p q => p.2 ≤ q.1) ∧
    ∀ p ∈ ivs, p.1 < p.2 ∧ p.2 ≤ l.length ∧ segSum l p.1 p.2 = T

noncomputable def maxCount (l : List Std.I64) (T : Int) : Nat := by
  classical
  exact Nat.findGreatest
    (fun m => ∃ ivs : List (Nat × Nat), ivs.length = m ∧ IsFamily l T ivs) l.length

def revList (l : List Std.I64) : List Std.I64 := l.reverse

def countEq (l : List Std.I64) (T : Int) : Nat := (l.filter (fun x => x.val = T)).length

def totalSum (l : List Std.I64) : Int := (l.map (fun x => x.val)).sum

/-- Whenever the function returns a result res, res equals the maximum size m of a family of intervals (l_0, r_0), ..., (l_{m-1}, r_{m-1}) such that 0 <= l_0 < r_0 <= l_1 < r_1 <= ... <= l_{m-1} < r_{m-1} <= len(nums) and, for every j with 0 <= j < m, the sum of nums[i] for l_j <= i < r_j equals target. The empty family with m = 0 is allowed. In other words, res is the maximum number of pairwise disjoint non-empty contiguous subarrays of nums whose sums are all equal to target.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val = (maxCount nums.val target.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val = (maxCount nums.val target.val : Int)) := by
  sorry

/-- For every such nums and target, the function returns a result res; it does not fail, panic, or overflow.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000) :
    ∃ res : Std.I64, Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000), ∃ res : Std.I64, Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) := by
  sorry

/-- Whenever the function returns a result res, 0 <= res <= len(nums).
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    0 ≤ res.val ∧ res.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), 0 ≤ res.val ∧ res.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result res, there exist res pairwise disjoint non-empty contiguous subarrays of nums, each of whose element sum equals target. For res = 0 this is the empty collection.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    ∃ ivs : List (Nat × Nat), IsFamily nums.val target.val ivs ∧
      res.val = (ivs.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), ∃ ivs : List (Nat × Nat), IsFamily nums.val target.val ivs ∧
      res.val = (ivs.length : Int)) := by
  sorry

/-- Whenever the function returns a result res, every collection of pairwise disjoint non-empty contiguous subarrays of nums whose element sums all equal target has size at most res. Equivalently, there is no such collection of size res + 1.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    ∀ ivs : List (Nat × Nat), IsFamily nums.val target.val ivs →
      (ivs.length : Int) ≤ res.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), ∀ ivs : List (Nat × Nat), IsFamily nums.val target.val ivs →
      (ivs.length : Int) ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res, res = 0 if and only if there is no pair (l, r) with 0 <= l < r <= len(nums) and the sum of nums[i] for l <= i < r equal to target.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val = 0 ↔
      ¬ ∃ l r : Nat, l < r ∧ r ≤ nums.val.length ∧ segSum nums.val l r = target.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val = 0 ↔
      ¬ ∃ l r : Nat, l < r ∧ r ≤ nums.val.length ∧ segSum nums.val l r = target.val) := by
  sorry

/-- Whenever the function returns a result res, res = len(nums) if and only if for every i with 0 <= i < len(nums), nums[i] = target.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val = (nums.val.length : Int) ↔ ∀ i ∈ nums.val, i.val = target.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val = (nums.val.length : Int) ↔ ∀ i ∈ nums.val, i.val = target.val) := by
  sorry

/-- Whenever the function returns a result res, res = 1 if nums[0] = target, and res = 0 otherwise.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, target is between 0 and 1000000 inclusive, and len(nums) = 1. -/
theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (hlen : nums.val.length = 1)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    ∀ a : Std.I64, nums.val = [a] →
      res.val = (if a.val = target.val then (1 : Int) else 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (hlen : nums.val.length = 1)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), ∀ a : Std.I64, nums.val = [a] →
      res.val = (if a.val = target.val then (1 : Int) else 0)) := by
  sorry

/-- Whenever the function returns a result res, res equals the number of indices i with 0 <= i < len(nums) and nums[i] = 0.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, target is between 0 and 1000000 inclusive, target = 0, and every nums[i] >= 0. -/
theorem spec_9 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (htarget : target.val = 0)
    (hnonneg : ∀ i ∈ nums.val, 0 ≤ i.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val = (countEq nums.val 0 : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (htarget : target.val = 0)
    (hnonneg : ∀ i ∈ nums.val, 0 ≤ i.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val = (countEq nums.val 0 : Int)) := by
  sorry

/-- Whenever the function returns a result res, res * target <= the sum of nums[i] over all i with 0 <= i < len(nums).
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, target is between 0 and 1000000 inclusive, target > 0, and every nums[i] >= 0. -/
theorem spec_10 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (htarget_pos : 0 < target.val)
    (hnonneg : ∀ i ∈ nums.val, 0 ≤ i.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val * target.val ≤ totalSum nums.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (htarget_pos : 0 < target.val)
    (hnonneg : ∀ i ∈ nums.val, 0 ≤ i.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val * target.val ≤ totalSum nums.val) := by
  sorry

/-- Whenever the function returns a result res, res is at least the number of indices i with 0 <= i < len(nums) and nums[i] = target.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_11 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    (countEq nums.val target.val : Int) ≤ res.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), (countEq nums.val target.val : Int) ≤ res.val) := by
  sorry

/-- Let rev(nums) be the array of length len(nums) with rev(nums)[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). Whenever the function returns a result res, the maximum number of pairwise disjoint non-empty contiguous subarrays of rev(nums) whose sums all equal target is also res.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_12 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    (maxCount (revList nums.val) target.val : Int) = res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), (maxCount (revList nums.val) target.val : Int) = res.val) := by
  sorry

/-- Let n = len(nums). For every integer k with 0 <= k <= n, if there is no pair (l, r) with 0 <= l < k < r <= n such that the sum of nums[i] for l <= i < r equals target, then whenever the function returns a result res, res = M(nums[0:k], target) + M(nums[k:n], target), where M(x, T) denotes the maximum number of pairwise disjoint non-empty contiguous subarrays of x whose sums all equal T.
  Preconditions: len(nums) is between 1 and 100000 inclusive, every nums[i] with 0 <= i < len(nums) is between -10000 and 10000 inclusive, and target is between 0 and 1000000 inclusive. -/
theorem spec_13 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (k : Nat) (hk : k ≤ nums.val.length)
    (hcut : ¬ ∃ l r : Nat, l < k ∧ k < r ∧ r ≤ nums.val.length ∧
      segSum nums.val l r = target.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res) :
    res.val = (maxCount (nums.val.take k) target.val : Int) +
      (maxCount (nums.val.drop k) target.val : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (helem : ∀ i ∈ nums.val, -10000 ≤ i.val ∧ i.val ≤ 10000)
    (htarget_lo : 0 ≤ target.val) (htarget_hi : target.val ≤ 1000000)
    (k : Nat) (hk : k ≤ nums.val.length)
    (hcut : ¬ ∃ l r : Nat, l < k ∧ k < r ∧ r ≤ nums.val.length ∧
      segSum nums.val l r = target.val)
    (res : Std.I64) (hres : Aegis.MaxNonOverlapping.max_non_overlapping nums target = ok res), res.val = (maxCount (nums.val.take k) target.val : Int) +
      (maxCount (nums.val.drop k) target.val : Int)) := by
  sorry

end AegisSpec.MaxNonOverlapping
