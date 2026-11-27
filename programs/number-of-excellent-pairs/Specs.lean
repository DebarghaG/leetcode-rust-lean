import Aegis.CountExcellentPairs.Code.Funs

/-!
# Specifications of `Aegis.CountExcellentPairs.count_excellent_pairs`

LeetCode problem `number-of-excellent-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountExcellentPairs (count_excellent_pairs)

set_option autoImplicit false

namespace AegisSpec.CountExcellentPairs

def natPopcount (x : ℕ) : ℕ := x.bits.count true

def pc (x : ℤ) : ℕ := natPopcount x.natAbs

def values (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def distinctVals (nums : Slice Std.I64) : Finset ℤ := (values nums).toFinset

abbrev excellent (k : ℤ) (a b : ℤ) : Prop := k ≤ (pc a : ℤ) + (pc b : ℤ)

def countOrderedPairs (S : Finset ℤ) (k : ℤ) : ℕ :=
  ((S ×ˢ S).filter (fun p => excellent k p.1 p.2)).card

def countSelfExcellent (S : Finset ℤ) (k : ℤ) : ℕ :=
  (S.filter (fun v => k ≤ 2 * (pc v : ℤ))).card

def countUnorderedPairs (S : Finset ℤ) (k : ℤ) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ excellent k p.1 p.2)).card

def countWithPc (S : Finset ℤ) (t : ℕ) : ℕ := (S.filter (fun v => pc v = t)).card

def pcPairSum (S : Finset ℤ) (k : ℤ) : ℕ :=
  ((Finset.range 64 ×ˢ Finset.range 64).filter
      (fun p : ℕ × ℕ => k ≤ (p.1 : ℤ) + (p.2 : ℤ))).sum
    (fun p => countWithPc S p.1 * countWithPc S p.2)

def minPc (nums : Slice Std.I64) : ℕ :=
  if h : (distinctVals nums).Nonempty then
    ((distinctVals nums).image pc).min' (h.image pc)
  else 0

def maxPc (nums : Slice Std.I64) : ℕ :=
  if h : (distinctVals nums).Nonempty then
    ((distinctVals nums).image pc).max' (h.image pc)
  else 0

/-- Whenever the function returns a result r, r is exactly the number of ordered pairs (a,b) such that a occurs as a value in nums, b occurs as a value in nums, and pc(a OR b) + pc(a AND b) >= k. Here pc(x) is the number of set bits in the binary representation of x. Pairs are ordered: (a,b) and (b,a) are distinct when a != b, while (a,a) is included exactly once for each value a that occurs in nums. Multiplicities in nums are ignored: a value occurring one or more times is available once as a possible component value. Equivalently, because pc(a OR b) + pc(a AND b) = pc(a) + pc(b) for nonnegative a and b, the condition is pc(a) + pc(b) >= k.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = (countOrderedPairs (distinctVals nums) k.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = (countOrderedPairs (distinctVals nums) k.val : ℤ)) := by
  sorry

/-- The function returns a result (it does not fail, overflow, panic, or access outside the slice) for every input satisfying the preconditions; in particular, the returned value is a valid 64-bit signed integer.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60) :
    ∃ r : Std.I64, count_excellent_pairs nums k = ok r ∧
      -(2 ^ 63 : ℤ) ≤ r.val ∧ r.val < 2 ^ 63 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60), ∃ r : Std.I64, count_excellent_pairs nums k = ok r ∧
      -(2 ^ 63 : ℤ) ≤ r.val ∧ r.val < 2 ^ 63) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= d*d, where d is the number of distinct values occurring in nums.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val ≤ ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val ≤ ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ)) := by
  sorry

/-- Let D be the set of distinct values occurring in nums and let m = min {pc(v) | v in D}. For any input satisfying the preconditions, if k <= 2*m, then whenever the function returns a result r, r = d*d, where d = |D|.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hk_le : k.val ≤ 2 * (minPc nums : ℤ))
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hk_le : k.val ≤ 2 * (minPc nums : ℤ))
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ)) := by
  sorry

/-- Let D be the set of distinct values occurring in nums and let M = max {pc(v) | v in D}. For any input satisfying the preconditions, if k > 2*M, then whenever the function returns a result r, r = 0.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hk_gt : 2 * (maxPc nums : ℤ) < k.val)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hk_gt : 2 * (maxPc nums : ℤ) < k.val)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = 0) := by
  sorry

/-- If all entries of nums are equal to a single value v (that is, nums[i] = v for every i with 0 <= i < len(nums)), then whenever the function returns a result r, r = 1 if 2*pc(v) >= k and r = 0 otherwise.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (v : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hconst : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = v)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = if 2 * (pc v : ℤ) ≥ k.val then 1 else 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (v : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hconst : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = v)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = if 2 * (pc v : ℤ) ≥ k.val then 1 else 0) := by
  sorry

/-- Let D be the set of distinct values occurring in nums and D2 the set of distinct values occurring in nums2. If D = D2, then whenever count_excellent_pairs(nums,k) returns r and count_excellent_pairs(nums2,k) returns r2, we have r = r2.
  Preconditions: nums and nums2 are slices each satisfying: len at least 1 and at most 100000; every element between 1 and 1000000000; and 1 <= k <= 60. -/
theorem spec_8 (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hsame : distinctVals nums = distinctVals nums2)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hsame : distinctVals nums = distinctVals nums2)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2), r.val = r2.val) := by
  sorry

/-- Let D be the set of distinct values occurring in nums and D2 the set of distinct values occurring in nums2. If D is a subset of D2, then whenever count_excellent_pairs(nums,k) returns r and count_excellent_pairs(nums2,k) returns r2, we have r <= r2.
  Preconditions: nums and nums2 are slices each satisfying: len at least 1 and at most 100000; every element between 1 and 1000000000; and 1 <= k <= 60. -/
theorem spec_9 (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hsub : distinctVals nums ⊆ distinctVals nums2)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hsub : distinctVals nums ⊆ distinctVals nums2)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2), r.val ≤ r2.val) := by
  sorry

/-- Whenever count_excellent_pairs(nums,k1) returns r1 and count_excellent_pairs(nums,k2) returns r2, we have r2 <= r1.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k1 <= k2 <= 60. -/
theorem spec_10 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk1_lb : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ 60)
    {r1 r2 : Std.I64} (hr1 : count_excellent_pairs nums k1 = ok r1)
    (hr2 : count_excellent_pairs nums k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk1_lb : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_ub : k2.val ≤ 60)
    {r1 r2 : Std.I64} (hr1 : count_excellent_pairs nums k1 = ok r1)
    (hr2 : count_excellent_pairs nums k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Let D be the set of distinct values occurring in nums, and let h be the number of v in D such that 2*pc(v) >= k. Whenever the function returns a result r, r >= h*h.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    (countSelfExcellent (distinctVals nums) k.val : ℤ) *
        (countSelfExcellent (distinctVals nums) k.val : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), (countSelfExcellent (distinctVals nums) k.val : ℤ) *
        (countSelfExcellent (distinctVals nums) k.val : ℤ) ≤ r.val) := by
  sorry

/-- Let D be the set of distinct values occurring in nums. Let d_eq be the number of v in D with 2*pc(v) >= k. Let d_neq be the number of unordered two-element subsets {a,b} of D (so a != b) such that pc(a)+pc(b) >= k. Whenever the function returns a result r, r = d_eq + 2*d_neq.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = (countSelfExcellent (distinctVals nums) k.val : ℤ) +
      2 * (countUnorderedPairs (distinctVals nums) k.val : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = (countSelfExcellent (distinctVals nums) k.val : ℤ) +
      2 * (countUnorderedPairs (distinctVals nums) k.val : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every value a occurring in nums and every value b occurring in nums, pc(a OR b) + pc(a AND b) < k (equivalently pc(a)+pc(b) < k).
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = 0 ↔ ∀ a ∈ distinctVals nums, ∀ b ∈ distinctVals nums,
      (pc a : ℤ) + (pc b : ℤ) < k.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = 0 ↔ ∀ a ∈ distinctVals nums, ∀ b ∈ distinctVals nums,
      (pc a : ℤ) + (pc b : ℤ) < k.val) := by
  sorry

/-- Let c_t be the number of distinct values v occurring in nums with pc(v) = t, for t = 0..63. Whenever the function returns a result r, r = sum over all pairs (i,j) with 0 <= i <= 63, 0 <= j <= 63 and i + j >= k of c_i * c_j.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    r.val = (pcPairSum (distinctVals nums) k.val : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), r.val = (pcPairSum (distinctVals nums) k.val : ℤ)) := by
  sorry

/-- Let D be the set of distinct values occurring in nums and D2 the set of distinct values occurring in nums2. If the multisets of popcounts {pc(v) | v in D} and {pc(v) | v in D2} are equal, then whenever count_excellent_pairs(nums,k) returns r and count_excellent_pairs(nums2,k) returns r2, we have r = r2.
  Preconditions: nums and nums2 are slices each satisfying: len at least 1 and at most 100000; every element between 1 and 1000000000; and the same k with 1 <= k <= 60. -/
theorem spec_15 (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hpc : (distinctVals nums).val.map pc = (distinctVals nums2).val.map pc)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
    (hbound2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    (hpc : (distinctVals nums).val.map pc = (distinctVals nums2).val.map pc)
    {r r2 : Std.I64} (hr : count_excellent_pairs nums k = ok r)
    (hr2 : count_excellent_pairs nums2 k = ok r2), r.val = r2.val) := by
  sorry

/-- Let D be the set of distinct values occurring in nums, let d = |D| and let m = min {pc(v) | v in D}. Whenever the function returns a result r, r = d*d if and only if k <= 2*m.
  Preconditions: len(nums) is at least 1 and at most 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= k <= 60. -/
theorem spec_16 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r) :
    (r.val = ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ) ↔
      k.val ≤ 2 * (minPc nums : ℤ)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hbound : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 60)
    {r : Std.I64} (hr : count_excellent_pairs nums k = ok r), (r.val = ((distinctVals nums).card : ℤ) * ((distinctVals nums).card : ℤ) ↔
      k.val ≤ 2 * (minPc nums : ℤ))) := by
  sorry

end AegisSpec.CountExcellentPairs
