import Aegis.MinOperationsToMakeMedianK.Code.Funs

/-!
# Specifications of `Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k`

LeetCode problem `minimum-operations-to-make-median-of-array-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperationsToMakeMedianK

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def posPart (x : ℤ) : ℤ := if x > 0 then x else 0

def iabs (x : ℤ) : ℤ := if x ≥ 0 then x else -x

def sortedVals (l : List ℤ) : List ℤ := l.insertionSort (· ≤ ·)

def medianVal (l : List ℤ) : ℤ := (sortedVals l).getD (l.length / 2) 0

def sumDeficitFrom (k : ℤ) (l : List ℤ) (start : ℕ) : ℤ :=
  ((l.drop start).map (fun x => posPart (k - x))).sum

def sumExcessUpTo (k : ℤ) (l : List ℤ) (last : ℕ) : ℤ :=
  ((l.take (last + 1)).map (fun x => posPart (x - k))).sum

def l1Dist (b a : List ℤ) : ℤ := (b.zipWith (fun x y => iabs (x - y)) a).sum

def SameMultiset (l₁ l₂ : List ℤ) : Prop := l₁.Perm l₂

/-- Let n = len(nums), let a be the sequence obtained by sorting nums in non-decreasing order (so a[0] <= a[1] <= ... <= a[n-1]), and let m = n/2 with integer division (the upper median index). The function returns a result r (it does not fail) such that: if a[m] < k then r = sum_{i=m}^{n-1} max(0, k - a[i]); if a[m] = k then r = 0; if a[m] > k then r = sum_{i=0}^{m} max(0, a[i] - k). Here max(0, x) is x when x > 0 and 0 otherwise.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∃ r,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      (medianVal (vals nums) < k.val →
        r.val = sumDeficitFrom k.val (sortedVals (vals nums)) (nums.val.length / 2)) ∧
      (medianVal (vals nums) = k.val → r.val = 0) ∧
      (k.val < medianVal (vals nums) →
        r.val = sumExcessUpTo k.val (sortedVals (vals nums)) (nums.val.length / 2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∃ r,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      (medianVal (vals nums) < k.val →
        r.val = sumDeficitFrom k.val (sortedVals (vals nums)) (nums.val.length / 2)) ∧
      (medianVal (vals nums) = k.val → r.val = 0) ∧
      (k.val < medianVal (vals nums) →
        r.val = sumExcessUpTo k.val (sortedVals (vals nums)) (nums.val.length / 2))) := by
  sorry

/-- For every nums and k satisfying the preconditions, the function returns a result r (it does not fail, overflow, or panic).
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∃ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∃ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r) := by
  sorry

/-- Let a be the non-decreasing sorted version of nums and let m = len(nums)/2 with integer division. Whenever the function returns a result r, r = 0 if and only if a[m] = k, i.e. the median of nums is already exactly k.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      (r.val = 0 ↔ medianVal (vals nums) = k.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      (r.val = 0 ↔ medianVal (vals nums) = k.val)) := by
  sorry

/-- Let a be the non-decreasing sorted version of nums and let m = len(nums)/2 with integer division. Whenever the function returns a result r, r >= |a[m] - k|, where |x| is x if x >= 0 and -x otherwise.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      iabs (medianVal (vals nums) - k.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      iabs (medianVal (vals nums) - k.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{len(nums)-1} |nums[i] - k|.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      r.val ≤ ((vals nums).map (fun x => iabs (x - k.val))).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      r.val ≤ ((vals nums).map (fun x => iabs (x - k.val))).sum) := by
  sorry

/-- Let r be the result returned by the function on (nums, k) and let r' be the result returned on (ys, k). Then both calls return results and r = r'.
  Preconditions: nums and k satisfy 1 <= len(nums) <= 2*10^5, 1 <= nums[i] <= 10^9 for every i, and 1 <= k <= 10^9; ys is a list of integers with len(ys) = len(nums) and the same multiset of elements as nums. -/
theorem spec_6 (nums ys : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hys_len : ys.val.length = nums.val.length)
    (hys_mult : SameMultiset (vals ys) (vals nums)) :
    ∃ r r',
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k ys k = ok r' ∧
      r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums ys : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hys_len : ys.val.length = nums.val.length)
    (hys_mult : SameMultiset (vals ys) (vals nums)), ∃ r r',
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k ys k = ok r' ∧
      r = r') := by
  sorry

/-- Let r be the result returned by the function on (nums, k) and let r' be the result returned on the array obtained by adding c to every element of nums, together with k + c. Then both calls return results and r = r'.
  Preconditions: nums and k satisfy 1 <= len(nums) <= 2*10^5, 1 <= nums[i] <= 10^9 for every i, and 1 <= k <= 10^9; let c be an integer such that 1 <= nums[i] + c <= 10^9 for every i and 1 <= k + c <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hshift : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 10 ^ 9)
    (hshift_k : 1 ≤ k.val + c ∧ k.val + c ≤ 10 ^ 9) :
    ∀ (nums' : Slice Std.I64) (k' : Std.I64),
      vals nums' = (vals nums).map (fun x => x + c) → k'.val = k.val + c →
      ∃ r r',
        Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
        Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums' k' = ok r' ∧
        r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9)
    (hshift : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 10 ^ 9)
    (hshift_k : 1 ≤ k.val + c ∧ k.val + c ≤ 10 ^ 9), ∀ (nums' : Slice Std.I64) (k' : Std.I64),
      vals nums' = (vals nums).map (fun x => x + c) → k'.val = k.val + c →
      ∃ r r',
        Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
        Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums' k' = ok r' ∧
        r = r') := by
  sorry

/-- The function returns a result r and there exists an integer array b of length n = len(nums) such that: (1) if c is b sorted in non-decreasing order, then c[n/2] = k, using integer division for n/2; and (2) sum_{i=0}^{n-1} |b[i] - nums[i]| = r.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∃ r,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      ∃ b : List ℤ,
        b.length = nums.val.length ∧
        (sortedVals b).getD (nums.val.length / 2) 0 = k.val ∧
        l1Dist b (vals nums) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∃ r,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r ∧
      ∃ b : List ℤ,
        b.length = nums.val.length ∧
        (sortedVals b).getD (nums.val.length / 2) 0 = k.val ∧
        l1Dist b (vals nums) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer array b of length n = len(nums) whose non-decreasing sorted version c satisfies c[n/2] = k (with integer division for n/2), one has sum_{i=0}^{n-1} |b[i] - nums[i]| >= r.
  Preconditions: 1 <= len(nums) <= 2*10^5; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9) :
    ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      ∀ b : List ℤ,
        b.length = nums.val.length →
        (sortedVals b).getD (nums.val.length / 2) 0 = k.val →
        r.val ≤ l1Dist b (vals nums) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 10 ^ 9), ∀ r, Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k = ok r →
      ∀ b : List ℤ,
        b.length = nums.val.length →
        (sortedVals b).getD (nums.val.length / 2) 0 = k.val →
        r.val ≤ l1Dist b (vals nums)) := by
  sorry

/-- If a[m] <= k1 <= k2, and the function returns r1 on (nums, k1) and r2 on (nums, k2), then r1 <= r2.
  Preconditions: nums, k1, k2 satisfy 1 <= len(nums) <= 2*10^5, 1 <= nums[i] <= 10^9 for every i, and 1 <= k1 <= k2 <= 10^9; let a be the non-decreasing sorted version of nums and let m = len(nums)/2 with integer division. -/
theorem spec_10 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk1_pos : 1 ≤ k1.val) (hk2_le : k2.val ≤ 10 ^ 9)
    (hk_mono : k1.val ≤ k2.val)
    (hmedian_le : medianVal (vals nums) ≤ k1.val) :
    ∀ r1 r2,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k1 = ok r1 →
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk1_pos : 1 ≤ k1.val) (hk2_le : k2.val ≤ 10 ^ 9)
    (hk_mono : k1.val ≤ k2.val)
    (hmedian_le : medianVal (vals nums) ≤ k1.val), ∀ r1 r2,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k1 = ok r1 →
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If k1 <= k2 <= a[m], and the function returns r1 on (nums, k1) and r2 on (nums, k2), then r1 >= r2.
  Preconditions: nums, k1, k2 satisfy 1 <= len(nums) <= 2*10^5, 1 <= nums[i] <= 10^9 for every i, and 1 <= k1 <= k2 <= 10^9; let a be the non-decreasing sorted version of nums and let m = len(nums)/2 with integer division. -/
theorem spec_11 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk1_pos : 1 ≤ k1.val) (hk2_le : k2.val ≤ 10 ^ 9)
    (hk_mono : k1.val ≤ k2.val)
    (hmedian_ge : k2.val ≤ medianVal (vals nums)) :
    ∀ r1 r2,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k1 = ok r1 →
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k2 = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2 * 10 ^ 5)
    (hvals : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 10 ^ 9)
    (hk1_pos : 1 ≤ k1.val) (hk2_le : k2.val ≤ 10 ^ 9)
    (hk_mono : k1.val ≤ k2.val)
    (hmedian_ge : k2.val ≤ medianVal (vals nums)), ∀ r1 r2,
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k1 = ok r1 →
      Aegis.MinOperationsToMakeMedianK.min_operations_to_make_median_k nums k2 = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

end AegisSpec.MinOperationsToMakeMedianK
