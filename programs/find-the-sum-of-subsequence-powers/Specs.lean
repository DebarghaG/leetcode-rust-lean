import Aegis.SumOfPowers.Code.Funs

/-!
# Specifications of `Aegis.SumOfPowers.sum_of_powers`

LeetCode problem `find-the-sum-of-subsequence-powers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumOfPowers

def MD : ℤ := 1000000007

def values (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def gap (a b : ℤ) : ℤ := ((a - b).natAbs : ℤ)

noncomputable def distSet (l : List ℤ) (I : Finset ℕ) : Finset ℤ :=
  ((I.product I).filter (fun p : ℕ × ℕ => p.1 < p.2)).image
    (fun p : ℕ × ℕ => gap (l.getD p.1 0) (l.getD p.2 0))

noncomputable def minGapOn (l : List ℤ) (I : Finset ℕ) : ℤ :=
  if h : (distSet l I).Nonempty then (distSet l I).min' h else 0

noncomputable def subsetMinGapSum (l : List ℤ) (k : ℕ) : ℤ :=
  ((Finset.range l.length).powersetCard k).sum (fun I => minGapOn l I)

noncomputable def allPairGapSum (l : List ℤ) : ℤ :=
  (Finset.range l.length).sum (fun i =>
    ((Finset.range l.length).filter (fun j => i < j)).sum (fun j =>
      gap (l.getD i 0) (l.getD j 0)))

noncomputable def dropOneMinGapSum (l : List ℤ) : ℤ :=
  (Finset.range l.length).sum (fun i => minGapOn l ((Finset.range l.length).erase i))

def InRange (s : Slice I64) : Prop :=
  ∀ x ∈ s.val, -100000000 ≤ x.val ∧ x.val ≤ 100000000

/-- Whenever sum_of_powers(nums, k) returns a result r, r is the unique integer such that 0 <= r < 1000000007 and r ≡ S (mod 1000000007), where S = sum over all subsets I of {0,1,...,n-1} with |I| = k of min{ |nums[i] - nums[j]| : i, j ∈ I, i ≠ j }.
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. -/
theorem spec_1 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums) :
    ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (subsetMinGapSum (values nums) k.val.toNat) ∧
        ∀ m : ℤ, 0 ≤ m → m < MD →
          Int.ModEq MD m (subsetMinGapSum (values nums) k.val.toNat) → m = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums), ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (subsetMinGapSum (values nums) k.val.toNat) ∧
        ∀ m : ℤ, 0 ≤ m → m < MD →
          Int.ModEq MD m (subsetMinGapSum (values nums) k.val.toNat) → m = r.val)) := by
  sorry

/-- For all nums and k satisfying the preconditions, sum_of_powers(nums, k) returns a result r (i.e., it does not fail).
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. -/
theorem spec_2 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums) :
    ∃ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums), ∃ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r) := by
  sorry

/-- sum_of_powers(nums1, k) and sum_of_powers(nums2, k) either both fail, or both return the same result r.
  Preconditions: nums1 and nums2 are slices of i64 with equal length n, 2 <= n <= 50. They are permutations of each other: there exists a bijection π : {0,...,n-1} -> {0,...,n-1} such that nums1[i] = nums2[π(i)] for all i. k is an i64 with 2 <= k <= n. All elements of both slices are in [-100000000, 100000000]. -/
theorem spec_3 (nums1 nums2 : Slice I64) (k : I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 2 ≤ nums1.val.length) (hn_hi : nums1.val.length ≤ 50)
    (hperm : nums1.val.Perm nums2.val)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums1.val.length : ℤ))
    (hb1 : InRange nums1) (hb2 : InRange nums2) :
    (∃ e1 e2 : Aeneas.Std.Error,
        Aegis.SumOfPowers.sum_of_powers nums1 k = Result.fail e1 ∧
        Aegis.SumOfPowers.sum_of_powers nums2 k = Result.fail e2) ∨
    (∃ r : I64,
        Aegis.SumOfPowers.sum_of_powers nums1 k = ok r ∧
        Aegis.SumOfPowers.sum_of_powers nums2 k = ok r) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hlen : nums1.val.length = nums2.val.length)
    (hn_lo : 2 ≤ nums1.val.length) (hn_hi : nums1.val.length ≤ 50)
    (hperm : nums1.val.Perm nums2.val)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums1.val.length : ℤ))
    (hb1 : InRange nums1) (hb2 : InRange nums2), (∃ e1 e2 : Aeneas.Std.Error,
        Aegis.SumOfPowers.sum_of_powers nums1 k = Result.fail e1 ∧
        Aegis.SumOfPowers.sum_of_powers nums2 k = Result.fail e2) ∨
    (∃ r : I64,
        Aegis.SumOfPowers.sum_of_powers nums1 k = ok r ∧
        Aegis.SumOfPowers.sum_of_powers nums2 k = ok r)) := by
  sorry

/-- When k = n, the result r (if returned) satisfies r ≡ min{ |nums[i] - nums[j]| : 0 <= i < j < n } (mod 1000000007) and 0 <= r < 1000000007.
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. Additionally, k = n. -/
theorem spec_4 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hkn : k.val = (nums.val.length : ℤ)) :
    ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (minGapOn (values nums) (Finset.range (values nums).length))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hkn : k.val = (nums.val.length : ℤ)), ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (minGapOn (values nums) (Finset.range (values nums).length)))) := by
  sorry

/-- The result r (if returned) satisfies r ≡ sum_{0 <= i < j < n} |nums[i] - nums[j]| (mod 1000000007) and 0 <= r < 1000000007.
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. Additionally, k = 2. -/
theorem spec_5 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hk2 : k.val = 2) :
    ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (allPairGapSum (values nums))) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hk2 : k.val = 2), ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (allPairGapSum (values nums)))) := by
  sorry

/-- sum_of_powers(nums, k) and sum_of_powers(nums', k) either both fail, or both return the same result r.
  Preconditions: nums is a slice of i64, n = len(nums), 2 <= n <= 50. k is an i64 with 2 <= k <= n. All nums[i] in [-100000000, 100000000]. Let c be an integer such that -100000000 <= nums[i] + c <= 100000000 for all i. Let nums' be the slice defined by nums'[i] = nums[i] + c. -/
theorem spec_6 (nums nums' : Slice I64) (c : ℤ) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hc : ∀ x ∈ nums.val, -100000000 ≤ x.val + c ∧ x.val + c ≤ 100000000)
    (hshift : values nums' = (values nums).map (fun v => v + c)) :
    (∃ e1 e2 : Aeneas.Std.Error,
        Aegis.SumOfPowers.sum_of_powers nums k = Result.fail e1 ∧
        Aegis.SumOfPowers.sum_of_powers nums' k = Result.fail e2) ∨
    (∃ r : I64,
        Aegis.SumOfPowers.sum_of_powers nums k = ok r ∧
        Aegis.SumOfPowers.sum_of_powers nums' k = ok r) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice I64) (c : ℤ) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hc : ∀ x ∈ nums.val, -100000000 ≤ x.val + c ∧ x.val + c ≤ 100000000)
    (hshift : values nums' = (values nums).map (fun v => v + c)), (∃ e1 e2 : Aeneas.Std.Error,
        Aegis.SumOfPowers.sum_of_powers nums k = Result.fail e1 ∧
        Aegis.SumOfPowers.sum_of_powers nums' k = Result.fail e2) ∨
    (∃ r : I64,
        Aegis.SumOfPowers.sum_of_powers nums k = ok r ∧
        Aegis.SumOfPowers.sum_of_powers nums' k = ok r)) := by
  sorry

/-- The result r (if returned) is 0.
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. Additionally, the number of distinct values in nums is less than k. -/
theorem spec_7 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hdistinct : ((nums.val.dedup.length : ℕ) : ℤ) < k.val) :
    ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hdistinct : ((nums.val.dedup.length : ℕ) : ℤ) < k.val), ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r → r.val = 0) := by
  sorry

/-- If both calls return results, then r' ≡ c * r (mod 1000000007).
  Preconditions: nums is a slice of i64, n = len(nums), 2 <= n <= 50. k is an i64 with 2 <= k <= n. All nums[i] in [-100000000, 100000000]. Let c be a positive integer such that c * nums[i] is within [-100000000, 100000000] for all i. Let nums' be the slice defined by nums'[i] = c * nums[i]. Let r be the result for nums (if it returns) and r' be the result for nums' (if it returns). -/
theorem spec_8 (nums nums' : Slice I64) (c : ℤ) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hc_pos : 0 < c)
    (hc : ∀ x ∈ nums.val, -100000000 ≤ c * x.val ∧ c * x.val ≤ 100000000)
    (hscale : values nums' = (values nums).map (fun v => c * v)) :
    ∀ r r' : I64,
      Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      Aegis.SumOfPowers.sum_of_powers nums' k = ok r' →
      Int.ModEq MD r'.val (c * r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice I64) (c : ℤ) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hc_pos : 0 < c)
    (hc : ∀ x ∈ nums.val, -100000000 ≤ c * x.val ∧ c * x.val ≤ 100000000)
    (hscale : values nums' = (values nums).map (fun v => c * v)), ∀ r r' : I64,
      Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      Aegis.SumOfPowers.sum_of_powers nums' k = ok r' →
      Int.ModEq MD r'.val (c * r.val)) := by
  sorry

/-- The result r (if returned) satisfies r ≡ sum_{i=0}^{n-1} min{ |nums[a] - nums[b]| : 0 <= a < b < n, a ≠ i, b ≠ i } (mod 1000000007) and 0 <= r < 1000000007.
  Preconditions: nums is a slice of i64, k is an i64. Let n = len(nums). Assume 2 <= n <= 50, 2 <= k <= n, and -100000000 <= nums[i] <= 100000000 for all 0 <= i < n. Additionally, k = n - 1 (which implies n >= 3). -/
theorem spec_9 (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hkn : k.val = (nums.val.length : ℤ) - 1) :
    ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (dropOneMinGapSum (values nums))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64)
    (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 50)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
    (hb : InRange nums)
    (hkn : k.val = (nums.val.length : ℤ) - 1), ∀ r : I64, Aegis.SumOfPowers.sum_of_powers nums k = ok r →
      (0 ≤ r.val ∧ r.val < MD ∧
        Int.ModEq MD r.val (dropOneMinGapSum (values nums)))) := by
  sorry

end AegisSpec.SumOfPowers
