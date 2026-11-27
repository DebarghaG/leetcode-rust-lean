import Aegis.CountPartitions.Code.Funs

/-!
# Specifications of `Aegis.CountPartitions.count_partitions`

LeetCode problem `number-of-great-partitions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountPartitions

  def modulus : ℤ := 1000000007

  def valueBound : ℤ := 1000000000

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def subSum (x : List ℤ) (S : Finset (Fin x.length)) : ℤ := ∑ i ∈ S, x.get i

  def greatSubsets (x : List ℤ) (k : ℤ) : Finset (Finset (Fin x.length)) :=
    Finset.univ.filter (fun S => k ≤ subSum x S ∧ k ≤ x.sum - subSum x S)

  def greatCount (x : List ℤ) (k : ℤ) : ℕ := (greatSubsets x k).card

  def greatSubsetsHead (x : List ℤ) (k : ℤ) (h : 0 < x.length) :
      Finset (Finset (Fin x.length)) :=
    Finset.univ.filter
      (fun S => (⟨0, h⟩ : Fin x.length) ∈ S ∧ k ≤ subSum x S ∧ k ≤ x.sum - subSum x S)

  def greatCountHead (x : List ℤ) (k : ℤ) (h : 0 < x.length) : ℕ :=
    (greatSubsetsHead x k h).card

  def sumEqSubsets (x : List ℤ) (k : ℤ) : Finset (Finset (Fin x.length)) :=
    Finset.univ.filter (fun S => subSum x S = k)

  def sumEqCount (x : List ℤ) (k : ℤ) : ℕ := (sumEqSubsets x k).card

  def smallSubsets (x : List ℤ) (k : ℤ) : Finset (Finset (Fin x.length)) :=
    Finset.univ.filter (fun S => subSum x S < k)

  def smallCount (x : List ℤ) (k : ℤ) : ℕ := (smallSubsets x k).card

  /-- Whenever the function returns a result r, r is the unique integer such that 0 <= r < 1000000007 and r is congruent modulo 1000000007 to G, where G is the ordinary number of subsets S of {0,...,n-1} satisfying (sum_{i in S} nums[i]) >= k and (T - sum_{i in S} nums[i]) >= k. Equivalently, identifying S with the first group and its complement with the second group, G is the number of ordered two-group partitions of the indices in which each group has sum at least k.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), 0 ≤ r.val ∧ r.val < modulus ∧
          r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus]) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail because of arithmetic overflow, an out-of-bounds access, or a panic.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound) :
      ∃ r : Std.I64, Aegis.CountPartitions.count_partitions nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound), ∃ r : Std.I64, Aegis.CountPartitions.count_partitions nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = 0. Indeed, if both group sums were at least k, the total sum T would be at least 2*k, so no great partition exists.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also T < 2*k. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hT : (vals nums).sum < 2 * k.val)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hT : (vals nums).sum < 2 * k.val)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r is the residue modulo 1000000007 of H, where H is the number of subsets S of {0,...,n-1} with sum_{i in S} nums[i] = k. Under T = 2*k, a partition is great exactly when the first group has sum k.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also T = 2*k. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hT : (vals nums).sum = 2 * k.val)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val ≡ (sumEqCount (vals nums) k.val : ℤ) [ZMOD modulus] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hT : (vals nums).sum = 2 * k.val)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val ≡ (sumEqCount (vals nums) k.val : ℤ) [ZMOD modulus]) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 1000000007 to 2^n - 2. Equivalently, the great partitions are exactly the ordered assignments in which both groups are nonempty.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also nums[i] >= k for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hlarge : ∀ x ∈ nums.val, k.val ≤ x.val)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val ≡ ((2 : ℤ) ^ (vals nums).length - 2) [ZMOD modulus] := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hlarge : ∀ x ∈ nums.val, k.val ≤ x.val)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val ≡ ((2 : ℤ) ^ (vals nums).length - 2) [ZMOD modulus]) := by
    sorry

  /-- Whenever the function returns a result r, r = 0. The only element cannot be placed in both groups, so one of the two groups is empty and has sum 0 < k.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also n = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hn : nums.val.length = 1)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hn : nums.val.length = 1)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 if nums[0] >= k and nums[1] >= k, and r = 0 otherwise. For two elements, the only possible great partitions are the two assignments placing one element in each group, and these are great exactly when both singleton sums are at least k.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also n = 2. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hn : nums.val.length = 2)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val = (if k.val ≤ (nums.val.get ⟨0, by omega⟩).val ∧
                  k.val ≤ (nums.val.get ⟨1, by omega⟩).val then 2 else 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hn : nums.val.length = 2)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val = (if k.val ≤ (nums.val.get ⟨0, by omega⟩).val ∧
                    k.val ≤ (nums.val.get ⟨1, by omega⟩).val then 2 else 0)) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 1000000007 to 2*G0, where G0 is the number of subsets S of {0,...,n-1} such that 0 is in S, sum_{i in S} nums[i] >= k, and T - sum_{i in S} nums[i] >= k. The great partitions are paired by complementation, and exactly one partition in each pair puts index 0 in the first group.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val ≡ (2 * (greatCountHead (vals nums) k.val (by simp [vals]; omega) : ℤ))
        [ZMOD modulus] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val ≡ (2 * (greatCountHead (vals nums) k.val (by simp [vals]; omega) : ℤ))
          [ZMOD modulus]) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 1000000007 to 2^n - 2*B, where B is the number of subsets S of {0,...,n-1} with sum_{i in S} nums[i] < k. The subsets failing the first-group condition and those failing the second-group condition are disjoint and are exchanged by complementation, each family having size B.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume also T >= 2*k. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hT : 2 * k.val ≤ (vals nums).sum)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val ≡ ((2 : ℤ) ^ (vals nums).length - 2 * (smallCount (vals nums) k.val : ℤ))
        [ZMOD modulus] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hT : 2 * k.val ≤ (vals nums).sum)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val ≡ ((2 : ℤ) ^ (vals nums).length - 2 * (smallCount (vals nums) k.val : ℤ))
          [ZMOD modulus]) := by
    sorry

  /-- Whenever count_partitions(nums, k) returns r and count_partitions(nums', k) returns r', we have r = r'. The number of great partitions depends only on the multiset of values, not on their order.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Let nums' be any slice of length n that is a permutation of nums, i.e. there is a bijection p on {0,...,n-1} with nums'[i] = nums[p(i)] for every i, and assume also 1 <= nums'[i] <= 1000000000 for every i. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hperm : (vals nums').Perm (vals nums))
      (r r' : Std.I64)
      (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
      (hr' : Aegis.CountPartitions.count_partitions nums' k = ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hperm : (vals nums').Perm (vals nums))
        (r r' : Std.I64)
        (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
        (hr' : Aegis.CountPartitions.count_partitions nums' k = ok r'), r = r') := by
    sorry

  /-- Whenever count_partitions(nums, k) returns r and count_partitions(nums', k') returns r', we have r = r'. Multiplying every value and the threshold by the same positive integer preserves all subset-sum inequalities against k.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Let c be a positive integer, let nums' be a slice with nums'[i] = c * nums[i] for every i, and let k' = c * k. Assume 1 <= nums'[i] <= 1000000000 for every i and 1 <= k' <= 1000. -/
  theorem spec_11 (nums nums' : Slice Std.I64) (k k' : Std.I64) (c : ℤ)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hc : 0 < c)
      (hval : vals nums' = (vals nums).map (fun x => c * x))
      (hscale : k'.val = c * k.val)
      (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 1000)
      (r r' : Std.I64)
      (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
      (hr' : Aegis.CountPartitions.count_partitions nums' k' = ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k k' : Std.I64) (c : ℤ)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hc : 0 < c)
        (hval : vals nums' = (vals nums).map (fun x => c * x))
        (hscale : k'.val = c * k.val)
        (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 1000)
        (r r' : Std.I64)
        (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
        (hr' : Aegis.CountPartitions.count_partitions nums' k' = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 1000000007 to G, where G is the number of subsets S of {0,...,n-1} satisfying (sum_{j in S} nums[j]) >= k and (T - sum_{j in S} nums[j]) >= k, and moreover G >= 2. In particular, the partition with first group {i} and the partition with first group the complement of {i} are two distinct great partitions.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < n. Assume there exists an index i with 0 <= i < n such that nums[i] >= k and T - nums[i] >= k. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (i : ℕ) (hi : i < nums.val.length)
      (hw : k.val ≤ (nums.val.get ⟨i, hi⟩).val ∧
              k.val ≤ (vals nums).sum - (nums.val.get ⟨i, hi⟩).val)
      (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r) :
      r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus] ∧
        2 ≤ greatCount (vals nums) k.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (i : ℕ) (hi : i < nums.val.length)
        (hw : k.val ≤ (nums.val.get ⟨i, hi⟩).val ∧
                k.val ≤ (vals nums).sum - (nums.val.get ⟨i, hi⟩).val)
        (r : Std.I64) (hr : Aegis.CountPartitions.count_partitions nums k = ok r), r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus] ∧
          2 ≤ greatCount (vals nums) k.val) := by
    sorry

  /-- Whenever count_partitions(nums, k1) returns r1 and count_partitions(nums, k2) returns r2, we have r1 congruent to G_1 modulo 1000000007, r2 congruent to G_2 modulo 1000000007, and G_1 >= G_2. Indeed, every subset satisfying both inequalities for k2 also satisfies both inequalities for k1.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k1 <= k2 <= 1000, and 1 <= nums[i] <= 1000000000 for every i. For j in {1,2}, let G_j be the ordinary number of subsets S of {0,...,n-1} such that sum_{i in S} nums[i] >= k_j and T - sum_{i in S} nums[i] >= k_j. -/
  theorem spec_13 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (r1 r2 : Std.I64)
      (hr1 : Aegis.CountPartitions.count_partitions nums k1 = ok r1)
      (hr2 : Aegis.CountPartitions.count_partitions nums k2 = ok r2) :
      r1.val ≡ (greatCount (vals nums) k1.val : ℤ) [ZMOD modulus] ∧
        r2.val ≡ (greatCount (vals nums) k2.val : ℤ) [ZMOD modulus] ∧
        greatCount (vals nums) k2.val ≤ greatCount (vals nums) k1.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (r1 r2 : Std.I64)
        (hr1 : Aegis.CountPartitions.count_partitions nums k1 = ok r1)
        (hr2 : Aegis.CountPartitions.count_partitions nums k2 = ok r2), r1.val ≡ (greatCount (vals nums) k1.val : ℤ) [ZMOD modulus] ∧
          r2.val ≡ (greatCount (vals nums) k2.val : ℤ) [ZMOD modulus] ∧
          greatCount (vals nums) k2.val ≤ greatCount (vals nums) k1.val) := by
    sorry

  /-- Whenever count_partitions(nums, k) returns r and count_partitions(nums', k) returns r', we have r congruent to G modulo 1000000007, r' congruent to G' modulo 1000000007, and G' >= G. For every subset S, sum_{i in S} nums'[i] >= sum_{i in S} nums[i] and T' - sum_{i in S} nums'[i] >= T - sum_{i in S} nums[i], so any great partition remains great after increasing values.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 1 <= n <= 1000, 1 <= k <= 1000, and 1 <= nums[i] <= 1000000000 for every i. Let nums' be a slice of length n with 1 <= nums[i] <= nums'[i] <= 1000000000 for every i, and let T' = sum_{i=0}^{n-1} nums'[i]. Let G be the ordinary number of great subsets for nums and k, and G' the ordinary number of great subsets for nums' and k. -/
  theorem spec_14 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
      (hle : List.Forall₂ (fun a b => a ≤ b) (vals nums) (vals nums'))
      (r r' : Std.I64)
      (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
      (hr' : Aegis.CountPartitions.count_partitions nums' k = ok r') :
      r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus] ∧
        r'.val ≡ (greatCount (vals nums') k.val : ℤ) [ZMOD modulus] ∧
        greatCount (vals nums) k.val ≤ greatCount (vals nums') k.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hnums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ valueBound)
        (hle : List.Forall₂ (fun a b => a ≤ b) (vals nums) (vals nums'))
        (r r' : Std.I64)
        (hr : Aegis.CountPartitions.count_partitions nums k = ok r)
        (hr' : Aegis.CountPartitions.count_partitions nums' k = ok r'), r.val ≡ (greatCount (vals nums) k.val : ℤ) [ZMOD modulus] ∧
          r'.val ≡ (greatCount (vals nums') k.val : ℤ) [ZMOD modulus] ∧
          greatCount (vals nums) k.val ≤ greatCount (vals nums') k.val) := by
    sorry

  end AegisSpec.CountPartitions
