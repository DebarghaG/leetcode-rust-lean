import Aegis.KSum.Code.Funs

/-!
# Specifications of `Aegis.KSum.k_sum`

LeetCode problem `find-the-k-sum-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.KSum

  namespace AegisSpec.KSum

  def asInts (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def listSum (l : List ℤ) : ℤ := l.sum

  def sumNeg (l : List ℤ) : ℤ := (l.filter (fun x => x < 0)).sum

  def sumPos (l : List ℤ) : ℤ := (l.filter (fun x => 0 < x)).sum

  def subseqSums (l : List ℤ) : List ℤ := l.sublists.map (fun s => s.sum)

  def countGt (l : List ℤ) (r : ℤ) : ℕ := (l.filter (fun x => r < x)).length

  def countGe (l : List ℤ) (r : ℤ) : ℕ := (l.filter (fun x => r ≤ x)).length

  def IsSubsetSum (l : List ℤ) (r : ℤ) : Prop := ∃ s ∈ l.sublists, s.sum = r

  def SameMultiset (l₁ l₂ : List ℤ) : Prop :=
    ∀ v : ℤ, l₁.countP (fun x => decide (x = v)) = l₂.countP (fun x => decide (x = v))

  def PointwiseLE (l₁ l₂ : List ℤ) : Prop := List.Forall₂ (fun a b => a ≤ b) l₁ l₂

  def DeleteOneZero (l l' : List ℤ) : Prop :=
    ∃ i, i < l.length ∧ l[i]? = some 0 ∧ l' = l.eraseIdx i

  /-- The function returns a result r, and r is the k-th largest element (1-indexed, counting multiplicity) of the multiset of all 2^n subsequence sums of nums, where the empty subsequence has sum 0. Equivalently: let S range over all subsets of {0, 1, ..., n-1} and write sum(S) = Σ_{i∈S} nums[i]. Then (a) the number of S with sum(S) > r is at most k-1, and (b) the number of S with sum(S) >= r is at least k.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). -/
  theorem spec_1 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length) :
      ∃ r : I64, k_sum nums k = ok r ∧
        (countGt (subseqSums (asInts nums)) r.val : ℤ) ≤ k.val - 1 ∧
        k.val ≤ (countGe (subseqSums (asInts nums)) r.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length), ∃ r : I64, k_sum nums k = ok r ∧
          (countGt (subseqSums (asInts nums)) r.val : ℤ) ≤ k.val - 1 ∧
          k.val ≤ (countGe (subseqSums (asInts nums)) r.val : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, panic, or out-of-bounds).
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). -/
  theorem spec_2 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length) :
      ∃ r : I64, k_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length), ∃ r : I64, k_sum nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, let sum_neg = Σ_{i: nums[i] < 0} nums[i] (0 if there are no negative elements) and sum_pos = Σ_{i: nums[i] > 0} nums[i] (0 if there are no positive elements). Then sum_neg <= r <= sum_pos.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). -/
  theorem spec_3 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length) :
      ∀ r : I64, k_sum nums k = ok r →
        sumNeg (asInts nums) ≤ r.val ∧ r.val ≤ sumPos (asInts nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length), ∀ r : I64, k_sum nums k = ok r →
          sumNeg (asInts nums) ≤ r.val ∧ r.val ≤ sumPos (asInts nums)) := by
    sorry

  /-- Whenever the function returns a result r, with k = 1, r equals sum_pos = Σ_{i: nums[i] > 0} nums[i] (0 if there are no positive elements).
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). Also k = 1. -/
  theorem spec_4 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hk_one : k.val = 1) :
      ∀ r : I64, k_sum nums k = ok r → r.val = sumPos (asInts nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hk_one : k.val = 1), ∀ r : I64, k_sum nums k = ok r → r.val = sumPos (asInts nums)) := by
    sorry

  /-- Whenever the function returns a result r, with k = 2^n, r equals sum_neg = Σ_{i: nums[i] < 0} nums[i] (0 if there are no negative elements).
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). Also k = 2^n (which forces n <= 10 because k <= 2000). -/
  theorem spec_5 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hk_all : k.val = 2 ^ nums.val.length) :
      ∀ r : I64, k_sum nums k = ok r → r.val = sumNeg (asInts nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hk_all : k.val = 2 ^ nums.val.length), ∀ r : I64, k_sum nums k = ok r → r.val = sumNeg (asInts nums)) := by
    sorry

  /-- Whenever the function returns a result r, with n = 1: (a) if k = 1, then r = max(nums[0], 0); (b) if k = 2, then r = min(nums[0], 0).
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). Also n = 1. -/
  theorem spec_6 (nums : Slice I64) (k : I64) (x : ℤ)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (h_single : asInts nums = [x]) :
      ∀ r : I64, k_sum nums k = ok r →
        (k.val = 1 → r.val = max x 0) ∧ (k.val = 2 → r.val = min x 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (k : I64) (x : ℤ)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (h_single : asInts nums = [x]), ∀ r : I64, k_sum nums k = ok r →
          (k.val = 1 → r.val = max x 0) ∧ (k.val = 2 → r.val = min x 0)) := by
    sorry

  /-- Whenever k_sum(nums, k) returns r and k_sum(nums', k) returns r', we have r = r'.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). Let nums' be any slice with len(nums') = n and with the same multiset of values as nums (i.e., for every integer v, the count of indices i with nums'[i] = v equals the count with nums[i] = v). -/
  theorem spec_7 (nums nums' : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hlen' : nums'.val.length = nums.val.length)
      (hmult : SameMultiset (asInts nums') (asInts nums)) :
      ∀ r r' : I64, k_sum nums k = ok r → k_sum nums' k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hlen' : nums'.val.length = nums.val.length)
        (hmult : SameMultiset (asInts nums') (asInts nums)), ∀ r r' : I64, k_sum nums k = ok r → k_sum nums' k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever k_sum(nums, k1) returns r1 and k_sum(nums, k2) returns r2, we have r1 >= r2.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let k1 and k2 be positive integers with 1 <= k1 <= k2 <= min(2000, 2^n). -/
  theorem spec_8 (nums : Slice I64) (k1 k2 : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val)
      (hk2_le : k2.val ≤ 2000) (hk2_bound : k2.val ≤ 2 ^ nums.val.length) :
      ∀ r1 r2 : I64, k_sum nums k1 = ok r1 → k_sum nums k2 = ok r2 → r1.val ≥ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (k1 k2 : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val)
        (hk2_le : k2.val ≤ 2000) (hk2_bound : k2.val ≤ 2 ^ nums.val.length), ∀ r1 r2 : I64, k_sum nums k1 = ok r1 → k_sum nums k2 = ok r2 → r1.val ≥ r2.val) := by
    sorry

  /-- Whenever k_sum(nums, k) returns r and k_sum(neg_nums, 2^n - k + 1) returns r', we have r = -r'.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n. Also 2^n - k + 1 <= 2000 (so the second call also satisfies the problem's bound on k). Let neg_nums be the slice of length n with neg_nums[i] = -nums[i] for all i. -/
  theorem spec_9 (nums negNums : Slice I64) (k k' : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hk'_le : 2 ^ nums.val.length - k.val + 1 ≤ 2000)
      (hneg_len : negNums.val.length = nums.val.length)
      (hneg : asInts negNums = (asInts nums).map (fun v => -v))
      (hk' : k'.val = 2 ^ nums.val.length - k.val + 1) :
      ∀ r r' : I64, k_sum nums k = ok r → k_sum negNums k' = ok r' → r.val = -r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums negNums : Slice I64) (k k' : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hk'_le : 2 ^ nums.val.length - k.val + 1 ≤ 2000)
        (hneg_len : negNums.val.length = nums.val.length)
        (hneg : asInts negNums = (asInts nums).map (fun v => -v))
        (hk' : k'.val = 2 ^ nums.val.length - k.val + 1), ∀ r r' : I64, k_sum nums k = ok r → k_sum negNums k' = ok r' → r.val = -r'.val) := by
    sorry

  /-- Whenever k_sum(nums', 2j-1) returns r1, k_sum(nums', 2j) returns r2, and k_sum(nums, j) returns r3, we have r1 = r2 = r3.
    Preconditions: Let n = len(nums). 1 <= n <= 99999 (so len(nums ++ [0]) <= 100000). For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let nums' = nums ++ [0]. Let j be an integer with 1 <= j <= 2^n and 2j <= 2000. -/
  theorem spec_10 (nums nums' : Slice I64) (j k1 k2 : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 99999)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hnums' : asInts nums' = asInts nums ++ [0])
      (hj_pos : 1 ≤ j.val) (hj_bound : j.val ≤ 2 ^ nums.val.length)
      (hj_le : 2 * j.val ≤ 2000)
      (hk1 : k1.val = 2 * j.val - 1) (hk2 : k2.val = 2 * j.val) :
      ∀ r1 r2 r3 : I64, k_sum nums' k1 = ok r1 → k_sum nums' k2 = ok r2 →
        k_sum nums j = ok r3 → r1.val = r2.val ∧ r2.val = r3.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64) (j k1 k2 : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 99999)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hnums' : asInts nums' = asInts nums ++ [0])
        (hj_pos : 1 ≤ j.val) (hj_bound : j.val ≤ 2 ^ nums.val.length)
        (hj_le : 2 * j.val ≤ 2000)
        (hk1 : k1.val = 2 * j.val - 1) (hk2 : k2.val = 2 * j.val), ∀ r1 r2 r3 : I64, k_sum nums' k1 = ok r1 → k_sum nums' k2 = ok r2 →
          k_sum nums j = ok r3 → r1.val = r2.val ∧ r2.val = r3.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S ⊆ {0, 1, ..., n-1} such that r = Σ_{i∈S} nums[i].
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). -/
  theorem spec_11 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length) :
      ∀ r : I64, k_sum nums k = ok r → IsSubsetSum (asInts nums) r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length), ∀ r : I64, k_sum nums k = ok r → IsSubsetSum (asInts nums) r.val) := by
    sorry

  /-- Whenever the function returns a result r: if nums[i] >= 0 for all i, then r >= 0; if nums[i] <= 0 for all i, then r <= 0.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. 1 <= k <= 2000 and k <= 2^n (where 2^n is the mathematical integer, the number of subsequences of nums). Also either nums[i] >= 0 for all i with 0 <= i < n, or nums[i] <= 0 for all i with 0 <= i < n. -/
  theorem spec_12 (nums : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hsign : (∀ x ∈ nums.val, 0 ≤ x.val) ∨ (∀ x ∈ nums.val, x.val ≤ 0)) :
      ∀ r : I64, k_sum nums k = ok r →
        ((∀ x ∈ nums.val, 0 ≤ x.val) → 0 ≤ r.val) ∧
        ((∀ x ∈ nums.val, x.val ≤ 0) → r.val ≤ 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hsign : (∀ x ∈ nums.val, 0 ≤ x.val) ∨ (∀ x ∈ nums.val, x.val ≤ 0)), ∀ r : I64, k_sum nums k = ok r →
          ((∀ x ∈ nums.val, 0 ≤ x.val) → 0 ≤ r.val) ∧
          ((∀ x ∈ nums.val, x.val ≤ 0) → r.val ≤ 0)) := by
    sorry

  /-- Whenever k_sum(nums, 2j-1) returns r1, k_sum(nums, 2j) returns r2, and k_sum(nums', j) returns r3, we have r1 = r2 = r3.
    Preconditions: Let n = len(nums). 2 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Assume nums contains at least one zero. Let nums' be a slice of length n-1 obtained by deleting one occurrence of 0 from nums. Let j be an integer with 1 <= j <= 2^{n-1} and 2j <= 2000. -/
  theorem spec_13 (nums nums' : Slice I64) (j k1 k2 : I64)
      (hn_pos : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hdel : DeleteOneZero (asInts nums) (asInts nums'))
      (hj_pos : 1 ≤ j.val) (hj_bound : j.val ≤ 2 ^ (nums.val.length - 1))
      (hj_le : 2 * j.val ≤ 2000)
      (hk1 : k1.val = 2 * j.val - 1) (hk2 : k2.val = 2 * j.val) :
      ∀ r1 r2 r3 : I64, k_sum nums k1 = ok r1 → k_sum nums k2 = ok r2 →
        k_sum nums' j = ok r3 → r1.val = r2.val ∧ r2.val = r3.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums' : Slice I64) (j k1 k2 : I64)
        (hn_pos : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hdel : DeleteOneZero (asInts nums) (asInts nums'))
        (hj_pos : 1 ≤ j.val) (hj_bound : j.val ≤ 2 ^ (nums.val.length - 1))
        (hj_le : 2 * j.val ≤ 2000)
        (hk1 : k1.val = 2 * j.val - 1) (hk2 : k2.val = 2 * j.val), ∀ r1 r2 r3 : I64, k_sum nums k1 = ok r1 → k_sum nums k2 = ok r2 →
          k_sum nums' j = ok r3 → r1.val = r2.val ∧ r2.val = r3.val) := by
    sorry

  /-- Whenever k_sum(nums, k) returns r and k_sum(nums, 2^n - k + 1) returns r', we have r + r' = total.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let total = Σ_{i=0}^{n-1} nums[i]. Let 1 <= k <= 2000 with k <= 2^n, and also 2^n - k + 1 <= 2000 (so the complementary index is a valid k bound). -/
  theorem spec_14 (nums : Slice I64) (k k' : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hk'_le : 2 ^ nums.val.length - k.val + 1 ≤ 2000)
      (hk' : k'.val = 2 ^ nums.val.length - k.val + 1) :
      ∀ r r' : I64, k_sum nums k = ok r → k_sum nums k' = ok r' →
        r.val + r'.val = listSum (asInts nums) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (k k' : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hk'_le : 2 ^ nums.val.length - k.val + 1 ≤ 2000)
        (hk' : k'.val = 2 ^ nums.val.length - k.val + 1), ∀ r r' : I64, k_sum nums k = ok r → k_sum nums k' = ok r' →
          r.val + r'.val = listSum (asInts nums)) := by
    sorry

  /-- Whenever k_sum(nums, k) returns r and k_sum(nums', k) returns r', we have r <= r'.
    Preconditions: Let n = len(nums). 1 <= n <= 100000. For every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let nums' be another slice of length n with -10^9 <= nums'[i] <= 10^9 for all i, and nums[i] <= nums'[i] for every i. Let 1 <= k <= 2000 with k <= 2^n. -/
  theorem spec_15 (nums nums' : Slice I64) (k : I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
      (hk_bound : k.val ≤ 2 ^ nums.val.length)
      (hlen' : nums'.val.length = nums.val.length)
      (hval' : ∀ x ∈ nums'.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
      (hle : PointwiseLE (asInts nums) (asInts nums')) :
      ∀ r r' : I64, k_sum nums k = ok r → k_sum nums' k = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums nums' : Slice I64) (k : I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hval : ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 2000)
        (hk_bound : k.val ≤ 2 ^ nums.val.length)
        (hlen' : nums'.val.length = nums.val.length)
        (hval' : ∀ x ∈ nums'.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000)
        (hle : PointwiseLE (asInts nums) (asInts nums')), ∀ r r' : I64, k_sum nums k = ok r → k_sum nums' k = ok r' → r.val ≤ r'.val) := by
    sorry

  end AegisSpec.KSum
