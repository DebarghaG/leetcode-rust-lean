import Aegis.MinSubsequence.Code.Funs

/-!
# Specifications of `Aegis.MinSubsequence.min_subsequence`

LeetCode problem `minimum-subsequence-in-non-increasing-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinSubsequence

  namespace AegisSpec.MinSubsequence

  def vals (l : List I64) : List Int := l.map (fun x => x.val)

  def sum (l : List Int) : Int := l.sum

  def sumInit (l : List Int) : Int := l.dropLast.sum

  def countOcc (l : List Int) (v : Int) : Nat := l.countP (fun x => decide (x = v))

  def NonIncreasing (l : List Int) : Prop :=
    ∀ i (h : i + 1 < l.length), l[i]'(by omega) ≥ l[i+1]'h

  def SubMultiset (r nums : List Int) : Prop := ∀ v, countOcc r v ≤ countOcc nums v

  def Majority (r nums : List Int) : Prop := 2 * sum r > sum nums

  def SameMultiset (l₁ l₂ : List Int) : Prop := ∀ v, countOcc l₁ v = countOcc l₂ v

  def maxElem : List Int → Int
    | [] => 0
    | a :: rest => rest.foldr max a

  def sortDesc (l : List Int) : List Int := l.mergeSort (fun a b => decide (b ≤ a))

  def topKSum (l : List Int) (k : Nat) : Int := sum ((sortDesc l).take k)

  /-- The function returns a result vector r of i64 such that: (1) r is sorted in non-increasing order: for every i with 0 <= i < len(r) - 1, r[i] >= r[i+1]; (2) the multiset of elements of r is a sub-multiset of the multiset of elements of nums: for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at most the number of indices j with 0 <= j < len(nums) and nums[j] = v; (3) 2 * sum(r) > sum(nums), where sum(x) denotes the sum of all elements of x; (4) among all vectors r' of i64 satisfying (1), (2), and (3), r has minimum length: len(r) <= len(r') for every such r'; (5) among all vectors r' of i64 satisfying (1), (2), (3), and len(r') = len(r), r has maximum sum: sum(r') <= sum(r).
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧

        NonIncreasing (vals r.val) ∧

        SubMultiset (vals r.val) (vals nums.val) ∧

        Majority (vals r.val) (vals nums.val) ∧

        (∀ r' : alloc.vec.Vec I64,
          NonIncreasing (vals r'.val) →
          SubMultiset (vals r'.val) (vals nums.val) →
          Majority (vals r'.val) (vals nums.val) →
          (vals r.val).length ≤ (vals r'.val).length) ∧

        (∀ r' : alloc.vec.Vec I64,
          NonIncreasing (vals r'.val) →
          SubMultiset (vals r'.val) (vals nums.val) →
          Majority (vals r'.val) (vals nums.val) →
          (vals r'.val).length = (vals r.val).length →
          sum (vals r'.val) ≤ sum (vals r.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧

          NonIncreasing (vals r.val) ∧

          SubMultiset (vals r.val) (vals nums.val) ∧

          Majority (vals r.val) (vals nums.val) ∧

          (∀ r' : alloc.vec.Vec I64,
            NonIncreasing (vals r'.val) →
            SubMultiset (vals r'.val) (vals nums.val) →
            Majority (vals r'.val) (vals nums.val) →
            (vals r.val).length ≤ (vals r'.val).length) ∧

          (∀ r' : alloc.vec.Vec I64,
            NonIncreasing (vals r'.val) →
            SubMultiset (vals r'.val) (vals nums.val) →
            Majority (vals r'.val) (vals nums.val) →
            (vals r'.val).length = (vals r.val).length →
            sum (vals r'.val) ≤ sum (vals r.val))) := by
    sorry

  /-- The returned vector r is sorted in non-increasing order: for every i with 0 <= i < len(r) - 1, r[i] >= r[i+1].
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        NonIncreasing (vals r.val) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          NonIncreasing (vals r.val)) := by
    sorry

  /-- For every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at most the number of indices j with 0 <= j < len(nums) and nums[j] = v. Equivalently, the multiset of elements of r is a sub-multiset of the multiset of elements of nums.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        SubMultiset (vals r.val) (vals nums.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          SubMultiset (vals r.val) (vals nums.val)) := by
    sorry

  /-- The sum of the elements of r is strictly greater than the sum of the elements of nums not included in r: 2 * sum(r) > sum(nums), where sum(x) denotes the sum of all elements of x.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        Majority (vals r.val) (vals nums.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          Majority (vals r.val) (vals nums.val)) := by
    sorry

  /-- For every vector r' of i64 such that the multiset of r' is a sub-multiset of the multiset of nums and 2 * sum(r') > sum(nums), it holds that len(r) <= len(r').
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        ∀ r' : alloc.vec.Vec I64,
          SubMultiset (vals r'.val) (vals nums.val) →
          Majority (vals r'.val) (vals nums.val) →
          (vals r.val).length ≤ (vals r'.val).length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          ∀ r' : alloc.vec.Vec I64,
            SubMultiset (vals r'.val) (vals nums.val) →
            Majority (vals r'.val) (vals nums.val) →
            (vals r.val).length ≤ (vals r'.val).length) := by
    sorry

  /-- For every vector r' of i64 such that the multiset of r' is a sub-multiset of the multiset of nums, 2 * sum(r') > sum(nums), and len(r') = len(r), it holds that sum(r') <= sum(r).
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        ∀ r' : alloc.vec.Vec I64,
          SubMultiset (vals r'.val) (vals nums.val) →
          Majority (vals r'.val) (vals nums.val) →
          (vals r'.val).length = (vals r.val).length →
          sum (vals r'.val) ≤ sum (vals r.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          ∀ r' : alloc.vec.Vec I64,
            SubMultiset (vals r'.val) (vals nums.val) →
            Majority (vals r'.val) (vals nums.val) →
            (vals r'.val).length = (vals r.val).length →
            sum (vals r'.val) ≤ sum (vals r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, panic, or cause an out-of-bounds access.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r) := by
    sorry

  /-- The returned vector r is non-empty and its first element equals the maximum element of nums: len(r) >= 1 and r[0] = max(nums), where max(nums) is the largest value among nums[0], nums[1], ..., nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        1 ≤ (vals r.val).length ∧
        (vals r.val).head? = some (maxElem (vals nums.val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          1 ≤ (vals r.val).length ∧
          (vals r.val).head? = some (maxElem (vals nums.val))) := by
    sorry

  /-- Let L = len(nums) and let n_1, n_2, ..., n_L be the elements of nums sorted in non-increasing order (so n_1 >= n_2 >= ... >= n_L and the multiset {n_1, ..., n_L} equals the multiset of nums). Let k = len(r). Then 1 <= k <= L, for every i with 0 <= i < k, r[i] = n_{i+1}, the inequality 2 * (n_1 + ... + n_k) > sum(nums) holds, and for every j with 1 <= j < k, the inequality 2 * (n_1 + ... + n_j) <= sum(nums) holds.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        1 ≤ (vals r.val).length ∧
        (vals r.val).length ≤ nums.val.length ∧
        vals r.val = (sortDesc (vals nums.val)).take (vals r.val).length ∧
        2 * topKSum (vals nums.val) (vals r.val).length > sum (vals nums.val) ∧
        ∀ j, 1 ≤ j → j < (vals r.val).length →
          2 * topKSum (vals nums.val) j ≤ sum (vals nums.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          1 ≤ (vals r.val).length ∧
          (vals r.val).length ≤ nums.val.length ∧
          vals r.val = (sortDesc (vals nums.val)).take (vals r.val).length ∧
          2 * topKSum (vals nums.val) (vals r.val).length > sum (vals nums.val) ∧
          ∀ j, 1 ≤ j → j < (vals r.val).length →
            2 * topKSum (vals nums.val) j ≤ sum (vals nums.val)) := by
    sorry

  /-- If len(r) >= 2, then 2 * (sum(r) - r[len(r)-1]) <= sum(nums).
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        (2 ≤ (vals r.val).length →
          2 * sumInit (vals r.val) ≤ sum (vals nums.val)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          (2 ≤ (vals r.val).length →
            2 * sumInit (vals r.val) ≤ sum (vals nums.val))) := by
    sorry

  /-- The returned vector r satisfies len(r) = 1 and r[0] = m, where m is the unique element of nums with 2 * m > sum(nums).
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; there exists an integer m such that m is an element of nums and 2 * m > sum(nums). -/
  theorem spec_11 (nums : Slice I64) (m : Int)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hmem : m ∈ vals nums.val)
      (hgt : 2 * m > sum (vals nums.val))
      (huniq : ∀ m', m' ∈ vals nums.val → 2 * m' > sum (vals nums.val) → m' = m) :
      ∃ r, min_subsequence nums = ok r ∧
        (vals r.val).length = 1 ∧
        vals r.val = [m] := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (m : Int)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hmem : m ∈ vals nums.val)
        (hgt : 2 * m > sum (vals nums.val))
        (huniq : ∀ m', m' ∈ vals nums.val → 2 * m' > sum (vals nums.val) → m' = m), ∃ r, min_subsequence nums = ok r ∧
          (vals r.val).length = 1 ∧
          vals r.val = [m]) := by
    sorry

  /-- min_subsequence(nums1) and min_subsequence(nums2) both succeed and their returned result vectors are equal.
    Preconditions: 1 <= len(nums1) <= 500; 1 <= len(nums2) <= 500; for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 100; for every i with 0 <= i < len(nums2), 1 <= nums2[i] <= 100; and for every integer v, the number of indices i with 0 <= i < len(nums1) and nums1[i] = v equals the number of indices j with 0 <= j < len(nums2) and nums2[j] = v. -/
  theorem spec_12 (nums1 nums2 : Slice I64)
      (hlen1a : 1 ≤ nums1.val.length) (hlen1b : nums1.val.length ≤ 500)
      (hrange1 : ∀ i (h : i < nums1.val.length),
        1 ≤ (nums1.val[i]'h).val ∧ (nums1.val[i]'h).val ≤ 100)
      (hlen2a : 1 ≤ nums2.val.length) (hlen2b : nums2.val.length ≤ 500)
      (hrange2 : ∀ i (h : i < nums2.val.length),
        1 ≤ (nums2.val[i]'h).val ∧ (nums2.val[i]'h).val ≤ 100)
      (hsame : SameMultiset (vals nums1.val) (vals nums2.val)) :
      ∃ r, min_subsequence nums1 = ok r ∧ min_subsequence nums2 = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice I64)
        (hlen1a : 1 ≤ nums1.val.length) (hlen1b : nums1.val.length ≤ 500)
        (hrange1 : ∀ i (h : i < nums1.val.length),
          1 ≤ (nums1.val[i]'h).val ∧ (nums1.val[i]'h).val ≤ 100)
        (hlen2a : 1 ≤ nums2.val.length) (hlen2b : nums2.val.length ≤ 500)
        (hrange2 : ∀ i (h : i < nums2.val.length),
          1 ≤ (nums2.val[i]'h).val ∧ (nums2.val[i]'h).val ≤ 100)
        (hsame : SameMultiset (vals nums1.val) (vals nums2.val)), ∃ r, min_subsequence nums1 = ok r ∧ min_subsequence nums2 = ok r) := by
    sorry

  /-- The length of r satisfies 1 <= len(r) <= floor(len(nums)/2) + 1, where floor(x) is the largest integer less than or equal to x.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_13 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        1 ≤ (vals r.val).length ∧
        (vals r.val).length ≤ nums.val.length / 2 + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          1 ≤ (vals r.val).length ∧
          (vals r.val).length ≤ nums.val.length / 2 + 1) := by
    sorry

  /-- The returned vector r satisfies len(r) = floor(len(nums)/2) + 1 and r[i] = c for every i with 0 <= i < len(r).
    Preconditions: 1 <= len(nums) <= 500; there exists an integer c with 1 <= c <= 100 such that for every i with 0 <= i < len(nums), nums[i] = c. -/
  theorem spec_14 (nums : Slice I64) (c : Int)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hc1 : 1 ≤ c) (hc2 : c ≤ 100)
      (hall : ∀ i (h : i < nums.val.length), (nums.val[i]'h).val = c) :
      ∃ r, min_subsequence nums = ok r ∧
        (vals r.val).length = nums.val.length / 2 + 1 ∧
        ∀ x, x ∈ vals r.val → x = c := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (c : Int)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hc1 : 1 ≤ c) (hc2 : c ≤ 100)
        (hall : ∀ i (h : i < nums.val.length), (nums.val[i]'h).val = c), ∃ r, min_subsequence nums = ok r ∧
          (vals r.val).length = nums.val.length / 2 + 1 ∧
          ∀ x, x ∈ vals r.val → x = c) := by
    sorry

  /-- For every integer x and every integer y, if x occurs in r (there exists i with 0 <= i < len(r) and r[i] = x) and y occurs in nums more times than it occurs in r (the number of indices j with 0 <= j < len(nums) and nums[j] = y is strictly greater than the number of indices i with 0 <= i < len(r) and r[i] = y), then x >= y.
    Preconditions: 1 <= len(nums) <= 500; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_15 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ r, min_subsequence nums = ok r ∧
        ∀ x y : Int,
          x ∈ vals r.val →
          countOcc (vals r.val) y < countOcc (vals nums.val) y →
          x ≥ y := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 500)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ r, min_subsequence nums = ok r ∧
          ∀ x y : Int,
            x ∈ vals r.val →
            countOcc (vals r.val) y < countOcc (vals nums.val) y →
            x ≥ y) := by
    sorry

  end AegisSpec.MinSubsequence
