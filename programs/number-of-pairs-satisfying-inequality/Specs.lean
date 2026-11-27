import Aegis.NumberOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPairs.number_of_pairs`

LeetCode problem `number-of-pairs-satisfying-inequality`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std

  namespace AegisSpec.NumberOfPairs

  def entry (s : Slice I64) (k : ℕ) : ℤ := (s.val[k]?).map (fun x => x.val) |>.getD 0

  def diffEntry (nums1 nums2 : Slice I64) (k : ℕ) : ℤ :=
    entry nums1 k - entry nums2 k

  def pairDiff (nums1 nums2 : Slice I64) (i j : ℕ) : ℤ :=
    diffEntry nums1 nums2 i - diffEntry nums1 nums2 j

  def indexPairs (n : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range n).product (Finset.range n)).filter (fun q => q.1 < q.2)

  def countPairs (n : ℕ) (p : ℕ → ℕ → Prop) [DecidableRel p] : ℕ :=
    ((indexPairs n).filter (fun q => p q.1 q.2)).card

  def minPairDiff (nums1 nums2 : Slice I64) (n : ℕ) : ℤ :=
    WithTop.untopD 0 ((indexPairs n).image (fun q => pairDiff nums1 nums2 q.1 q.2)).min

  def maxPairDiff (nums1 nums2 : Slice I64) (n : ℕ) : ℤ :=
    WithBot.unbotD 0 ((indexPairs n).image (fun q => pairDiff nums1 nums2 q.1 q.2)).max

  /-- The function returns a result r, and r is exactly the number of pairs (i, j) of integers with 0 <= i < j < n for which nums1[i] - nums1[j] <= nums2[i] - nums2[j] + diff. All arithmetic in this inequality is exact integer arithmetic; under the preconditions every term involved is small enough that no overflow can occur.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_1 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val = ((countPairs n (fun i j =>
          entry nums1 i - entry nums1 j ≤ entry nums2 i - entry nums2 j + diff.val)) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val = ((countPairs n (fun i j =>
            entry nums1 i - entry nums1 j ≤ entry nums2 i - entry nums2 j + diff.val)) : ℤ)) := by
    sorry

  /-- The function returns a result r, and 0 <= r <= n*(n-1)/2. Here n*(n-1)/2 is the total number of index pairs (i, j) with 0 <= i < j < n.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_2 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_3 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r) := by
    sorry

  /-- The function returns a result r, and r = 1 if nums1[0] - nums1[1] <= nums2[0] - nums2[1] + diff, while r = 0 otherwise.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, n = 2, for every k with 0 <= k < 2 both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_4 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : n = 2)
      (hbound1 : ∀ k, k < 2 → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < 2 → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val = (if entry nums1 0 - entry nums1 1 ≤ entry nums2 0 - entry nums2 1 + diff.val
          then 1 else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : n = 2)
        (hbound1 : ∀ k, k < 2 → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < 2 → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val = (if entry nums1 0 - entry nums1 1 ≤ entry nums2 0 - entry nums2 1 + diff.val
            then 1 else 0)) := by
    sorry

  /-- For 0 <= i < j < n define d(i,j) = (nums1[i] - nums2[i]) - (nums1[j] - nums2[j]), and let m = min { d(i,j) : 0 <= i < j < n }, which is well-defined because n >= 2. The function returns a result r, and r = 0 if and only if diff < m.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_5 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        (r.val = 0 ↔ diff.val < minPairDiff nums1 nums2 n) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          (r.val = 0 ↔ diff.val < minPairDiff nums1 nums2 n)) := by
    sorry

  /-- For 0 <= i < j < n define d(i,j) = (nums1[i] - nums2[i]) - (nums1[j] - nums2[j]), and let M = max { d(i,j) : 0 <= i < j < n }, which is well-defined because n >= 2. The function returns a result r, and r = n*(n-1)/2 if and only if diff >= M.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_6 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        (r.val = ((n * (n - 1) / 2 : ℕ) : ℤ) ↔ maxPairDiff nums1 nums2 n ≤ diff.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          (r.val = ((n * (n - 1) / 2 : ℕ) : ℤ) ↔ maxPairDiff nums1 nums2 n ≤ diff.val)) := by
    sorry

  /-- For every pair of integers d1 and d2 with -10000 <= d1 <= d2 <= 10000, let r1 be the result of number_of_pairs(nums1, nums2, d1) and let r2 be the result of number_of_pairs(nums1, nums2, d2). The function returns both results, and r1 <= r2.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000. -/
  theorem spec_7 (nums1 nums2 : Slice I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (d1 d2 : I64) (hd1 : -10000 ≤ d1.val) (hdd : d1.val ≤ d2.val)
      (hd2 : d2.val ≤ 10000) :
      ∃ r1 r2, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d1 = Result.ok r1 ∧
        Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d2 = Result.ok r2 ∧
        r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (d1 d2 : I64) (hd1 : -10000 ≤ d1.val) (hdd : d1.val ≤ d2.val)
        (hd2 : d2.val ≤ 10000), ∃ r1 r2, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d1 = Result.ok r1 ∧
          Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d2 = Result.ok r2 ∧
          r1.val ≤ r2.val) := by
    sorry

  /-- For every integer d with -10000 <= d < 10000, let r_d be the result of number_of_pairs(nums1, nums2, d) and let r_next be the result of number_of_pairs(nums1, nums2, d+1). The function returns both results, and r_next - r_d is exactly the number of pairs (i, j) with 0 <= i < j < n and (nums1[i] - nums2[i]) - (nums1[j] - nums2[j]) = d+1.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000. -/
  theorem spec_8 (nums1 nums2 : Slice I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (d dnext : I64) (hd : -10000 ≤ d.val) (hd_lt : d.val < 10000)
      (hnext : dnext.val = d.val + 1) :
      ∃ rd rnext, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d = Result.ok rd ∧
        Aegis.NumberOfPairs.number_of_pairs nums1 nums2 dnext = Result.ok rnext ∧
        rnext.val - rd.val =
          ((countPairs n (fun i j => pairDiff nums1 nums2 i j = d.val + 1)) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (d dnext : I64) (hd : -10000 ≤ d.val) (hd_lt : d.val < 10000)
        (hnext : dnext.val = d.val + 1), ∃ rd rnext, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 d = Result.ok rd ∧
          Aegis.NumberOfPairs.number_of_pairs nums1 nums2 dnext = Result.ok rnext ∧
          rnext.val - rd.val =
            ((countPairs n (fun i j => pairDiff nums1 nums2 i j = d.val + 1)) : ℤ)) := by
    sorry

  /-- For every integer c such that nums1[k] + c is in the interval [-10000, 10000] for every k with 0 <= k < n, let nums1' be the slice defined by nums1'[k] = nums1[k] + c. Let r be the result of number_of_pairs(nums1, nums2, diff) and let r' be the result of number_of_pairs(nums1', nums2, diff). The function returns both results, and r' = r.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_9 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000)
      (c : ℤ) (hc : ∀ k, k < n → -10000 ≤ entry nums1 k + c ∧ entry nums1 k + c ≤ 10000) :
      ∃ nums1' : Slice I64, nums1'.val.length = n ∧
        (∀ k, k < n → entry nums1' k = entry nums1 k + c) ∧
        ∃ r r', Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          Aegis.NumberOfPairs.number_of_pairs nums1' nums2 diff = Result.ok r' ∧
          r' = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000)
        (c : ℤ) (hc : ∀ k, k < n → -10000 ≤ entry nums1 k + c ∧ entry nums1 k + c ≤ 10000), ∃ nums1' : Slice I64, nums1'.val.length = n ∧
          (∀ k, k < n → entry nums1' k = entry nums1 k + c) ∧
          ∃ r r', Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
            Aegis.NumberOfPairs.number_of_pairs nums1' nums2 diff = Result.ok r' ∧
            r' = r) := by
    sorry

  /-- Let nums1' and nums2' be any slices of length n whose entries all lie in [-10000, 10000] and which satisfy nums1'[k] - nums2'[k] = nums1[k] - nums2[k] for every k with 0 <= k < n. Let r be the result of number_of_pairs(nums1, nums2, diff) and let r' be the result of number_of_pairs(nums1', nums2', diff). The function returns both results, and r' = r.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_10 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000)
      (nums1' nums2' : Slice I64)
      (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
      (hbound1' : ∀ k, k < n → -10000 ≤ entry nums1' k ∧ entry nums1' k ≤ 10000)
      (hbound2' : ∀ k, k < n → -10000 ≤ entry nums2' k ∧ entry nums2' k ≤ 10000)
      (hsame : ∀ k, k < n → diffEntry nums1' nums2' k = diffEntry nums1 nums2 k) :
      ∃ r r', Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        Aegis.NumberOfPairs.number_of_pairs nums1' nums2' diff = Result.ok r' ∧
        r' = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000)
        (nums1' nums2' : Slice I64)
        (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
        (hbound1' : ∀ k, k < n → -10000 ≤ entry nums1' k ∧ entry nums1' k ≤ 10000)
        (hbound2' : ∀ k, k < n → -10000 ≤ entry nums2' k ∧ entry nums2' k ≤ 10000)
        (hsame : ∀ k, k < n → diffEntry nums1' nums2' k = diffEntry nums1 nums2 k), ∃ r r', Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          Aegis.NumberOfPairs.number_of_pairs nums1' nums2' diff = Result.ok r' ∧
          r' = r) := by
    sorry

  /-- Let a[k] = nums1[k] - nums2[k] for 0 <= k < n. Let C be the number of pairs (i, j) with 0 <= i < j < n and a[i] <= a[j]. The function returns a result r, and r >= C.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and 0 <= diff <= 10000. -/
  theorem spec_11 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : 0 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val ≥ ((countPairs n (fun i j =>
          diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j)) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : 0 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val ≥ ((countPairs n (fun i j =>
            diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j)) : ℤ)) := by
    sorry

  /-- Let a[k] = nums1[k] - nums2[k] for 0 <= k < n. Let C be the number of pairs (i, j) with 0 <= i < j < n and a[i] < a[j]. The function returns a result r, and r <= C.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff < 0. -/
  theorem spec_12 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val < 0) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val ≤ ((countPairs n (fun i j =>
          diffEntry nums1 nums2 i < diffEntry nums1 nums2 j)) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val < 0), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val ≤ ((countPairs n (fun i j =>
            diffEntry nums1 nums2 i < diffEntry nums1 nums2 j)) : ℤ)) := by
    sorry

  /-- Let a[k] = nums1[k] - nums2[k] for 0 <= k < n. The function returns a result r, and r is exactly the number of pairs (i, j) with 0 <= i < j < n and a[i] <= a[j] + diff.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and -10000 <= diff <= 10000. -/
  theorem spec_13 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val = ((countPairs n (fun i j =>
          diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j + diff.val)) : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : -10000 ≤ diff.val ∧ diff.val ≤ 10000), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val = ((countPairs n (fun i j =>
            diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j + diff.val)) : ℤ)) := by
    sorry

  /-- Let a[k] = nums1[k] - nums2[k] for 0 <= k < n. Let C be the number of pairs (i, j) with 0 <= i < j < n and a[i] <= a[j]. The function returns a result r, and r = C.
    Preconditions: Let n = len(nums1). The constraints hold: len(nums1) = len(nums2) = n, 2 <= n <= 100000, for every k with 0 <= k < n both -10000 <= nums1[k] <= 10000 and -10000 <= nums2[k] <= 10000, and diff = 0. -/
  theorem spec_14 (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : 2 ≤ n) (hn_le : n ≤ 100000)
      (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
      (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
      (hdiff : diff.val = 0) :
      ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
        r.val = ((countPairs n (fun i j =>
          diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j)) : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 : Slice I64) (diff : I64) (n : ℕ)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : 2 ≤ n) (hn_le : n ≤ 100000)
        (hbound1 : ∀ k, k < n → -10000 ≤ entry nums1 k ∧ entry nums1 k ≤ 10000)
        (hbound2 : ∀ k, k < n → -10000 ≤ entry nums2 k ∧ entry nums2 k ≤ 10000)
        (hdiff : diff.val = 0), ∃ r, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 diff = Result.ok r ∧
          r.val = ((countPairs n (fun i j =>
            diffEntry nums1 nums2 i ≤ diffEntry nums1 nums2 j)) : ℤ)) := by
    sorry

  end AegisSpec.NumberOfPairs
