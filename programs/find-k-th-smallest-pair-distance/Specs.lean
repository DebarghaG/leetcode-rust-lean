import Aegis.SmallestDistancePair.Code.Funs

/-!
# Specifications of `Aegis.SmallestDistancePair.smallest_distance_pair`

LeetCode problem `find-k-th-smallest-pair-distance`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestDistancePair

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def numPairs (n : ℕ) : ℕ := n * (n - 1) / 2

  def pairDists : List ℤ → List ℤ
    | [] => []
    | x :: xs => xs.map (fun y => |x - y|) ++ pairDists xs

  def sortedPairDists (l : List ℤ) : List ℤ := (pairDists l).mergeSort (· ≤ ·)

  def countLE (l : List ℤ) (r : ℤ) : ℕ := (pairDists l).countP (fun d => decide (d ≤ r))

  def countLT (l : List ℤ) (r : ℤ) : ℕ := (pairDists l).countP (fun d => decide (d < r))

  def countEq (l : List ℤ) : ℕ := (pairDists l).countP (fun d => decide (d = 0))

  def distAt (l : List ℤ) (i j : ℕ) : Option ℤ :=
    match l[i]?, l[j]? with
    | some a, some b => some |a - b|
    | _, _ => none

  def listMax (l : List ℤ) : ℤ := (l.max?).getD 0

  def listMin (l : List ℤ) : ℤ := (l.min?).getD 0

  /-- Let M = n*(n-1)/2. Let d_1 <= d_2 <= ... <= d_M be the nondecreasing list of the M values |nums[i] - nums[j]| obtained from all index pairs with 0 <= i < j < n, with one entry per pair, so equal distances are repeated. The function returns a result r and r = d_k (1-indexed).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ)) :
      ∃ r, Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r ∧
        (sortedPairDists (vals nums))[(k.val - 1).toNat]? = some r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ)), ∃ r, Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r ∧
          (sortedPairDists (vals nums))[(k.val - 1).toNat]? = some r.val) := by
    sorry

  /-- For every nums and k satisfying the preconditions, the function returns a result r; in particular, it does not fail because of overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ)) :
      ∃ r, Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ)), ∃ r, Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum values among nums[0],...,nums[n-1].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      0 ≤ r.val ∧ r.val ≤ listMax (vals nums) - listMin (vals nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), 0 ≤ r.val ∧ r.val ≤ listMax (vals nums) - listMin (vals nums)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < j < n such that r = |nums[i] - nums[j]|.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      ∃ i j, i < j ∧ j < nums.val.length ∧ distAt (vals nums) i j = some r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), ∃ i j, i < j ∧ j < nums.val.length ∧ distAt (vals nums) i j = some r.val) := by
    sorry

  /-- Whenever the function returns a result r, the number of index pairs (i,j) with 0 <= i < j < n and |nums[i] - nums[j]| <= r is at least k.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      k.val ≤ (countLE (vals nums) r.val : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), k.val ≤ (countLE (vals nums) r.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, the number of index pairs (i,j) with 0 <= i < j < n and |nums[i] - nums[j]| < r is less than k; equivalently, it is at most k-1. With repeated distances this number need not equal k-1; the valid rank characterization is count(<r) < k <= count(<=r).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      (countLT (vals nums) r.val : ℤ) < k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), (countLT (vals nums) r.val : ℤ) < k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min { |nums[i] - nums[j]| : 0 <= i < j < n }.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and k = 1. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk : k.val = 1)
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      (pairDists (vals nums)).min? = some r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk : k.val = 1)
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), (pairDists (vals nums)).min? = some r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = max(nums) - min(nums).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and k = n*(n-1)/2. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk : k.val = (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      r.val = listMax (vals nums) - listMin (vals nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk : k.val = (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), r.val = listMax (vals nums) - listMin (vals nums)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2. Let z be the number of index pairs (i,j) with 0 <= i < j < n and nums[i] = nums[j]; assume k <= z. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (hz : k.val ≤ (countEq (vals nums) : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (hz : k.val ≤ (countEq (vals nums) : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), r.val = 0) := by
    sorry

  /-- If the call smallest_distance_pair(nums, k) returns r and the call smallest_distance_pair(nums', k) returns r', then r = r'.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2. Let nums' be any slice of i64 with len(nums') = n whose entries have the same multiset of values as nums, i.e. nums' is a permutation of nums. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (hlen : nums'.val.length = nums.val.length)
      (hperm : (vals nums').Perm (vals nums))
      (r r' : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r)
      (hr' : Aegis.SmallestDistancePair.smallest_distance_pair nums' k = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (hlen : nums'.val.length = nums.val.length)
        (hperm : (vals nums').Perm (vals nums))
        (r r' : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r)
        (hr' : Aegis.SmallestDistancePair.smallest_distance_pair nums' k = ok r'), r.val = r'.val) := by
    sorry

  /-- If the call smallest_distance_pair(nums, k1) returns r1 and the call smallest_distance_pair(nums, k2) returns r2, then r1 <= r2.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6. Let k1 and k2 be integers with 1 <= k1 <= k2 <= n*(n-1)/2. -/
  theorem spec_11 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2 : k2.val ≤ (numPairs nums.val.length : ℤ))
      (r1 r2 : Std.I64)
      (hr1 : Aegis.SmallestDistancePair.smallest_distance_pair nums k1 = ok r1)
      (hr2 : Aegis.SmallestDistancePair.smallest_distance_pair nums k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2 : k2.val ≤ (numPairs nums.val.length : ℤ))
        (r1 r2 : Std.I64)
        (hr1 : Aegis.SmallestDistancePair.smallest_distance_pair nums k1 = ok r1)
        (hr2 : Aegis.SmallestDistancePair.smallest_distance_pair nums k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If the call smallest_distance_pair(nums, k) returns r and the call smallest_distance_pair(nums_c, k) returns r_c, then r = r_c.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2. Let c be an integer such that 0 <= nums[i] + c <= 10^6 for every i. Define nums_c by nums_c[i] = nums[i] + c. -/
  theorem spec_12 (nums nums_c : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (hc : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x + c ∧ x + c ≤ 10 ^ 6)
      (hlen : nums_c.val.length = nums.val.length)
      (hshift : ∀ i, i < nums.val.length → ∀ x y, (vals nums)[i]? = some x →
        (vals nums_c)[i]? = some y → y = x + c)
      (r r_c : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r)
      (hr_c : Aegis.SmallestDistancePair.smallest_distance_pair nums_c k = ok r_c) :
      r.val = r_c.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums_c : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (hc : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x + c ∧ x + c ≤ 10 ^ 6)
        (hlen : nums_c.val.length = nums.val.length)
        (hshift : ∀ i, i < nums.val.length → ∀ x y, (vals nums)[i]? = some x →
          (vals nums_c)[i]? = some y → y = x + c)
        (r r_c : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r)
        (hr_c : Aegis.SmallestDistancePair.smallest_distance_pair nums_c k = ok r_c), r.val = r_c.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x such that the number of index pairs (i,j) with 0 <= i < j < n and |nums[i] - nums[j]| <= x is at least k, we have r <= x.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      ∀ x : ℤ, k.val ≤ (countLE (vals nums) x : ℤ) → r.val ≤ x := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), ∀ x : ℤ, k.val ≤ (countLE (vals nums) x : ℤ) → r.val ≤ x) := by
    sorry

  /-- Whenever the function returns a result r, r is the least integer x such that the number of index pairs (i,j) with 0 <= i < j < n and |nums[i] - nums[j]| <= x is at least k; equivalently, r = min { x in Z : #{ (i,j) : 0 <= i < j < n and |nums[i]-nums[j]| <= x } >= k }.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2, where k is the integer value of the i64 parameter. -/
  theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      k.val ≤ (countLE (vals nums) r.val : ℤ) ∧
        ∀ x : ℤ, k.val ≤ (countLE (vals nums) x : ℤ) → r.val ≤ x := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), k.val ≤ (countLE (vals nums) r.val : ℤ) ∧
          ∀ x : ℤ, k.val ≤ (countLE (vals nums) x : ℤ) → r.val ≤ x) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if z >= k.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 10^4; for every index i with 0 <= i < n, 0 <= nums[i] <= 10^6; and 1 <= k <= n*(n-1)/2. Let z be the number of index pairs (i,j) with 0 <= i < j < n and nums[i] = nums[j]. -/
  theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
      (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
      (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
        0 ≤ x ∧ x ≤ 10 ^ 6)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
      (r : Std.I64)
      (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r) :
      (r.val = 0 ↔ k.val ≤ (countEq (vals nums) : ℤ)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn2 : 2 ≤ nums.val.length) (hn : nums.val.length ≤ 10000)
        (hbound : ∀ i, i < nums.val.length → ∀ x, (vals nums)[i]? = some x →
          0 ≤ x ∧ x ≤ 10 ^ 6)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (numPairs nums.val.length : ℤ))
        (r : Std.I64)
        (hr : Aegis.SmallestDistancePair.smallest_distance_pair nums k = ok r), (r.val = 0 ↔ k.val ≤ (countEq (vals nums) : ℤ))) := by
    sorry

  end AegisSpec.SmallestDistancePair
