import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-the-maximum-length-of-a-good-subsequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumLength

  namespace AegisSpec.MaximumLength

  def numChanges : List Int → Nat
    | [] => 0
    | [_] => 0
    | a :: b :: rest => (if a = b then 0 else 1) + numChanges (b :: rest)

  def elem (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i default).val

  def IsSubseqIndices (nums : Slice Std.I64) (idx : List Nat) (seq : List Int) : Prop :=
    idx.Pairwise (· < ·) ∧
      (∀ i ∈ idx, i < nums.val.length) ∧
      seq = idx.map (fun i => elem nums i)

  def IsGoodSubseq (nums : Slice Std.I64) (k : Int) (seq : List Int) : Prop :=
    seq ≠ [] ∧ ∃ idx, IsSubseqIndices nums idx seq ∧ (numChanges seq : Int) ≤ k

  def IsMaxGoodSubseqLen (nums : Slice Std.I64) (k : Int) (r : Int) : Prop :=
    (∃ seq, IsGoodSubseq nums k seq ∧ (seq.length : Int) = r) ∧
      ∀ seq, IsGoodSubseq nums k seq → (seq.length : Int) ≤ r

  def freq (nums : Slice Std.I64) (v : Int) : Nat :=
    (nums.val.filter (fun x => decide (x.val = v))).length

  def maxFreq (nums : Slice Std.I64) : Nat :=
    nums.val.foldr (fun x m => max (freq nums x.val) m) 0

  theorem slice_val_length_le (s : Slice Std.I64) : s.val.length ≤ Usize.max := by
    have h : s.list.toList.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    simpa only [Slice.val, h] using s.bound

  def sliceRev (s : Slice Std.I64) : Slice Std.I64 :=
    Slice.from s.val.reverse (by
      rw [List.length_reverse]
      exact slice_val_length_le s)

  /-- The function returns a result r, and r (interpreted as a mathematical integer) is the maximum length of a good subsequence of nums. A good subsequence of nums is a non-empty sequence seq of integers of length m (with m >= 1) for which there exist indices 0 <= i_0 < ... < i_{m-1} < len(nums) such that seq[t] = nums[i_t] for every 0 <= t < m, and the number of t with 0 <= t < m-1 and seq[t] != seq[t+1] is at most k.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int)) :
      ∃ r, maximum_length nums k = ok r ∧ IsMaxGoodSubseqLen nums k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int)), ∃ r, maximum_length nums k = ok r ∧ IsMaxGoodSubseqLen nums k.val r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int)) :
      ∃ r, maximum_length nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int)), ∃ r, maximum_length nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r on an input satisfying the preconditions, r <= len(nums) (interpreting r as a mathematical integer).
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns r, let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let maxfreq be the maximum of freq(v) over all integers v. Then r >= maxfreq.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      (maxFreq nums : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), (maxFreq nums : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, r >= min(len(nums), k+1), where k+1 is computed as a mathematical integer.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      min (nums.val.length : Int) (k.val + 1) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), min (nums.val.length : Int) (k.val + 1) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let maxfreq be the maximum of freq(v) over all integers v. Then r = maxfreq.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with k = 0. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk : k.val = 0)
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      r.val = (maxFreq nums : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk : k.val = 0)
        (r : Std.I64) (hr : maximum_length nums k = ok r), r.val = (maxFreq nums : Int)) := by
    sorry

  /-- Whenever the function returns r, r = len(nums).
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with len(nums)-1 <= k <= min(50, len(nums)). -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_ge : (nums.val.length : Int) - 1 ≤ k.val)
      (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      r.val = (nums.val.length : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_ge : (nums.val.length : Int) - 1 ≤ k.val)
        (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), r.val = (nums.val.length : Int)) := by
    sorry

  /-- If maximum_length(nums, k1) returns r1 and maximum_length(nums, k2) returns r2, then r1 <= r2.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k1 and k2 are i64 values with 0 <= k1 <= k2 <= min(50, len(nums)). -/
  theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk1_pos : 0 ≤ k1.val) (hk_le : k1.val ≤ k2.val)
      (hk2_le : k2.val ≤ min 50 (nums.val.length : Int))
      (r1 r2 : Std.I64)
      (hr1 : maximum_length nums k1 = ok r1) (hr2 : maximum_length nums k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk1_pos : 0 ≤ k1.val) (hk_le : k1.val ≤ k2.val)
        (hk2_le : k2.val ≤ min 50 (nums.val.length : Int))
        (r1 r2 : Std.I64)
        (hr1 : maximum_length nums k1 = ok r1) (hr2 : maximum_length nums k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If maximum_length(nums, k) returns r and maximum_length(nums2, k) returns r2, then r = r2.
    Preconditions: nums and nums2 are slices of i64 with 1 <= len(nums) = len(nums2) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9 and 1 <= nums2[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)); for all i, j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j] iff nums2[i] = nums2[j]. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hlen_eq : nums.val.length = nums2.val.length)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hval2 : ∀ i, i < nums2.val.length → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (hequiv : ∀ i j, i < nums.val.length → j < nums.val.length →
        (elem nums i = elem nums j ↔ elem nums2 i = elem nums2 j))
      (r r2 : Std.I64)
      (hr : maximum_length nums k = ok r) (hr2 : maximum_length nums2 k = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hlen_eq : nums.val.length = nums2.val.length)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hval2 : ∀ i, i < nums2.val.length → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (hequiv : ∀ i j, i < nums.val.length → j < nums.val.length →
          (elem nums i = elem nums j ↔ elem nums2 i = elem nums2 j))
        (r r2 : Std.I64)
        (hr : maximum_length nums k = ok r) (hr2 : maximum_length nums2 k = ok r2), r.val = r2.val) := by
    sorry

  /-- Let rev(nums) be the slice of length len(nums) with rev(nums)[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). If maximum_length(nums, k) returns r and maximum_length(rev(nums), k) returns r2, then r = r2.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r r2 : Std.I64)
      (hr : maximum_length nums k = ok r) (hr2 : maximum_length (sliceRev nums) k = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r r2 : Std.I64)
        (hr : maximum_length nums k = ok r) (hr2 : maximum_length (sliceRev nums) k = ok r2), r.val = r2.val) := by
    sorry

  /-- Whenever the function returns r, there exist a sequence seq of length r and indices 0 <= i_0 < ... < i_{r-1} < len(nums) such that seq[t] = nums[i_t] for every 0 <= t < r, and the number of t with 0 <= t < r-1 and seq[t] != seq[t+1] is at most k.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      ∃ (seq : List Int) (idx : List Nat),
        IsSubseqIndices nums idx seq ∧ (seq.length : Int) = r.val ∧
          (numChanges seq : Int) ≤ k.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), ∃ (seq : List Int) (idx : List Nat),
          IsSubseqIndices nums idx seq ∧ (seq.length : Int) = r.val ∧
            (numChanges seq : Int) ≤ k.val) := by
    sorry

  /-- Whenever the function returns r, for every m >= 1, every sequence seq of length m, and every list of indices 0 <= i_0 < ... < i_{m-1} < len(nums) such that seq[t] = nums[i_t] for every 0 <= t < m, if the number of t with 0 <= t < m-1 and seq[t] != seq[t+1] is at most k, then m <= r.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      ∀ (seq : List Int) (idx : List Nat), 1 ≤ seq.length →
        IsSubseqIndices nums idx seq → (numChanges seq : Int) ≤ k.val →
          (seq.length : Int) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), ∀ (seq : List Int) (idx : List Nat), 1 ≤ seq.length →
          IsSubseqIndices nums idx seq → (numChanges seq : Int) ≤ k.val →
            (seq.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns r, let freq(v) be the number of indices i with 0 <= i < len(nums) and nums[i] = v, and let maxfreq be the maximum of freq(v) over all integers v. Then r <= (k+1) * maxfreq, where k+1 is computed as a mathematical integer.
    Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 5000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; k is an i64 with 0 <= k <= min(50, len(nums)). -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
      (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
      (r : Std.I64) (hr : maximum_length nums k = ok r) :
      r.val ≤ (k.val + 1) * (maxFreq nums : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 5000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 10 ^ 9)
        (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ min 50 (nums.val.length : Int))
        (r : Std.I64) (hr : maximum_length nums k = ok r), r.val ≤ (k.val + 1) * (maxFreq nums : Int)) := by
    sorry

  end AegisSpec.MaximumLength
