import Aegis.MinSumSquareDiff.Code.Funs

/-!
# Specifications of `Aegis.MinSumSquareDiff.min_sum_square_diff`

LeetCode problem `minimum-sum-of-squared-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSumSquareDiff

  open Aegis.MinSumSquareDiff

  def nth (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i 0#i64).val

  def absDiffs (nums1 nums2 : Slice Std.I64) : List Int :=
    List.zipWith (fun a b => |a.val - b.val|) nums1.val nums2.val

  def sqDiffs (nums1 nums2 : Slice Std.I64) : List Int :=
    List.zipWith (fun a b => (a.val - b.val) ^ 2) nums1.val nums2.val

  def sumAbsDiffs (nums1 nums2 : Slice Std.I64) : Int := (absDiffs nums1 nums2).sum

  def sumSqDiffs (nums1 nums2 : Slice Std.I64) : Int := (sqDiffs nums1 nums2).sum

  def feasibleCosts (d : List Int) (K : Int) : Set Int :=
    { s | ∃ x : List Int, x.length = d.length ∧
            (∀ i, i < d.length → 0 ≤ x.getD i 0 ∧ x.getD i 0 ≤ d.getD i 0) ∧
            (∑ i ∈ Finset.range d.length, x.getD i 0) ≤ K ∧
            s = ∑ i ∈ Finset.range d.length, (d.getD i 0 - x.getD i 0) ^ 2 }

  /-- Let D_i = |nums1[i] - nums2[i]| for 0 <= i < n. The function returns a result r such that r = min { sum_{i=0}^{n-1} (D_i - x_i)^2 : x is an integer sequence of length n, 0 <= x_i <= D_i for all i, and sum_{i=0}^{n-1} x_i <= k1 + k2 }.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_1
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        IsLeast (feasibleCosts (absDiffs nums1 nums2) (k1.val + k2.val)) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          IsLeast (feasibleCosts (absDiffs nums1 nums2) (k1.val + k2.val)) r.val) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, no arithmetic overflow, no out-of-bounds access).
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_2
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r) := by
    sorry

  /-- The returned value r satisfies r >= 0.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_3
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- If k1 + k2 >= sum_{i=0}^{n-1} |nums1[i] - nums2[i]|, then r = 0.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_4
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hK : k1.val + k2.val ≥ sumAbsDiffs nums1 nums2) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hK : k1.val + k2.val ≥ sumAbsDiffs nums1 nums2), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧ r.val = 0) := by
    sorry

  /-- If k1 = 0 and k2 = 0, then r = sum_{i=0}^{n-1} (nums1[i] - nums2[i])^2.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_5
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hk1 : k1.val = 0) (hk2 : k2.val = 0) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        r.val = sumSqDiffs nums1 nums2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hk1 : k1.val = 0) (hk2 : k2.val = 0), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          r.val = sumSqDiffs nums1 nums2) := by
    sorry

  /-- Let r = min_sum_square_diff(nums1, nums2, k1, k2) and r' = min_sum_square_diff(nums2, nums1, k2, k1). Then r = r'.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_6
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums2 nums1 k2 k1 = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums2 nums1 k2 k1 = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let r = min_sum_square_diff(nums1, nums2, k1, k2) and r' = min_sum_square_diff(nums1, nums2, k1', k2'). Then r = r'.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, 0 <= k1, k2 <= 10^9, and for any integers k1', k2' with 0 <= k1', k2' <= 10^9 and k1' + k2' = k1 + k2. -/
  theorem spec_7
      (nums1 nums2 : Slice Std.I64) (k1 k2 k1' k2' : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hk1'lo : 0 ≤ k1'.val) (hk1'hi : k1'.val ≤ 1000000000)
      (hk2'lo : 0 ≤ k2'.val) (hk2'hi : k2'.val ≤ 1000000000)
      (hsum : k1'.val + k2'.val = k1.val + k2.val) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums1 nums2 k1' k2' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 k1' k2' : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hk1'lo : 0 ≤ k1'.val) (hk1'hi : k1'.val ≤ 1000000000)
        (hk2'lo : 0 ≤ k2'.val) (hk2'hi : k2'.val ≤ 1000000000)
        (hsum : k1'.val + k2'.val = k1.val + k2.val), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums1 nums2 k1' k2' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let r = min_sum_square_diff(nums1, nums2, k1, k2) and r' = min_sum_square_diff(nums1, nums2, k1', k2'). Then r' <= r.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, 0 <= k1, k2 <= 10^9, and for any integers k1', k2' with 0 <= k1', k2' <= 10^9, k1' >= k1, and k2' >= k2. -/
  theorem spec_8
      (nums1 nums2 : Slice Std.I64) (k1 k2 k1' k2' : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hk1'lo : 0 ≤ k1'.val) (hk1'hi : k1'.val ≤ 1000000000)
      (hk2'lo : 0 ≤ k2'.val) (hk2'hi : k2'.val ≤ 1000000000)
      (hk1le : k1'.val ≥ k1.val) (hk2le : k2'.val ≥ k2.val) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums1 nums2 k1' k2' = ok r' ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 k1' k2' : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hk1'lo : 0 ≤ k1'.val) (hk1'hi : k1'.val ≤ 1000000000)
        (hk2'lo : 0 ≤ k2'.val) (hk2'hi : k2'.val ≤ 1000000000)
        (hk1le : k1'.val ≥ k1.val) (hk2le : k2'.val ≥ k2.val), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums1 nums2 k1' k2' = ok r' ∧ r'.val ≤ r.val) := by
    sorry

  /-- The returned value r satisfies r <= sum_{i=0}^{n-1} (nums1[i] - nums2[i])^2.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_9
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        r.val ≤ sumSqDiffs nums1 nums2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          r.val ≤ sumSqDiffs nums1 nums2) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} |nums1[i] - nums2[i]| and K = k1 + k2. The returned value r satisfies n * r >= (max(0, S - K))^2.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_10
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        (n : Int) * r.val ≥ (max 0 (sumAbsDiffs nums1 nums2 - (k1.val + k2.val))) ^ 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          (n : Int) * r.val ≥ (max 0 (sumAbsDiffs nums1 nums2 - (k1.val + k2.val))) ^ 2) := by
    sorry

  /-- The returned value r satisfies r = (max(0, |nums1[0] - nums2[0]| - (k1 + k2)))^2.
    Preconditions: len(nums1) = len(nums2) = n, n = 1, 0 <= nums1[0] <= 10^5, 0 <= nums2[0] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_11
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn : n = 1)
      (h1lo : 0 ≤ nth nums1 0) (h1hi : nth nums1 0 ≤ 100000)
      (h2lo : 0 ≤ nth nums2 0) (h2hi : nth nums2 0 ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        r.val = (max 0 (|nth nums1 0 - nth nums2 0| - (k1.val + k2.val))) ^ 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn : n = 1)
        (h1lo : 0 ≤ nth nums1 0) (h1hi : nth nums1 0 ≤ 100000)
        (h2lo : 0 ≤ nth nums2 0) (h2hi : nth nums2 0 ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          r.val = (max 0 (|nth nums1 0 - nth nums2 0| - (k1.val + k2.val))) ^ 2) := by
    sorry

  /-- Let nums1'[i] = nums1[π(i)] and nums2'[i] = nums2[π(i)] for 0 <= i < n. Let r = min_sum_square_diff(nums1, nums2, k1, k2) and r' = min_sum_square_diff(nums1', nums2', k1, k2). Then r = r'.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, 0 <= k1, k2 <= 10^9, and π is any permutation of {0, ..., n-1}. -/
  theorem spec_12
      (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (π : Equiv.Perm (Fin n))
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
      (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hperm1 : ∀ (i : Nat) (hi : i < n), nth nums1' i = nth nums1 (π ⟨i, hi⟩).val)
      (hperm2 : ∀ (i : Nat) (hi : i < n), nth nums2' i = nth nums2 (π ⟨i, hi⟩).val) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (π : Equiv.Perm (Fin n))
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
        (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hperm1 : ∀ (i : Nat) (hi : i < n), nth nums1' i = nth nums1 (π ⟨i, hi⟩).val)
        (hperm2 : ∀ (i : Nat) (hi : i < n), nth nums2' i = nth nums2 (π ⟨i, hi⟩).val), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- There exist integer sequences a and b of length n such that sum_{i=0}^{n-1} |a_i - nums1[i]| <= k1, sum_{i=0}^{n-1} |b_i - nums2[i]| <= k2, and sum_{i=0}^{n-1} (a_i - b_i)^2 = r, where r is the returned value.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_13
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        ∃ a b : List Int, a.length = n ∧ b.length = n ∧
          (∑ i ∈ Finset.range n, |a.getD i 0 - nth nums1 i|) ≤ k1.val ∧
          (∑ i ∈ Finset.range n, |b.getD i 0 - nth nums2 i|) ≤ k2.val ∧
          (∑ i ∈ Finset.range n, (a.getD i 0 - b.getD i 0) ^ 2) = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          ∃ a b : List Int, a.length = n ∧ b.length = n ∧
            (∑ i ∈ Finset.range n, |a.getD i 0 - nth nums1 i|) ≤ k1.val ∧
            (∑ i ∈ Finset.range n, |b.getD i 0 - nth nums2 i|) ≤ k2.val ∧
            (∑ i ∈ Finset.range n, (a.getD i 0 - b.getD i 0) ^ 2) = r.val) := by
    sorry

  /-- For every pair of integer sequences a and b of length n satisfying sum_{i=0}^{n-1} |a_i - nums1[i]| <= k1 and sum_{i=0}^{n-1} |b_i - nums2[i]| <= k2, we have sum_{i=0}^{n-1} (a_i - b_i)^2 >= r, where r is the returned value.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_14
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        ∀ a b : List Int, a.length = n → b.length = n →
          (∑ i ∈ Finset.range n, |a.getD i 0 - nth nums1 i|) ≤ k1.val →
          (∑ i ∈ Finset.range n, |b.getD i 0 - nth nums2 i|) ≤ k2.val →
          r.val ≤ ∑ i ∈ Finset.range n, (a.getD i 0 - b.getD i 0) ^ 2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          ∀ a b : List Int, a.length = n → b.length = n →
            (∑ i ∈ Finset.range n, |a.getD i 0 - nth nums1 i|) ≤ k1.val →
            (∑ i ∈ Finset.range n, |b.getD i 0 - nth nums2 i|) ≤ k2.val →
            r.val ≤ ∑ i ∈ Finset.range n, (a.getD i 0 - b.getD i 0) ^ 2) := by
    sorry

  /-- min_sum_square_diff(nums1', nums2', k1, k2) = min_sum_square_diff(nums1, nums2, k1, k2).
    Preconditions: len(nums1) = len(nums2) = len(nums1') = len(nums2') = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5, 0 <= nums2[i] <= 10^5, 0 <= nums1'[i] <= 10^5, 0 <= nums2'[i] <= 10^5, 0 <= k1, k2 <= 10^9, and |nums1'[i] - nums2'[i]| = |nums1[i] - nums2[i]| for all i. -/
  theorem spec_15
      (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
      (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hdiff : ∀ i, i < n → |nth nums1' i - nth nums2' i| = |nth nums1 i - nth nums2 i|) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
        (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hdiff : ∀ i, i < n → |nth nums1' i - nth nums2' i| = |nth nums1 i - nth nums2 i|), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let S = sum_{i=0}^{n-1} |nums1[i] - nums2[i]| and K = k1 + k2. The returned value r satisfies r = 0 if and only if K >= S.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 10^5, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^5 and 0 <= nums2[i] <= 10^5, and 0 <= k1, k2 <= 10^9. -/
  theorem spec_16
      (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000) :
      ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        (r.val = 0 ↔ k1.val + k2.val ≥ sumAbsDiffs nums1 nums2) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000), ∃ r, min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          (r.val = 0 ↔ k1.val + k2.val ≥ sumAbsDiffs nums1 nums2)) := by
    sorry

  /-- min_sum_square_diff(nums1, nums2, k1, k2) <= min_sum_square_diff(nums1', nums2', k1, k2).
    Preconditions: len(nums1) = len(nums2) = len(nums1') = len(nums2') = n, 1 <= n <= 10^5, all entries of the four arrays lie in [0, 10^5], 0 <= k1, k2 <= 10^9, and |nums1[i] - nums2[i]| <= |nums1'[i] - nums2'[i]| for every 0 <= i < n. -/
  theorem spec_17
      (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
      (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
      (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
      (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
      (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
      (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
      (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
      (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
      (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
      (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
      (hmono : ∀ i, i < n → |nth nums1 i - nth nums2 i| ≤ |nth nums1' i - nth nums2' i|) :
      ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
        min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (nums1 nums2 nums1' nums2' : Slice Std.I64) (k1 k2 : Std.I64) (n : Nat)
        (hlen1 : nums1.val.length = n) (hlen2 : nums2.val.length = n)
        (hlen1' : nums1'.val.length = n) (hlen2' : nums2'.val.length = n)
        (hn_pos : 1 ≤ n) (hn_max : n ≤ 100000)
        (h1lo : ∀ i, i < n → 0 ≤ nth nums1 i) (h1hi : ∀ i, i < n → nth nums1 i ≤ 100000)
        (h2lo : ∀ i, i < n → 0 ≤ nth nums2 i) (h2hi : ∀ i, i < n → nth nums2 i ≤ 100000)
        (h1'lo : ∀ i, i < n → 0 ≤ nth nums1' i) (h1'hi : ∀ i, i < n → nth nums1' i ≤ 100000)
        (h2'lo : ∀ i, i < n → 0 ≤ nth nums2' i) (h2'hi : ∀ i, i < n → nth nums2' i ≤ 100000)
        (hk1lo : 0 ≤ k1.val) (hk1hi : k1.val ≤ 1000000000)
        (hk2lo : 0 ≤ k2.val) (hk2hi : k2.val ≤ 1000000000)
        (hmono : ∀ i, i < n → |nth nums1 i - nth nums2 i| ≤ |nth nums1' i - nth nums2' i|), ∃ r r', min_sum_square_diff nums1 nums2 k1 k2 = ok r ∧
          min_sum_square_diff nums1' nums2' k1 k2 = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MinSumSquareDiff
