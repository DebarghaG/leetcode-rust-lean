import Aegis.SumSubseqWidths.Code.Funs

/-!
# Specifications of `Aegis.SumSubseqWidths.sum_subseq_widths`

LeetCode problem `sum-of-subsequence-widths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumSubseqWidths

def modulus : Int := 1000000007

def sliceValues (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def IsNondecreasing (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def setWidth (v : Nat → Int) (S : Finset Nat) : Int :=
  if h : S.Nonempty then S.sup' h v - S.inf' h v else 0

def subsetWidthSum (v : List Int) : Int :=
  ∑ S ∈ (Finset.range v.length).powerset, setWidth (fun i => v.getD i 0) S

def sortedClosedForm (b : List Int) : Int :=
  ∑ i ∈ Finset.range b.length,
    b.getD i 0 * ((2 : Int) ^ i - (2 : Int) ^ (b.length - 1 - i))

/-- Whenever sum_subseq_widths(nums) returns a result r, r = T(nums) mod M, i.e. r is the unique integer in [0, M-1] congruent to T(nums) modulo M.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for every i with 0 <= i < n. Let M = 1000000007. For a non-empty set S of indices with 0 <= i < n, define width(S) = max_{i in S} nums[i] - min_{i in S} nums[i]. Let T(nums) be the sum of width(S) over all non-empty subsets S of {0,...,n-1}. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000) :
    ∀ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
      r.val % modulus = subsetWidthSum (sliceValues nums) % modulus ∧
        0 ≤ r.val ∧ r.val < modulus := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000), ∀ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
      r.val % modulus = subsetWidthSum (sliceValues nums) % modulus ∧
        0 ≤ r.val ∧ r.val < modulus) := by
  sorry

/-- The call sum_subseq_widths(nums) returns a result r; it does not fail (no panic, out-of-bounds, overflow, or other failure).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000) :
    ∃ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000), ∃ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r) := by
  sorry

/-- Whenever sum_subseq_widths(nums1) returns r1 and sum_subseq_widths(nums2) returns r2, r1 = r2.
  Preconditions: Let nums1 and nums2 be slices of equal length n with 1 <= n <= 100000 and all entries in [1,100000]. Assume that for every integer v, the number of indices i with nums1[i]=v equals the number with nums2[i]=v (equivalently, nums2 is a permutation or rearrangement of nums1). -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (hn1 : 1 ≤ nums1.val.length) (hn2 : nums1.val.length ≤ 100000)
    (hlen : nums2.val.length = nums1.val.length)
    (h1lo : ∀ v ∈ sliceValues nums1, 1 ≤ v)
    (h1hi : ∀ v ∈ sliceValues nums1, v ≤ 100000)
    (h2lo : ∀ v ∈ sliceValues nums2, 1 ≤ v)
    (h2hi : ∀ v ∈ sliceValues nums2, v ≤ 100000)
    (hcount : ∀ v : Int, (sliceValues nums1).count v = (sliceValues nums2).count v) :
    ∀ r1 r2 : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums1 = ok r1 →
        Aegis.SumSubseqWidths.sum_subseq_widths nums2 = ok r2 → r1 = r2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hn1 : 1 ≤ nums1.val.length) (hn2 : nums1.val.length ≤ 100000)
    (hlen : nums2.val.length = nums1.val.length)
    (h1lo : ∀ v ∈ sliceValues nums1, 1 ≤ v)
    (h1hi : ∀ v ∈ sliceValues nums1, v ≤ 100000)
    (h2lo : ∀ v ∈ sliceValues nums2, 1 ≤ v)
    (h2hi : ∀ v ∈ sliceValues nums2, v ≤ 100000)
    (hcount : ∀ v : Int, (sliceValues nums1).count v = (sliceValues nums2).count v), ∀ r1 r2 : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums1 = ok r1 →
        Aegis.SumSubseqWidths.sum_subseq_widths nums2 = ok r2 → r1 = r2) := by
  sorry

/-- Whenever sum_subseq_widths(nums) returns r and sum_subseq_widths(nums') returns r', we have r = r'.
  Preconditions: Let n = len(nums), with 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for all i. Let k be an integer such that 1 <= nums[i] + k <= 100000 for every i. Define nums' by nums'[i] = nums[i] + k for 0 <= i < n. -/
theorem spec_4 (nums nums' : Slice Std.I64) (k : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hk : ∀ v ∈ sliceValues nums, 1 ≤ v + k ∧ v + k ≤ 100000)
    (hshift : sliceValues nums' = (sliceValues nums).map (fun v => v + k)) :
    ∀ r r' : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
        Aegis.SumSubseqWidths.sum_subseq_widths nums' = ok r' → r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hk : ∀ v ∈ sliceValues nums, 1 ≤ v + k ∧ v + k ≤ 100000)
    (hshift : sliceValues nums' = (sliceValues nums).map (fun v => v + k)), ∀ r r' : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
        Aegis.SumSubseqWidths.sum_subseq_widths nums' = ok r' → r = r') := by
  sorry

/-- Whenever sum_subseq_widths(nums) returns r and sum_subseq_widths(nums') returns r', we have r' = (c * r) mod M.
  Preconditions: Let n = len(nums), with 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for all i. Let c be a positive integer such that 1 <= c * nums[i] <= 100000 for every i. Define nums' by nums'[i] = c * nums[i] for 0 <= i < n. Let M = 1000000007. -/
theorem spec_5 (nums nums' : Slice Std.I64) (c : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hc : 0 < c)
    (hc_bounds : ∀ v ∈ sliceValues nums, 1 ≤ c * v ∧ c * v ≤ 100000)
    (hscale : sliceValues nums' = (sliceValues nums).map (fun v => c * v)) :
    ∀ r r' : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
        Aegis.SumSubseqWidths.sum_subseq_widths nums' = ok r' →
          r'.val % modulus = (c * r.val) % modulus := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hc : 0 < c)
    (hc_bounds : ∀ v ∈ sliceValues nums, 1 ≤ c * v ∧ c * v ≤ 100000)
    (hscale : sliceValues nums' = (sliceValues nums).map (fun v => c * v)), ∀ r r' : Std.I64,
      Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
        Aegis.SumSubseqWidths.sum_subseq_widths nums' = ok r' →
          r'.val % modulus = (c * r.val) % modulus) := by
  sorry

/-- Whenever sum_subseq_widths(nums) returns a result r, r is congruent modulo M to the sum from i = 0 to n-1 of b[i] * (2^i - 2^(n-1-i)).
  Preconditions: Let n = len(nums), with 1 <= n <= 100000 and 1 <= nums[i] <= 100000 for all i. Let b be any sequence of length n that is a nondecreasing rearrangement of nums, so b[0] <= b[1] <= ... <= b[n-1] and the multiset of b equals the multiset of nums. Let M = 1000000007. All powers 2^k below are mathematical integers. -/
theorem spec_6 (nums : Slice Std.I64) (b : List Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hb_sorted : IsNondecreasing b)
    (hb_perm : b.Perm (sliceValues nums)) :
    ∀ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
      r.val % modulus = sortedClosedForm b % modulus := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (b : List Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlo : ∀ v ∈ sliceValues nums, 1 ≤ v)
    (hhi : ∀ v ∈ sliceValues nums, v ≤ 100000)
    (hb_sorted : IsNondecreasing b)
    (hb_perm : b.Perm (sliceValues nums)), ∀ r : Std.I64, Aegis.SumSubseqWidths.sum_subseq_widths nums = ok r →
      r.val % modulus = sortedClosedForm b % modulus) := by
  sorry

end AegisSpec.SumSubseqWidths
