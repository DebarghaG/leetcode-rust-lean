import Aegis.LongestArithSeqLength.Code.Funs

/-!
# Specifications of `Aegis.LongestArithSeqLength.longest_arith_seq_length`

LeetCode problem `longest-arithmetic-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestArithSeqLength

  def values (nums : Slice Std.I64) : List ℤ := nums.val.map fun x => x.val

  def AllInRange (a : List ℤ) (lo hi : ℤ) : Prop := ∀ x ∈ a, lo ≤ x ∧ x ≤ hi

  def IsArithSubseq (a : List ℤ) (k : ℕ) : Prop :=
    ∃ idx : Fin k → Fin a.length,
      (∀ i j : Fin k, i < j → idx i < idx j) ∧
        ∃ d : ℤ, ∀ (j : ℕ) (hj : j + 1 < k),
          a.get (idx ⟨j + 1, by omega⟩) - a.get (idx ⟨j, by omega⟩) = d

  def IsArithLen (a : List ℤ) (r : ℤ) : Prop := ∃ k : ℕ, r = (k : ℤ) ∧ IsArithSubseq a k

  def ArithLenSet (a : List ℤ) : Set ℤ :=
    { r | ∃ k : ℕ, r = (k : ℤ) ∧ 2 ≤ k ∧ k ≤ a.length ∧ IsArithSubseq a k }

  def HasConstDiff (a : List ℤ) : Prop :=
    ∃ d : ℤ, ∀ (i : ℕ) (h : i + 1 < a.length), a.get ⟨i + 1, h⟩ - a.get ⟨i, by omega⟩ = d

  def countEq (a : List ℤ) (c : ℤ) : ℕ := a.countP fun x => decide (x = c)

  /-- The function returns a result r, and r is the largest integer k with 2 <= k <= len(nums) for which there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) for all j and an integer d such that nums[i_{j+1}] - nums[i_j] = d for every j with 0 <= j < k-1. In other words, r is the length of a longest arithmetic subsequence of nums: a subsequence is obtained by deleting zero or more elements without changing the order, and arithmetic means all consecutive differences of the selected values are equal.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∃ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r ∧
        IsGreatest (ArithLenSet (values nums)) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∃ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r ∧
          IsGreatest (ArithLenSet (values nums)) r.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular it does not panic, does not access nums outside the range 0 <= i < len(nums), and does not overflow the signed 64-bit integer range.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∃ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∃ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 2 <= r <= len(nums).
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        2 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          2 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i_0 < i_1 < ... < i_{r-1} with 0 <= i_j < len(nums) and an integer d such that nums[i_{j+1}] - nums[i_j] = d for every j with 0 <= j < r-1. Thus the returned length r is attained by some arithmetic subsequence of nums.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        IsArithLen (values nums) r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          IsArithLen (values nums) r.val) := by
    sorry

  /-- Whenever the function returns a result r, every arithmetic subsequence of nums has length at most r. Explicitly, for every integer k with 2 <= k <= len(nums) and every sequence of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) for all j, if there is an integer d such that nums[i_{j+1}] - nums[i_j] = d for every j with 0 <= j < k-1, then k <= r.
    Preconditions: len(nums) >= 2 and len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        ∀ k : ℕ, 2 ≤ k → k ≤ nums.val.length → IsArithSubseq (values nums) k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          ∀ k : ℕ, 2 ≤ k → k ≤ nums.val.length → IsArithSubseq (values nums) k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 2.
    Preconditions: len(nums) = 2, 0 <= nums[0] <= 500, and 0 <= nums[1] <= 500. -/
  theorem spec_6 (nums : Slice Std.I64) (hlen : nums.val.length = 2)
      (h0 : 0 ≤ (nums.val.get ⟨0, by omega⟩).val ∧ (nums.val.get ⟨0, by omega⟩).val ≤ 500)
      (h1 : 0 ≤ (nums.val.get ⟨1, by omega⟩).val ∧ (nums.val.get ⟨1, by omega⟩).val ≤ 500) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        r.val = 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 2)
        (h0 : 0 ≤ (nums.val.get ⟨0, by omega⟩).val ∧ (nums.val.get ⟨0, by omega⟩).val ≤ 500)
        (h1 : 0 ≤ (nums.val.get ⟨1, by omega⟩).val ∧ (nums.val.get ⟨1, by omega⟩).val ≤ 500), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          r.val = 2) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums).
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and there is an integer c such that 0 <= c <= 500 and nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (c : ℤ) (hc_lo : 0 ≤ c) (hc_hi : c ≤ 500)
      (hall : ∀ x ∈ values nums, x = c) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (c : ℤ) (hc_lo : 0 ≤ c) (hc_hi : c ≤ 500)
        (hall : ∀ x ∈ values nums, x = c), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and r = len(nums), there exists an integer d such that nums[i+1] - nums[i] = d for every i with 0 <= i < len(nums)-1.
    Preconditions: len(nums) >= 2, len(nums) <= 1000, and 0 <= nums[i] <= 500 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        r.val = (nums.val.length : ℤ) → HasConstDiff (values nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          r.val = (nums.val.length : ℤ) → HasConstDiff (values nums)) := by
    sorry

  /-- Whenever the function returns r for nums and r2 for nums2, r2 = r.
    Preconditions: nums and nums2 are slices with 2 <= len(nums) <= 1000, len(nums2) = len(nums), 0 <= nums[i] <= 500 and 0 <= nums2[i] <= 500 for every i, and nums2[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums nums2 : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hlen2 : nums2.val.length = nums.val.length)
      (hrange : AllInRange (values nums) 0 500)
      (hrange2 : AllInRange (values nums2) 0 500)

      (hrev : values nums2 = (values nums).reverse) :
      ∀ r r2 : Std.I64,
        Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        Aegis.LongestArithSeqLength.longest_arith_seq_length nums2 = ok r2 → r2 = r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hlen2 : nums2.val.length = nums.val.length)
        (hrange : AllInRange (values nums) 0 500)
        (hrange2 : AllInRange (values nums2) 0 500)

        (hrev : values nums2 = (values nums).reverse), ∀ r r2 : Std.I64,
          Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          Aegis.LongestArithSeqLength.longest_arith_seq_length nums2 = ok r2 → r2 = r) := by
    sorry

  /-- Whenever the function returns r for nums and r2 for nums2, either r2 = r or r2 = r + 1.
    Preconditions: nums and nums2 are slices with 2 <= len(nums) <= 999, len(nums2) = len(nums)+1, 0 <= nums[i] <= 500 and 0 <= nums2[i] <= 500 for every valid i, nums2[i] = nums[i] for every i with 0 <= i < len(nums), and nums2[len(nums)] is some integer x. -/
  theorem spec_10 (nums nums2 : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 999)
      (hlen2 : nums2.val.length = nums.val.length + 1)
      (hrange : AllInRange (values nums) 0 500)
      (hrange2 : AllInRange (values nums2) 0 500)
      (x : ℤ)
      (happend : values nums2 = values nums ++ [x]) :
      ∀ r r2 : Std.I64,
        Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        Aegis.LongestArithSeqLength.longest_arith_seq_length nums2 = ok r2 →
        r2.val = r.val ∨ r2.val = r.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 999)
        (hlen2 : nums2.val.length = nums.val.length + 1)
        (hrange : AllInRange (values nums) 0 500)
        (hrange2 : AllInRange (values nums2) 0 500)
        (x : ℤ)
        (happend : values nums2 = values nums ++ [x]), ∀ r r2 : Std.I64,
          Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          Aegis.LongestArithSeqLength.longest_arith_seq_length nums2 = ok r2 →
          r2.val = r.val ∨ r2.val = r.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= m.
    Preconditions: len(nums) >= 2, len(nums) <= 1000, 0 <= nums[i] <= 500 for every i, and there are an integer c and an integer m with m >= 2 such that exactly m indices i satisfy 0 <= i < len(nums) and nums[i] = c. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : AllInRange (values nums) 0 500)
      (c : ℤ) (m : ℕ) (hm : 2 ≤ m) (hcount : countEq (values nums) c = m) :
      ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
        (m : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : AllInRange (values nums) 0 500)
        (c : ℤ) (m : ℕ) (hm : 2 ≤ m) (hcount : countEq (values nums) c = m), ∀ r : Std.I64, Aegis.LongestArithSeqLength.longest_arith_seq_length nums = ok r →
          (m : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.LongestArithSeqLength
