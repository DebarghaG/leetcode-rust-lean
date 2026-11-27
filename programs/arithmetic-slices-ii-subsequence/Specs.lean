import Aegis.NumberOfArithmeticSlices.Code.Funs

/-!
# Specifications of `Aegis.NumberOfArithmeticSlices.number_of_arithmetic_slices`

LeetCode problem `arithmetic-slices-ii-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.NumberOfArithmeticSlices (number_of_arithmetic_slices)

  noncomputable section

  namespace AegisSpec.NumberOfArithmeticSlices

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def indexValues (v : List ℤ) (s : Finset ℕ) : List ℤ :=
    ((List.range v.length).filter (fun i => decide (i ∈ s))).map (fun i => v.getD i 0)

  def IsArith (l : List ℤ) : Prop :=
    ∃ d : ℤ, ∀ j : ℕ, j + 1 < l.length → l.getD (j + 1) 0 - l.getD j 0 = d

  def arithIndexSets (v : List ℤ) : Finset (Finset ℕ) :=
    letI := Classical.propDecidable
    ((Finset.range v.length).powerset).filter
      (fun s => 3 ≤ s.card ∧ IsArith (indexValues v s))

  def numArithSlices (v : List ℤ) : ℕ := (arithIndexSets v).card

  def numArithTriples (v : List ℤ) : ℕ :=
    (((Finset.range v.length).product (Finset.range v.length)).product
        (Finset.range v.length)).filter
      (fun p : (ℕ × ℕ) × ℕ =>
        p.1.1 < p.1.2 ∧ p.1.2 < p.2 ∧
          v.getD p.1.2 0 - v.getD p.1.1 0 = v.getD p.2 0 - v.getD p.1.2 0) |>.card

  def sumChoose (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 3 n, n.choose k

  def tripleInd (v : List ℤ) (i j k : ℕ) : ℕ :=
    if v.getD j 0 - v.getD i 0 = v.getD k 0 - v.getD j 0 then 1 else 0

  def quadInd (v : List ℤ) : ℕ :=
    if v.getD 1 0 - v.getD 0 0 = v.getD 2 0 - v.getD 1 0 ∧
        v.getD 2 0 - v.getD 1 0 = v.getD 3 0 - v.getD 2 0 then 1 else 0

  def InI64Range32 (nums : Slice Std.I64) : Prop :=
    ∀ x ∈ nums.val, -(2 : ℤ) ^ 31 ≤ x.val ∧ x.val ≤ (2 : ℤ) ^ 31 - 1

  def IsShift (c : ℤ) (nums nums' : Slice Std.I64) : Prop :=
    nums'.val.length = nums.val.length ∧
      ∀ i : ℕ, i < nums.val.length → (vals nums').getD i 0 = (vals nums).getD i 0 + c

  def IsConstant (c : ℤ) (nums : Slice Std.I64) : Prop := ∀ x ∈ nums.val, x.val = c

  /-- Let A(nums) be the number of index sequences (i_0, i_1, ..., i_{k-1}) such that k >= 3, 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums), and there exists an integer d with nums[i_{j+1}] - nums[i_j] = d for every j with 0 <= j < k-1. The function returns a result r and r = A(nums).
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. The count A(nums) defined in the statement satisfies A(nums) <= 2^31 - 1 (the promised 32-bit answer). -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1) :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          r.val = (numArithSlices (vals nums) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            r.val = (numArithSlices (vals nums) : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail by panic, out-of-bounds indexing, or arithmetic overflow.
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. The number of arithmetic subsequences of nums (strictly increasing index sequences of length at least 3 whose consecutive value differences are all equal) is at most 2^31 - 1. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1) :
      ∃ r : Std.I64, number_of_arithmetic_slices nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1), ∃ r : Std.I64, number_of_arithmetic_slices nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r) :
      (0 : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r), (0 : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2^31 - 1.
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. The number of arithmetic subsequences of nums is at most 2^31 - 1. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r) :
      r.val ≤ (2 : ℤ) ^ 31 - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r), r.val ≤ (2 : ℤ) ^ 31 - 1) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 1 <= len(nums) <= 2. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 2)
      (hrange : InI64Range32 nums) :
      ∃ r : Std.I64, number_of_arithmetic_slices nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 2)
        (hrange : InI64Range32 nums), ∃ r : Std.I64, number_of_arithmetic_slices nums = ok r ∧ r.val = 0) := by
    sorry

  /-- Let d1 = nums[1] - nums[0] and d2 = nums[2] - nums[1]. The function returns a result r and (if d1 = d2 then r = 1, and if d1 != d2 then r = 0).
    Preconditions: len(nums) = 3. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : nums.val.length = 3)
      (hrange : InI64Range32 nums) :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          ((vals nums).getD 1 0 - (vals nums).getD 0 0
              = (vals nums).getD 2 0 - (vals nums).getD 1 0 → r.val = 1) ∧
          ((vals nums).getD 1 0 - (vals nums).getD 0 0
              ≠ (vals nums).getD 2 0 - (vals nums).getD 1 0 → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 3)
        (hrange : InI64Range32 nums), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            ((vals nums).getD 1 0 - (vals nums).getD 0 0
                = (vals nums).getD 2 0 - (vals nums).getD 1 0 → r.val = 1) ∧
            ((vals nums).getD 1 0 - (vals nums).getD 0 0
                ≠ (vals nums).getD 2 0 - (vals nums).getD 1 0 → r.val = 0)) := by
    sorry

  /-- The function returns a result r and r = S.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. There exists an integer c such that nums[i] = c for every i with 0 <= i < n, and -2^31 <= c <= 2^31 - 1. Let S = sum_{k=3}^n C(n,k), where C(n,k) is the binomial coefficient n choose k; assume S <= 2^31 - 1. -/
  theorem spec_7 (nums : Slice Std.I64) (c : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hconst : IsConstant c nums)
      (hc_lo : -(2 : ℤ) ^ 31 ≤ c) (hc_hi : c ≤ (2 : ℤ) ^ 31 - 1)
      (hS : sumChoose nums.val.length ≤ 2 ^ 31 - 1) :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          r.val = (sumChoose nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (c : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hconst : IsConstant c nums)
        (hc_lo : -(2 : ℤ) ^ 31 ≤ c) (hc_hi : c ≤ (2 : ℤ) ^ 31 - 1)
        (hS : sumChoose nums.val.length ≤ 2 ^ 31 - 1), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            r.val = (sumChoose nums.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = A(nums) = A(nums').
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. Let A(x) be the number of arithmetic subsequences of an integer array x, defined by strictly increasing index sequences of length at least 3 whose consecutive value differences are all equal. Assume A(nums) <= 2^31 - 1. Let c be any integer and nums' any integer array such that len(nums') = len(nums), nums'[i] = nums[i] + c for every i, and every nums'[i] is representable as an i64 integer. -/
  theorem spec_8 (nums nums' : Slice Std.I64) (c : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
      (hshift : IsShift c nums nums') :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          r.val = (numArithSlices (vals nums) : ℤ) ∧
          r.val = (numArithSlices (vals nums') : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
        (hshift : IsShift c nums nums'), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            r.val = (numArithSlices (vals nums) : ℤ) ∧
            r.val = (numArithSlices (vals nums') : ℤ)) := by
    sorry

  /-- The function returns a result r and r = A(nums_rev).
    Preconditions: nums satisfies 1 <= len(nums) <= 1000 and -2^31 <= nums[i] <= 2^31 - 1 for every 0 <= i < len(nums), and its number of arithmetic subsequences is at most 2^31 - 1. Let A(x) be the number of arithmetic subsequences of an integer array x, defined by strictly increasing index sequences of length at least 3 whose consecutive value differences are all equal. Let nums_rev be the array with len(nums_rev) = len(nums) and nums_rev[i] = nums[len(nums)-1-i] for every i. -/
  theorem spec_9 (nums nums_rev : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
      (hrev : vals nums_rev = (vals nums).reverse) :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          r.val = (numArithSlices (vals nums_rev) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums_rev : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
        (hrev : vals nums_rev = (vals nums).reverse), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            r.val = (numArithSlices (vals nums_rev) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r >= T(nums).
    Preconditions: 1 <= len(nums) <= 1000. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. The number A(nums) of arithmetic subsequences of nums is at most 2^31 - 1. Let T(nums) be the number of triples (i,j,k) with 0 <= i < j < k < len(nums) and nums[j] - nums[i] = nums[k] - nums[j]. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
      (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r) :
      (numArithTriples (vals nums) : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (hbound : numArithSlices (vals nums) ≤ 2 ^ 31 - 1)
        (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r), (numArithTriples (vals nums) : ℤ) ≤ r.val) := by
    sorry

  /-- Define t(i,j,k) = 1 if nums[j] - nums[i] = nums[k] - nums[j], and t(i,j,k) = 0 otherwise. Define q = 1 if nums[1] - nums[0] = nums[2] - nums[1] and nums[2] - nums[1] = nums[3] - nums[2], and q = 0 otherwise. The function returns a result r and r = t(0,1,2) + t(0,1,3) + t(0,2,3) + t(1,2,3) + q.
    Preconditions: len(nums) = 4. For every i with 0 <= i < len(nums), -2^31 <= nums[i] <= 2^31 - 1. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : nums.val.length = 4)
      (hrange : InI64Range32 nums) :
      ∃ r : Std.I64,
        number_of_arithmetic_slices nums = ok r ∧
          r.val = ((tripleInd (vals nums) 0 1 2 + tripleInd (vals nums) 0 1 3 +
              tripleInd (vals nums) 0 2 3 + tripleInd (vals nums) 1 2 3 +
              quadInd (vals nums) : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 4)
        (hrange : InI64Range32 nums), ∃ r : Std.I64,
          number_of_arithmetic_slices nums = ok r ∧
            r.val = ((tripleInd (vals nums) 0 1 2 + tripleInd (vals nums) 0 1 3 +
                tripleInd (vals nums) 0 2 3 + tripleInd (vals nums) 1 2 3 +
                quadInd (vals nums) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{k=3}^n C(n,k), where C(n,k) is the binomial coefficient n choose k.
    Preconditions: Let n = len(nums). 1 <= n <= 1000. For every i with 0 <= i < n, -2^31 <= nums[i] <= 2^31 - 1. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
      (hrange : InI64Range32 nums)
      (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r) :
      r.val ≤ (sumChoose nums.val.length : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 1000)
        (hrange : InI64Range32 nums)
        (r : Std.I64) (hr : number_of_arithmetic_slices nums = ok r), r.val ≤ (sumChoose nums.val.length : ℤ)) := by
    sorry

  end AegisSpec.NumberOfArithmeticSlices
