import Aegis.SumOfGoodNumbers.Code.Funs

/-!
# Specifications of `Aegis.SumOfGoodNumbers.sum_of_good_numbers`

LeetCode problem `sum-of-good-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfGoodNumbers

def elem (nums : Slice Std.I64) (i : ℤ) : ℤ := (nums.val[i.toNat]!).val

def Good (nums : Slice Std.I64) (k : ℤ) (i : ℤ) : Prop :=
  0 ≤ i ∧ i < (nums.val.length : ℤ) ∧
    (0 ≤ i - k ∧ i - k < (nums.val.length : ℤ) → elem nums i > elem nums (i - k)) ∧
    (0 ≤ i + k ∧ i + k < (nums.val.length : ℤ) → elem nums i > elem nums (i + k))

instance instDecidableGood (nums : Slice Std.I64) (k i : ℤ) : Decidable (Good nums k i) := by
  unfold Good
  infer_instance

def goodIndices (nums : Slice Std.I64) (k : ℤ) : Finset ℕ :=
  (Finset.range nums.val.length).filter (fun i => Good nums k (i : ℤ))

def goodSum (nums : Slice Std.I64) (k : ℤ) : ℤ :=
  (goodIndices nums k).sum (fun i => elem nums (i : ℤ))

def goodCount (nums : Slice Std.I64) (k : ℤ) : ℤ := ((goodIndices nums k).card : ℤ)

def sumOver (nums : Slice Std.I64) (lo hi : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico lo hi, elem nums (i : ℤ)

/-- Call an index i good for (nums,k) when 0 <= i < n, (if 0 <= i-k < n then nums[i] > nums[i-k]), and (if 0 <= i+k < n then nums[i] > nums[i+k]). Whenever the function returns a result r, r equals the sum of nums[i] over all i with 0 <= i < n that are good for (nums,k). The sum over an empty set of indices is 0.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2) with k interpreted as an integer; and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → r.val = goodSum nums k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000), ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → r.val = goodSum nums k.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; equivalently, it never fails on such inputs.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000) :
    ∃ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000), ∃ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000) :
    ∀ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000), ∀ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (sum_{i=0}^{n-1} nums[i]) - 1.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000) :
    ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val ≤ sumOver nums 0 nums.val.length - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000), ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val ≤ sumOver nums 0 nums.val.length - 1) := by
  sorry

/-- If there is an integer c with 1 <= c <= 1000 such that nums[i] = c for every i with 0 <= i < n, then whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hconst : ∀ i : ℕ, i < nums.val.length → elem nums (i : ℤ) = c) :
    ∀ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c) (hc2 : c ≤ 1000)
    (hconst : ∀ i : ℕ, i < nums.val.length → elem nums (i : ℤ) = c), ∀ r : Std.I64, Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → r.val = 0) := by
  sorry

/-- Assume n = 2 (hence k = 1). Whenever the function returns a result r: if nums[0] > nums[1] then r = nums[0]; if nums[0] < nums[1] then r = nums[1]; if nums[0] = nums[1] then r = 0.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hn : nums.val.length = 2) :
    ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        (elem nums 0 > elem nums 1 → r.val = elem nums 0) ∧
        (elem nums 0 < elem nums 1 → r.val = elem nums 1) ∧
        (elem nums 0 = elem nums 1 → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hn : nums.val.length = 2), ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        (elem nums 0 > elem nums 1 → r.val = elem nums 0) ∧
        (elem nums 0 < elem nums 1 → r.val = elem nums 1) ∧
        (elem nums 0 = elem nums 1 → r.val = 0)) := by
  sorry

/-- If nums[i] > nums[i+1] for every i with 0 <= i < n-1, then whenever the function returns a result r, r = sum_{i=0}^{k-1} nums[i].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hmono : ∀ i : ℕ, i + 1 < nums.val.length →
      elem nums (i : ℤ) > elem nums ((i : ℤ) + 1)) :
    ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val = sumOver nums 0 k.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hmono : ∀ i : ℕ, i + 1 < nums.val.length →
      elem nums (i : ℤ) > elem nums ((i : ℤ) + 1)), ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val = sumOver nums 0 k.val.toNat) := by
  sorry

/-- If nums[i] < nums[i+1] for every i with 0 <= i < n-1, then whenever the function returns a result r, r = sum_{i=n-k}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hmono : ∀ i : ℕ, i + 1 < nums.val.length →
      elem nums (i : ℤ) < elem nums ((i : ℤ) + 1)) :
    ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val = sumOver nums (nums.val.length - k.val.toNat) nums.val.length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hmono : ∀ i : ℕ, i + 1 < nums.val.length →
      elem nums (i : ℤ) < elem nums ((i : ℤ) + 1)), ∀ r : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        r.val = sumOver nums (nums.val.length - k.val.toNat) nums.val.length) := by
  sorry

/-- Let rev be the array of length n with rev[i] = nums[n-1-i] for 0 <= i < n. Whenever the function returns r for (nums,k) and r' for (rev,k), r = r'.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_9 (nums rev : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hrev : rev.val = nums.val.reverse) :
    ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers rev k = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums rev : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (hrev : rev.val = nums.val.reverse), ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers rev k = ok r' → r.val = r'.val) := by
  sorry

/-- Call an index i good for (nums,k) when 0 <= i < n, (if 0 <= i-k < n then nums[i] > nums[i-k]), and (if 0 <= i+k < n then nums[i] > nums[i+k]). For every integer i with 0 <= i < n, if i is good for (nums,k), then whenever the function returns a result r, r >= nums[i].
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000) :
    ∀ i : ℤ, 0 ≤ i → i < (nums.val.length : ℤ) → Good nums k.val i →
      ∀ r : Std.I64,
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → elem nums i ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000), ∀ i : ℤ, 0 ≤ i → i < (nums.val.length : ℤ) → Good nums k.val i →
      ∀ r : Std.I64,
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r → elem nums i ≤ r.val) := by
  sorry

/-- Call an index i good for (nums,k) when 0 <= i < n, (if 0 <= i-k < n then nums[i] > nums[i-k]), and (if 0 <= i+k < n then nums[i] > nums[i+k]). Let nums' be the array with nums'[i] = nums[i]+c, and let g be the number of indices i with 0 <= i < n that are good for (nums,k). Whenever the function returns r for (nums,k) and r' for (nums',k), r' = r + c*g.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. Let c be an integer such that 1 <= nums[i]+c <= 1000 for every i with 0 <= i < n. -/
theorem spec_11 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ)
    (hc : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) + c ∧ elem nums (i : ℤ) + c ≤ 1000)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i : ℕ, i < nums.val.length → elem nums' (i : ℤ) = elem nums (i : ℤ) + c) :
    ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums' k = ok r' →
          r'.val = r.val + c * goodCount nums k.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ)
    (hc : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) + c ∧ elem nums (i : ℤ) + c ≤ 1000)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i : ℕ, i < nums.val.length → elem nums' (i : ℤ) = elem nums (i : ℤ) + c), ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums' k = ok r' →
          r'.val = r.val + c * goodCount nums k.val) := by
  sorry

/-- Let nums' be the array with nums'[i] = c*nums[i] for 0 <= i < n. Whenever the function returns r for (nums,k) and r' for (nums',k), r' = c*r.
  Preconditions: Let n = len(nums). Assume 2 <= n <= 100; 1 <= k <= floor(n/2); and 1 <= nums[i] <= 1000 for every i with 0 <= i < n. Let c be an integer with c >= 1 such that 1 <= c*nums[i] <= 1000 for every i with 0 <= i < n. -/
theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c)
    (hc : ∀ i : ℕ, i < nums.val.length →
      1 ≤ c * elem nums (i : ℤ) ∧ c * elem nums (i : ℤ) ≤ 1000)
    (hlen : nums'.val.length = nums.val.length)
    (hscale : ∀ i : ℕ, i < nums.val.length → elem nums' (i : ℤ) = c * elem nums (i : ℤ)) :
    ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums' k = ok r' → r'.val = c * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn2 : 2 ≤ nums.val.length) (hn100 : nums.val.length ≤ 100)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : ℤ) / 2)
    (hnums : ∀ i : ℕ, i < nums.val.length →
      1 ≤ elem nums (i : ℤ) ∧ elem nums (i : ℤ) ≤ 1000)
    (c : ℤ) (hc1 : 1 ≤ c)
    (hc : ∀ i : ℕ, i < nums.val.length →
      1 ≤ c * elem nums (i : ℤ) ∧ c * elem nums (i : ℤ) ≤ 1000)
    (hlen : nums'.val.length = nums.val.length)
    (hscale : ∀ i : ℕ, i < nums.val.length → elem nums' (i : ℤ) = c * elem nums (i : ℤ)), ∀ r r' : Std.I64,
      Aegis.SumOfGoodNumbers.sum_of_good_numbers nums k = ok r →
        Aegis.SumOfGoodNumbers.sum_of_good_numbers nums' k = ok r' → r'.val = c * r.val) := by
  sorry

  end AegisSpec.SumOfGoodNumbers
